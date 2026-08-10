-- | Axioma oracle for the circuits-inference second slice.
--
-- Checks four claims:
--
-- 1. 'traceEK' on the geometric body terminates (no pure-Double divergence).
-- 2. The empirical mean of geometric samples agrees with the analytic mean.
-- 3. 'parFGK' and 'parGFK' agree in distribution but differ operationally on
--    an ordered effect (premonoidal witness).
-- 4. SMC particle filter matches exact enumeration on a 2-state HMM
--    (tolerance oracle).
module Main where

import Circuit.Inference.HMC (hmcSamples, momentTest)
import Circuit.Inference.LinearSolve (exactStationary, powerIteration)
import Circuit.Inference.Prob (Prob (..), parFGK, parGFK)
import Circuit.Inference.SMC (exactFiltering, l1Distance, particleFilter, trace5)
import Circuit.Inference.Sampler (geometric, sample)
import Control.Arrow (Kleisli (..))
import Data.IORef (IORef, modifyIORef', newIORef, readIORef, writeIORef)
import Data.List (sort)
import Data.Map.Strict qualified as Map
import System.Exit (exitFailure)
import System.Random (randomRIO)

-- | Number of samples for statistical checks.
nSamples :: Int
nSamples = 10000

-- | Relative tolerance for empirical mean vs analytic mean.
meanTol :: Double
meanTol = 0.1

report :: String -> Bool -> IO ()
report label ok = putStrLn $ label ++ ": " ++ if ok then "PASS" else "FAIL"

-- | Sample a value and accumulate it.
sampleSum :: Int -> IO Int -> IO Double
sampleSum 0 _ = pure 0
sampleSum n action = do
  x <- action
  rest <- sampleSum (n - 1) action
  pure (fromIntegral x + rest)

-- | Check that geometric terminates and its empirical mean is near (1-p)/p.
checkGeometric :: IO Bool
checkGeometric = do
  let p = 0.3
      expected = (1 - p) / p
  total <- sampleSum nSamples (sample (geometric p))
  let empirical = total / fromIntegral nSamples
      ok = abs (empirical - expected) <= meanTol * expected
  report ("geometric mean (expected " ++ show expected ++ ", got " ++ show empirical ++ ")") ok
  pure ok

-- | Two-point Bernoulli sampler with a side effect that records order.
--
-- The result type is @(Bool, Bool)@ so that the sampler can be nested under
-- 'parFGK' / 'parGFK'.  The sampler appends @(label, counter)@ to the shared
-- log, then increments the counter.
orderedBernoulli :: String -> IORef [(String, Int)] -> Prob (Kleisli IO) (Bool, Bool) () Bool
orderedBernoulli name logRef = Prob $ \(Kleisli k) -> Kleisli $ \(x, ()) -> do
  b <- randomRIO (0, 1) :: IO Double
  let v = b < 0.5
  n <- length <$> readIORef logRef
  modifyIORef' logRef ((name, n) :)
  k (x, v)

-- | Collect output frequencies from an effectful sampler.
frequencies :: (Ord a) => Int -> IO a -> IO (Map.Map a Int)
frequencies n action = go n Map.empty
  where
    go 0 m = pure m
    go i m = do
      v <- action
      go (i - 1) (Map.insertWith (+) v 1 m)

-- | Check that parFGK and parGFK give the same output distribution but
-- different operational logs on ordered effects.
checkPremonoidal :: IO Bool
checkPremonoidal = do
  logRef <- newIORef []
  let samplerA = orderedBernoulli "A" logRef
      samplerB = orderedBernoulli "B" logRef
      -- Final continuation returns the paired output.
      finalK = Kleisli (\(_, (a, b)) -> pure (a, b))
      -- Both samplers have input (); parFGK/parGFK produce input ((), ()).
      runPair nesting = do
        writeIORef logRef []
        let p = nesting samplerA samplerB
        result <- runKleisli (runProb p finalK) ((), ((), ()))
        entries <- readIORef logRef
        pure (result, entries)

  freqFG <- frequencies nSamples (fst <$> runPair parFGK)
  freqGF <- frequencies nSamples (fst <$> runPair parGFK)
  let tvDistance =
        sum
          [ abs (fromIntegral (Map.findWithDefault 0 k freqFG - Map.findWithDefault 0 k freqGF) :: Double)
          | k <- [(False, False), (False, True), (True, False), (True, True)]
          ]
          / fromIntegral nSamples
      distOk = tvDistance <= 0.05

  -- Operational order: parFGK samples A then B; parGFK samples B then A.
  (_, logFG) <- runPair parFGK
  (_, logGF) <- runPair parGFK
  let orderOf logEntries = map snd (sort (map (\(name, n) -> (n, name)) logEntries))
      orderFG = orderOf logFG
      orderGF = orderOf logGF
      opOk = orderFG == ["A", "B"] && orderGF == ["B", "A"]

  report "parFGK/parGFK distribution equality" distOk
  report "parFGK/parGFK operational order differs" opOk
  pure (distOk && opOk)

-- | Check SMC particle filter converges to exact filtering on trace5.
checkSMC :: IO Bool
checkSMC = do
  let exact = exactFiltering trace5
      smc = particleFilter trace5 2000
      dist = l1Distance exact smc
      tol = 0.1
      ok = dist <= tol
  report ("SMC filtering within L1 tolerance " ++ show tol) ok
  pure ok

-- | Check HMC preserves N(0,1) — empirical moments match within tolerance.
checkHMC :: IO Bool
checkHMC = do
  samples <- hmcSamples 5000 0.1 10
  let (ok, meanVal, varVal) = momentTest samples
  report ("HMC moments (mean=" ++ show meanVal ++ ", var=" ++ show varVal ++ ")") ok
  pure ok

-- | Check stationary distribution from linear solve matches power iteration.
checkLinearSolve :: IO Bool
checkLinearSolve = do
  let exact = exactStationary
      approx = powerIteration
      maxDiff = maximum (zipWith (\x y -> abs (x - y)) exact approx)
      ok = maxDiff < 1e-10
  report ("Linear solve vs power iteration (max diff=" ++ show maxDiff ++ ")") ok
  pure ok

main :: IO ()
main = do
  okGeo <- checkGeometric
  okPre <- checkPremonoidal
  okSMC <- checkSMC
  okHMC <- checkHMC
  okLin <- checkLinearSolve
  if okGeo && okPre && okSMC && okHMC && okLin
    then putStrLn "circuits-inference axioma: all checks passed"
    else do
      putStrLn "circuits-inference axioma: one or more checks failed"
      exitFailure
