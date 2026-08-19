-- | Axioma oracle for the circuits-inference second slice.
--
-- Checks nine claims:
--
-- 1. 'traceEK' on the geometric body terminates (no pure-Double divergence).
-- 2. The empirical mean of geometric samples agrees with the analytic mean.
-- 3. 'parFGK' and 'parGFK' agree in distribution but differ operationally on
--    an ordered effect (premonoidal witness).
-- 4. SMC particle filter matches exact enumeration on a 2-state HMM
--    (tolerance oracle).
-- 5. HMC preserves N(0,1) moments, and the leapfrog integrator is reversible
--    and volume-preserving on the Gaussian target (exact oracles).
-- 6. The leapfrog and Yoshida-4 'System'/'Process' wrappers agree with the
--    pure step functions.
-- 7. The Yoshida-4 integrator is reversible and volume-preserving on the
--    Gaussian target (exact oracles).
-- 8. Leapfrog energy error on the harmonic oscillator scales like @eps^2@.
-- 9. Yoshida-4 energy error on the harmonic oscillator scales like @eps^4@.
module Main where

import Circuit (runSystem)
import Circuit.Inference.HMC
  ( hmcSamples,
    leapfrogJacobianDet,
    leapfrogOrderSlope,
    leapfrogProcess,
    leapfrogReversible,
    leapfrogStep,
    leapfrogSystem,
    momentTest,
    yoshida4JacobianDet,
    yoshida4OrderSlope,
    yoshida4Process,
    yoshida4Reversible,
    yoshida4Step,
    yoshida4System,
  )
import Circuit.Inference.LinearSolve (exactStationary, powerIteration)
import Circuit.Inference.Prob (Prob (..), parFGK, parGFK)
import Circuit.Inference.SMC (State (..), exactFiltering, l1Distance, obsProb, particleFilter, smcSystem, smcTotalWeight, trace5, transProb)
import Circuit.Inference.Sampler (geometric, sample)
import Circuit.Process (scan)
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

-- | Check SMC polynomial shape: weight is a position, not a direction.
checkSMCPoly :: IO Bool
checkSMCPoly = do
  let o = 1
      expected = sum [transProb StateA s' * obsProb o s' | s' <- [StateA, StateB]]
      actual = smcTotalWeight o StateA
      ok = abs (actual - expected) < 1e-9
  report ("SMC polynomial shape: total weight matches marginal likelihood " ++ show actual) ok
  pure ok

-- | Check HMC preserves N(0,1) — empirical moments match within tolerance.
checkHMC :: IO Bool
checkHMC = do
  samples <- hmcSamples 5000 0.1 10
  let (ok, meanVal, varVal) = momentTest samples
  report ("HMC moments (mean=" ++ show meanVal ++ ", var=" ++ show varVal ++ ")") ok
  pure ok

-- | Check the leapfrog 'System' and 'Process' agree with the pure step.
checkLeapfrogProcess :: IO Bool
checkLeapfrogProcess = do
  let eps = 0.1
      seed = (0.0, 1.0)
      proc = leapfrogProcess eps
      -- One input through the Process: output is the stepped state.
      procResult = scan proc [seed]
      -- One step through the underlying system.
      stepped = runSystem (leapfrogSystem eps) (seed, Right seed)
      expected = leapfrogStep seed eps
      ok = procResult == [expected] && fst stepped == expected
  report "leapfrog process/system agreement" ok
  pure ok

-- | Exact oracle: leapfrog integration is reversible up to machine epsilon.
checkLeapfrogReversible :: IO Bool
checkLeapfrogReversible = do
  let eps = 0.1
      n = 10
      state = (1.0, 0.5)
      ok = leapfrogReversible eps n state
  report ("leapfrog reversible (eps=" ++ show eps ++ ", n=" ++ show n ++ ")") ok
  pure ok

-- | Exact oracle: leapfrog integration preserves phase-space volume.
checkLeapfrogVolume :: IO Bool
checkLeapfrogVolume = do
  let eps = 0.1
      n = 10
      det = leapfrogJacobianDet eps n
      ok = abs (det - 1.0) <= 1e-12
  report ("leapfrog volume preservation (det=" ++ show det ++ ")") ok
  pure ok

-- | Check the Yoshida-4 'System' and 'Process' agree with the pure step.
checkYoshida4Process :: IO Bool
checkYoshida4Process = do
  let eps = 0.1
      seed = (0.0, 1.0)
      proc = yoshida4Process eps
      procResult = scan proc [seed]
      stepped = runSystem (yoshida4System eps) (seed, Right seed)
      expected = yoshida4Step seed eps
      ok = procResult == [expected] && fst stepped == expected
  report "Yoshida-4 process/system agreement" ok
  pure ok

-- | Exact oracle: Yoshida-4 integration is reversible up to machine epsilon.
checkYoshida4Reversible :: IO Bool
checkYoshida4Reversible = do
  let eps = 0.1
      n = 5
      state = (1.0, 0.5)
      ok = yoshida4Reversible eps n state
  report ("Yoshida-4 reversible (eps=" ++ show eps ++ ", n=" ++ show n ++ ")") ok
  pure ok

-- | Exact oracle: Yoshida-4 integration preserves phase-space volume.
checkYoshida4Volume :: IO Bool
checkYoshida4Volume = do
  let eps = 0.1
      n = 5
      det = yoshida4JacobianDet eps n
      ok = abs (det - 1.0) <= 1e-12
  report ("Yoshida-4 volume preservation (det=" ++ show det ++ ")") ok
  pure ok

-- | Order oracle: leapfrog energy error scales like @eps^2@ on the harmonic
-- oscillator.
checkLeapfrogOrder :: IO Bool
checkLeapfrogOrder = do
  let slope = leapfrogOrderSlope 1.0 (1.0, 0.0)
      ok = abs (slope - 2.0) <= 0.1
  report ("leapfrog order slope (slope=" ++ show slope ++ ")") ok
  pure ok

-- | Order oracle: Yoshida-4 energy error scales like @eps^4@ on the harmonic
-- oscillator.
checkYoshida4Order :: IO Bool
checkYoshida4Order = do
  let slope = yoshida4OrderSlope 1.0 (1.0, 0.0)
      ok = abs (slope - 4.0) <= 0.1
  report ("Yoshida-4 order slope (slope=" ++ show slope ++ ")") ok
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
  okSMCPoly <- checkSMCPoly
  okHMC <- checkHMC
  okMach <- checkLeapfrogProcess
  okRev <- checkLeapfrogReversible
  okVol <- checkLeapfrogVolume
  okY4Mach <- checkYoshida4Process
  okY4Rev <- checkYoshida4Reversible
  okY4Vol <- checkYoshida4Volume
  okOrd <- checkLeapfrogOrder
  okY4Ord <- checkYoshida4Order
  okLin <- checkLinearSolve
  if okGeo && okPre && okSMC && okSMCPoly && okHMC && okMach && okRev && okVol && okY4Mach && okY4Rev && okY4Vol && okOrd && okY4Ord && okLin
    then putStrLn "circuits-inference axioma: all checks passed"
    else do
      putStrLn "circuits-inference axioma: one or more checks failed"
      exitFailure
