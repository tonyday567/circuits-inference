-- | Hamiltonian Monte Carlo on a standard Gaussian target.
--
-- HMC with leapfrog integration and Metropolis-Hastings accept/reject.
-- The oracle verifies empirical moments match N(0,1) within tolerance.
module Circuit.Inference.HMC
  ( -- * Sampling
    hmcSamples,
    momentTest,
  )
where

import System.Random (randomRIO)

-- | N(0,1) log-density.
logPTarget :: Double -> Double
logPTarget x = -((x * x) / 2)

-- | Gradient of log-density.
gradLogP :: Double -> Double
gradLogP x = -x

-- | One leapfrog step.
leapfrogStep :: (Double, Double) -> Double -> (Double, Double)
leapfrogStep (x, p) eps =
  let pHalf = p + (eps / 2) * gradLogP x
      xNext = x + eps * pHalf
      pNext = pHalf + (eps / 2) * gradLogP xNext
   in (xNext, pNext)

-- | L leapfrog steps.
leapfrog :: Double -> Int -> (Double, Double) -> (Double, Double)
leapfrog eps n state = iterate (`leapfrogStep` eps) state !! n

-- | One HMC step: sample momentum, run L leapfrog steps, MH accept/reject.
hmcStep :: Double -> Int -> Double -> IO (Double, Bool)
hmcStep eps nLeap x = do
  u1 <- randomRIO (0, 1 :: Double)
  u2 <- randomRIO (0, 1 :: Double)
  let p = sqrt (-(2 * log (max u1 1e-300))) * cos (2 * pi * u2)
      eCurrent = -logPTarget x + (p * p) / 2
      (xProp, pProp) = leapfrog eps nLeap (x, p)
      eProposed = -logPTarget xProp + (pProp * pProp) / 2
      logAlpha = eCurrent - eProposed
  u <- randomRIO (0, 1 :: Double)
  let accept = log u < logAlpha
      xNext = if accept then xProp else x
  pure (xNext, accept)

-- | Generate N HMC samples.
hmcSamples :: Int -> Double -> Int -> IO [Double]
hmcSamples nSamples eps nLeap =
  let go 0 _ xs = pure (reverse xs)
      go k x xs = do
        (xNext, _) <- hmcStep eps nLeap x
        go (k - 1) xNext (xNext : xs)
   in go nSamples 0.0 []

-- | Check empirical moments match N(0,1).
momentTest :: [Double] -> (Bool, Double, Double)
momentTest xs =
  let n = fromIntegral (length xs)
      mean = sum xs / n
      var = sum (map (\x -> (x - mean) ** 2) xs) / n
      se = sqrt (var / n)
      meanOk = abs mean <= 3 * se
      varOk = abs (var - 1) <= 0.2
   in (meanOk && varOk, mean, var)
