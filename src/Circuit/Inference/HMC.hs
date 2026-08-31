-- | Hamiltonian Monte Carlo on a standard Gaussian target.
--
-- HMC with leapfrog integration and Metropolis-Hastings accept/reject.
-- The oracle verifies empirical moments match N(0,1) within tolerance.
--
-- This module also exposes the leapfrog integrator as a 'System' and 'Process'
-- over the circuits polynomial interface, together with exact oracles for
-- reversibility and volume preservation on the Gaussian target.
module Circuit.Inference.HMC
  ( -- * Sampling
    hmcSamples,
    momentTest,

    -- * Leapfrog dynamics
    leapfrogStep,
    leapfrog,
    negateMomentum,
    reverseLeapfrog,

    -- * Circuit integrations
    leapfrogSystem,
    leapfrogProcess,

    -- * Yoshida-4 dynamics
    yoshida4Step,
    yoshida4,
    yoshida4System,
    yoshida4Process,

    -- * Exact oracles
    leapfrogReversible,
    leapfrogJacobianDet,
    yoshida4Reversible,
    yoshida4JacobianDet,

    -- * Order oracles
    leapfrogOrderSlope,
    yoshida4OrderSlope,
  )
where

import Circuit (Mono, Moore, Process, moore)
import Circuit.Moore (mooreAsProcess)
import Data.Void (absurd)
import System.Random (randomRIO)

-- | N(0,1) log-density.
logPTarget :: Double -> Double
logPTarget x = -((x * x) / 2)

-- | Gradient of log-density.
gradLogP :: Double -> Double
gradLogP x = -x

-- | One leapfrog step on the Gaussian target.
leapfrogStep :: (Double, Double) -> Double -> (Double, Double)
leapfrogStep (x, p) eps =
  let pHalf = p + (eps / 2) * gradLogP x
      xNext = x + eps * pHalf
      pNext = pHalf + (eps / 2) * gradLogP xNext
   in (xNext, pNext)

-- | L leapfrog steps.
leapfrog :: Double -> Int -> (Double, Double) -> (Double, Double)
leapfrog eps n state = iterate (`leapfrogStep` eps) state !! n

-- | Negate the momentum component of a phase-space point.
negateMomentum :: (Double, Double) -> (Double, Double)
negateMomentum (x, p) = (x, -p)

-- | Run the leapfrog integrator backwards in time.
--
-- Time reversal for symplectic integrators is achieved by negating the momentum,
-- integrating forward, then negating the momentum again.
reverseLeapfrog :: Double -> Int -> (Double, Double) -> (Double, Double)
reverseLeapfrog eps n = negateMomentum . leapfrog eps n . negateMomentum

-- | The leapfrog integrator as a cartesian 'System' with phase-space state.
--
-- The state is the current @(position, momentum)@ pair.  The monomial direction
-- is ignored because the Gaussian-target dynamics are autonomous; the output
-- position is the current phase-space point (the state before the step).
leapfrogSystem :: Double -> Moore (,) (Double, Double) (->) (Mono (Double, Double) (Double, Double))
leapfrogSystem eps = moore $ \case
  (_, Left v) -> absurd v
  (s, Right _) ->
    let s' = leapfrogStep s eps
     in (s', (s, ()))

-- | The leapfrog integrator as a first-input-seeded 'Process'.
--
-- The seed is @(0, 1)@; the observation returns the current state as the
-- position, and the step uses 'leapfrogSystem'.
leapfrogProcess :: Double -> Process (Double, Double) (Double, Double)
leapfrogProcess eps = mooreAsProcess (leapfrogSystem eps) (0.0, 1.0)

-- ---------------------------------------------------------------------------
-- Yoshida-4 composition
-- ---------------------------------------------------------------------------

-- | Classic Yoshida coefficients for 4th-order symplectic composition.
--
-- One Yoshida-4 macro-step is the symmetric composition
-- @S(c1 eps) ∘ S(c2 eps) ∘ S(c3 eps)@ of three leapfrog steps.
yoshidaC1 :: Double
yoshidaC1 = 1.0 / (2.0 - 2.0 ** (1.0 / 3.0))

yoshidaC2 :: Double
yoshidaC2 = -((2.0 ** (1.0 / 3.0)) / (2.0 - 2.0 ** (1.0 / 3.0)))

yoshidaC3 :: Double
yoshidaC3 = yoshidaC1

-- | One Yoshida-4 macro-step on the Gaussian target.
yoshida4Step :: (Double, Double) -> Double -> (Double, Double)
yoshida4Step state eps =
  let s1 = leapfrogStep state (yoshidaC1 * eps)
      s2 = leapfrogStep s1 (yoshidaC2 * eps)
      s3 = leapfrogStep s2 (yoshidaC3 * eps)
   in s3

-- | N Yoshida-4 macro-steps.
yoshida4 :: Double -> Int -> (Double, Double) -> (Double, Double)
yoshida4 eps n state = iterate (`yoshida4Step` eps) state !! n

-- | Run the Yoshida-4 integrator backwards in time.
reverseYoshida4 :: Double -> Int -> (Double, Double) -> (Double, Double)
reverseYoshida4 eps n = negateMomentum . yoshida4 eps n . negateMomentum

-- | The Yoshida-4 integrator as a cartesian 'System'.
--
-- The output position is the current phase-space point (the state before the
-- macro-step); the state transition performs one Yoshida-4 macro-step.
yoshida4System :: Double -> Moore (,) (Double, Double) (->) (Mono (Double, Double) (Double, Double))
yoshida4System eps = moore $ \case
  (_, Left v) -> absurd v
  (s, Right _) ->
    let s' = yoshida4Step s eps
     in (s', (s, ()))

-- | The Yoshida-4 integrator as a first-input-seeded 'Process'.
yoshida4Process :: Double -> Process (Double, Double) (Double, Double)
yoshida4Process eps = mooreAsProcess (yoshida4System eps) (0.0, 1.0)

-- | Exact oracle: Yoshida-4 integration is reversible up to machine epsilon.
yoshida4Reversible :: Double -> Int -> (Double, Double) -> Bool
yoshida4Reversible eps n state =
  let forward = yoshida4 eps n state
      recovered = reverseYoshida4 eps n forward
      tol = 1e-12
      near u v = abs (u - v) <= tol
   in near (fst state) (fst recovered) && near (snd state) (snd recovered)

-- | Exact oracle: the Yoshida-4 map preserves phase-space volume.
--
-- The map is linear for the Gaussian target, and a composition of symplectic
-- maps has determinant 1.
yoshida4JacobianDet :: Double -> Int -> Double
yoshida4JacobianDet eps n =
  let f = yoshida4 eps n
      (x1, p1) = f (1.0, 0.0)
      (x2, p2) = f (0.0, 1.0)
   in x1 * p2 - p1 * x2

-- | Exact oracle: leapfrog integration is reversible up to machine epsilon.
--
-- Forward integration followed by momentum flip, backward integration, and
-- another momentum flip returns to the initial phase-space point.
leapfrogReversible :: Double -> Int -> (Double, Double) -> Bool
leapfrogReversible eps n state =
  let forward = leapfrog eps n state
      recovered = reverseLeapfrog eps n forward
      tol = 1e-12
      near u v = abs (u - v) <= tol
   in near (fst state) (fst recovered) && near (snd state) (snd recovered)

-- | Exact oracle: the leapfrog map preserves phase-space volume.
--
-- For the Gaussian target the leapfrog step is linear, so the Jacobian is
-- constant.  We estimate it by applying the n-step map to the standard basis
-- vectors and returning the determinant, which is exactly 1.0 for a symplectic
-- integrator.
leapfrogJacobianDet :: Double -> Int -> Double
leapfrogJacobianDet eps n =
  let f = leapfrog eps n
      (x1, p1) = f (1.0, 0.0)
      (x2, p2) = f (0.0, 1.0)
   in x1 * p2 - p1 * x2

-- ---------------------------------------------------------------------------
-- Order oracles (harmonic oscillator)
-- ---------------------------------------------------------------------------

-- | Energy of the harmonic oscillator @H(q,p) = (q^2 + p^2) / 2@.
harmonicEnergy :: (Double, Double) -> Double
harmonicEnergy (q, p) = (q * q + p * p) / 2

-- | Integrate a one-step method for a fixed total time.
integrateForTime ::
  ((Double, Double) -> Double -> (Double, Double)) ->
  Double ->
  Double ->
  (Double, Double) ->
  (Double, Double)
integrateForTime stepper eps totalTime state =
  let n = max 1 (round (totalTime / eps))
   in iterate (`stepper` eps) state !! n

-- | Ordinary-least-squares slope of log(error) vs log(step size).
logLogSlope :: [(Double, Double)] -> Double
logLogSlope pairs =
  let n = fromIntegral (length pairs)
      xs = map (log . fst) pairs
      ys = map (log . snd) pairs
      xMean = sum xs / n
      yMean = sum ys / n
      num = sum (zipWith (\x y -> (x - xMean) * (y - yMean)) xs ys)
      den = sum (map (\x -> (x - xMean) * (x - xMean)) xs)
   in num / den

-- | Measured energy-error slope for leapfrog on the harmonic oscillator.
--
-- Expected value is 2.0.  We use four step sizes and a fixed integration
-- length so that the leading term dominates the observed error.
leapfrogOrderSlope :: Double -> (Double, Double) -> Double
leapfrogOrderSlope totalTime state =
  let e0 = harmonicEnergy state
      errorAt eps =
        abs (harmonicEnergy (integrateForTime leapfrogStep eps totalTime state) - e0)
      pairs = [(eps, errorAt eps) | eps <- [0.05, 0.025, 0.0125, 0.00625]]
   in logLogSlope pairs

-- | Measured energy-error slope for Yoshida-4 on the harmonic oscillator.
--
-- Expected value is 4.0.
yoshida4OrderSlope :: Double -> (Double, Double) -> Double
yoshida4OrderSlope totalTime state =
  let e0 = harmonicEnergy state
      errorAt eps =
        abs (harmonicEnergy (integrateForTime yoshida4Step eps totalTime state) - e0)
      pairs = [(eps, errorAt eps) | eps <- [0.05, 0.025, 0.0125, 0.00625]]
   in logLogSlope pairs

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
