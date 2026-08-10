-- | Sequential Monte Carlo on a discrete hidden Markov model.
--
-- A 2-state HMM with binary observations.  Exact inference by enumeration
-- of all 2^T state sequences.  SMC particle filter approximates the same
-- posterior.  Oracle: L1 distance between SMC and exact marginal < 0.1.
module Circuit.Inference.SMC
  ( -- * Model
    State (..),
    transProb,
    obsProb,
    initialP,

    -- * Exact inference
    exactFiltering,

    -- * SMC particle filter
    particleFilter,

    -- * Oracle
    trace5,
    l1Distance,
  )
where

import Data.List (foldl')
import Data.Maybe (fromMaybe)
import System.Random (StdGen, mkStdGen, randomR)

-- ---------------------------------------------------------------------------
-- 2-state HMM
-- ---------------------------------------------------------------------------

data State = StateA | StateB
  deriving (Eq, Ord, Show)

allStates :: [State]
allStates = [StateA, StateB]

-- | Initial distribution: P(S₁=S).
initialP :: State -> Double
initialP StateA = 0.6
initialP StateB = 0.4

-- | Transition: P(next | current).
transProb :: State -> State -> Double
transProb StateA StateA = 0.7
transProb StateA StateB = 0.3
transProb StateB StateA = 0.2
transProb StateB StateB = 0.8

-- | Observation likelihood: P(o | state). o ∈ {0, 1}.
obsProb :: Int -> State -> Double
obsProb 1 StateA = 0.9
obsProb 1 StateB = 0.2
obsProb 0 StateA = 0.1
obsProb 0 StateB = 0.8
obsProb _ _ = error "obsProb: observation must be 0 or 1"

-- | 5-step trace, 2⁵ = 32 sequences for exact enumeration.
trace5 :: [Int]
trace5 = [1, 0, 1, 0, 1]

-- ---------------------------------------------------------------------------
-- Exact inference by full enumeration
-- ---------------------------------------------------------------------------

-- | Compute joint probability P(S_1…S_T, O_1…O_T) for a given state sequence.
jointProb :: [State] -> [Int] -> Double
jointProb [s] [o] = initialP s * obsProb o s
jointProb (s : ss@(s' : _)) (o : os) =
  initialP s * obsProb o s * go s' (zip ss os)
  where
    go _ [] = 1
    go prev ((cur, o') : rest) = transProb prev cur * obsProb o' cur * go cur rest
jointProb _ _ = error "jointProb: length mismatch"

-- | All state sequences of length t.
allSeqs :: Int -> [[State]]
allSeqs 0 = [[]]
allSeqs k = [s : rest | s <- allStates, rest <- allSeqs (k - 1)]

-- | Exact filtering P(S_T | O_{1:T}) by enumeration.
-- Returns [(S, normalised probability)].
exactFiltering :: [Int] -> [(State, Double)]
exactFiltering obs =
  let t = length obs
      seqs = allSeqs t
      joints = map (\seq -> (last seq, jointProb seq obs)) seqs
      -- Sum probability for each final state
      totalByState s = sum [p | (lastS, p) <- joints, lastS == s]
      total = sum (map snd joints)
   in [(s, totalByState s / total) | total > 0, s <- allStates]

-- ---------------------------------------------------------------------------
-- Particle filter (SMC) — deterministic seed for reproducibility
-- ---------------------------------------------------------------------------

-- | Run a particle filter and return empirical final filtering distribution.
-- n particles, deterministic RNG (seed = 42), systematic resampling.
particleFilter :: [Int] -> Int -> [(State, Double)]
particleFilter obs nP =
  let gen0 = mkStdGen 42

      step (particles, gen) o =
        let -- Propagate each particle by sampling next state
            nextState s g =
              let (r, g') = randomR (0 :: Double, 1) g
               in (if r < transProb s StateA then StateA else StateB, g')
            (propagated, gen1) = foldl' (\(ps, g) p -> let (p', g') = nextState p g in (ps ++ [p'], g')) ([], gen) particles
            -- Weight by observation likelihood
            ws = map (\p -> obsProb o p) propagated
            total = sum ws
            normWs = if total > 0 then map (/ total) ws else replicate nP (1 / fromIntegral nP)
            -- Systematic resample
            (resampled, gen2) = resample (zip propagated normWs) nP gen1
         in (resampled, gen2)

      -- Initial: all particles start in StateA (deterministic)
      initParticles = replicate nP StateA

      (finalParticles, _) = foldl' step (initParticles, gen0) obs

      -- Filtering estimate: fraction in each state
      prob s = fromIntegral (length (filter (== s) finalParticles)) / fromIntegral nP
   in [(s, prob s) | s <- allStates]

-- | Systematic resampling with a supplied RNG.
resample :: [(State, Double)] -> Int -> StdGen -> ([State], StdGen)
resample weighted n gen =
  let cumWeights = drop 1 (scanl (+) 0 (map snd weighted))
      stepVal = 1.0 / fromIntegral n
      (u0, gen') = randomR (0, stepVal) gen
      threshold i = u0 + fromIntegral i * stepVal
      pick u = fst $ head $ dropWhile (\(_, c) -> c < u) (zip (map fst weighted) cumWeights)
      picked = map (pick . threshold) [0 .. n - 1]
   in (picked, gen')

-- ---------------------------------------------------------------------------
-- Oracle
-- ---------------------------------------------------------------------------

-- | L1 distance between two filtering distributions.
l1Distance :: [(State, Double)] -> [(State, Double)] -> Double
l1Distance d1 d2 =
  sum [abs (look s d1 - look s d2) | s <- allStates]
  where
    look s = fromMaybe 0 . Prelude.lookup s
