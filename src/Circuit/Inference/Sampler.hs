-- | Effectful samplers as @Prob (K IO)@ morphisms.
module Circuit.Inference.Sampler
  ( -- * Primitive samplers
    bernoulli,
    uniformDiscrete,

    -- * Recursive trace samplers
    geometric,
    geometricBody,
    sample,
  )
where

import Circuit.Category (K (..))
import Circuit.Inference.Prob (Prob (..), fromWeightedK, traceEK)
import System.Random (randomRIO)

-- | Bernoulli trial with success probability @p@.
--
-- Output 'True' with probability @p@, 'False' with probability @1-p@.
bernoulli :: Double -> Prob (K IO) Double () Bool
bernoulli p = fromWeightedK [(True, p), (False, 1 - p)]

-- | Discrete uniform distribution over a finite list.
uniformDiscrete :: [a] -> Prob (K IO) Double () a
uniformDiscrete xs =
  let n = length xs
      w = 1 / fromIntegral n
   in fromWeightedK [(x, w) | x <- xs]

-- | Extract a single sample from a sampler by using the output itself as the
-- dualizing object.
sample :: Prob (K IO) b () b -> IO b
sample s = runK (runProb s (K (\(_, b) -> pure b))) ((), ())

-- | Geometric distribution counting failures before the first success.
--
-- Implemented as a terminating 'traceEK' over an effectful Bernoulli body.
-- Each recursive iteration performs an 'IO' sample, so the trace is productive
-- and returns a value with probability 1 (for @0 < p <= 1@).
geometric :: Double -> Prob (K IO) Int () Int
geometric p = traceEK (geometricBody p)

-- | Body of the geometric sampler.
--
-- Input: @Left ()@ on first call, @Right n@ on recursive calls where @n@ is
-- the current failure count.  Output: @Right k@ terminates with final count
-- @k@; @Left k@ continues with count @k@.
geometricBody ::
  Double ->
  Prob (K IO) Int (Either () Int) (Either Int Int)
geometricBody p = Prob $ \(K k) -> K $ \(x, e) -> do
  u <- randomRIO (0, 1) :: IO Double
  let out = case e of
        -- Left value escapes as the final output; Right value feeds back.
        -- State counts failures so far, so the first failure advances to 1.
        Left () -> if u < p then Left 0 else Right 1
        Right n -> if u < p then Left n else Right (n + 1)
  k (x, out)
