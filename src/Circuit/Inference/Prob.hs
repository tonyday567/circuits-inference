{-# OPTIONS_GHC -Wno-orphans #-}

-- | Effectful probability row: @Prob (Kleisli m) r@.
--
-- The function-arrow instances in "Circuit.Prob" are the reference semantics.
-- This module ports the cartesian and cocartesian structural instances to the
-- Kleisli base arrow, which is the substrate for sampling-based inference.
-- The tensor remains premonoidal: the two nestings 'parFGK' and 'parGFK' agree
-- on distribution but differ operationally when effects do not commute.
module Circuit.Inference.Prob
  ( -- * Re-export base type
    Prob (..),

    -- * Kleisli primitives
    embedK,
    fromWeightedK,
    scoreK,
    massK,
    copyPK,
    discardPK,
    choiceByK,
    orPK,

    -- * Parallel nestings (premonoidal)
    parFGK,
    parGFK,

    -- * Traced Either over effectful base arrows
    traceEK,
    traceENK,
  )
where

import Circuit.Category (Category (..))
import Circuit.Channel (Channel (..), Strength (..))
import Circuit.Prob (Prob (..))
import Control.Arrow (Kleisli (..))
import Prelude hiding (id, (.))

-- | Lift a pure function into an effectful probability morphism.
embedK :: (a -> b) -> Prob (Kleisli m) r a b
embedK h = Prob $ \(Kleisli k) -> Kleisli $ \(x, a) -> k (x, h a)

-- | Build a probability morphism from a finite weighted table.
fromWeightedK :: (Num r, Monad m) => [(b, r)] -> Prob (Kleisli m) r () b
fromWeightedK xs = Prob $ \(Kleisli k) -> Kleisli $ \(x, ()) -> do
  rs <- traverse (\(b, w) -> fmap (w *) (k (x, b))) xs
  pure (sum rs)

-- | Scale the result of a continuation.
scoreK :: (Monad m) => (r -> r) -> Prob (Kleisli m) r a a
scoreK scale = Prob $ \(Kleisli k) -> Kleisli $ \(x, a) -> fmap scale (k (x, a))

-- | Compute the total mass of an unnormalised morphism against the unit
-- continuation.
massK :: (Monad m) => r -> Prob (Kleisli m) r a b -> a -> m r
massK one (Prob f) a = runKleisli (f (Kleisli (\_ -> pure one))) ((), a)

-- | Deterministic copy.
copyPK :: Prob (Kleisli m) r a (a, a)
copyPK = embedK (\a -> (a, a))

-- | Deterministic discard.
discardPK :: Prob (Kleisli m) r a ()
discardPK = embedK (const ())

-- | Binary choice combined by a scalar operation.
choiceByK ::
  (Monad m) =>
  (r -> r -> r) ->
  Prob (Kleisli m) r a b ->
  Prob (Kleisli m) r a b ->
  Prob (Kleisli m) r a b
choiceByK (<+>) (Prob f) (Prob g) = Prob $ \k -> Kleisli $ \p -> do
  rf <- runKleisli (f k) p
  rg <- runKleisli (g k) p
  pure (rf <+> rg)

-- | Angelic choice for @r = Bool@.
orPK ::
  (Monad m) =>
  Prob (Kleisli m) Bool a b ->
  Prob (Kleisli m) Bool a b ->
  Prob (Kleisli m) Bool a b
orPK = choiceByK (||)

-- ---------------------------------------------------------------------------
-- Cartesian structural instances
-- ---------------------------------------------------------------------------

instance (Monad m) => Channel (,) (Prob (Kleisli m) r) where
  assoc = embedK assoc
  assoc' = embedK assoc'
  slide = embedK slide

instance (Monad m) => Strength (,) (Prob (Kleisli m) r) where
  strength (Prob f) = Prob $ \k -> f (k . assoc) . assoc'

-- ---------------------------------------------------------------------------
-- Cocartesian structural instances
-- ---------------------------------------------------------------------------

instance (Monad m) => Channel Either (Prob (Kleisli m) r) where
  assoc = embedK assoc
  assoc' = embedK assoc'
  slide = embedK slide

instance (Monad m) => Strength Either (Prob (Kleisli m) r) where
  strength (Prob f) = Prob $ \(Kleisli k) -> Kleisli $ \(x, e) -> case e of
    Left a -> k (x, Left a)
    Right b -> runKleisli (f (Kleisli (\(x', c) -> k (x', Right c)))) (x, b)

-- ---------------------------------------------------------------------------
-- Parallel nestings (Fubini on the linear/commutative fragment)
-- ---------------------------------------------------------------------------

-- | Parallel composition: @g@ runs at context @(x, b)@, @f@ runs at context
-- @(x, c)@.  One of two lawful nestings; operationally distinct from 'parGFK'
-- when the underlying monad has ordered effects.
parFGK ::
  Prob (Kleisli m) r a b ->
  Prob (Kleisli m) r c d ->
  Prob (Kleisli m) r (a, c) (b, d)
parFGK (Prob f) (Prob g) = Prob $ \(Kleisli k) ->
  let kg = Kleisli $ \((ctx, b), d) -> k (ctx, (b, d))
      Kleisli gc = g kg
      kf = Kleisli $ \((ctx, c), b) -> gc ((ctx, b), c)
      Kleisli fa = f kf
   in Kleisli $ \(ctx, (a, c)) -> fa ((ctx, c), a)

-- | Parallel composition: @f@ runs at context @(x, d)@, @g@ runs at context
-- @(x, a)@.  The other nesting; agrees with 'parFGK' on distribution for the
-- linear fragment, but differs operationally on ordered effects.
parGFK ::
  Prob (Kleisli m) r a b ->
  Prob (Kleisli m) r c d ->
  Prob (Kleisli m) r (a, c) (b, d)
parGFK (Prob f) (Prob g) = Prob $ \(Kleisli k) ->
  let kf = Kleisli $ \((ctx, d), b) -> k (ctx, (b, d))
      Kleisli fa = f kf
      kg = Kleisli $ \((ctx, a), d) -> fa ((ctx, d), a)
      Kleisli gb = g kg
   in Kleisli $ \(ctx, (a, c)) -> gb ((ctx, a), c)

-- ---------------------------------------------------------------------------
-- Traced Either (productive under effectful base arrows)
-- ---------------------------------------------------------------------------

-- | Least-fixpoint trace over the 'Either' tensor for @Kleisli m@.
--
-- Recursive re-entries are productive because each recursive call is an
-- effectful action in @m@.  For almost-surely terminating bodies (e.g. a
-- geometric sampler) the trace returns a sample rather than diverging.
traceEK ::
  Prob (Kleisli m) r (Either a s) (Either b s) ->
  Prob (Kleisli m) r a b
traceEK (Prob f) = Prob $ \(Kleisli k) ->
  let step (x, Left b) = k (x, b)
      step (x, Right s) = runKleisli (f (Kleisli step)) (x, Right s)
   in Kleisli $ \(x, a) -> runKleisli (f (Kleisli step)) (x, Left a)

-- | Fuel-bounded variant of 'traceEK'.
traceENK ::
  (Monad m) =>
  r ->
  Int ->
  Prob (Kleisli m) r (Either a s) (Either b s) ->
  Prob (Kleisli m) r a b
traceENK zero n0 (Prob f) = Prob $ \(Kleisli k) ->
  let step _ (x, Left b) = k (x, b)
      step n (x, Right s)
        | n <= 0 = pure zero
        | otherwise = runKleisli (f (Kleisli (step (n - 1)))) (x, Right s)
   in Kleisli $ \(x, a) -> runKleisli (f (Kleisli (step n0))) (x, Left a)
