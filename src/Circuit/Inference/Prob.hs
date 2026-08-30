{-# OPTIONS_GHC -Wno-orphans #-}

-- | Effectful probability row: @Prob (K m) r@.
--
-- The function-arrow instances in "Circuit.Prob" are the reference semantics.
-- This module ports the cartesian and cocartesian structural instances to the
-- K base arrow, which is the substrate for sampling-based inference.
-- The tensor remains premonoidal: the two nestings 'parFGK' and 'parGFK' agree
-- on distribution but differ operationally when effects do not commute.
module Circuit.Inference.Prob
  ( -- * Re-export base type
    Prob (..),

    -- * K primitives
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

import Circuit.Category (Category (..), K (..))
import Circuit.Traced (Assoc (..), Slide (..), Strength (..), Yank (..))
import Circuit.Prob (Prob (..))
import Prelude hiding (id, (.))

-- | Lift a pure function into an effectful probability morphism.
embedK :: (a -> b) -> Prob (K m) r a b
embedK h = Prob $ \(K k) -> K $ \(x, a) -> k (x, h a)

-- | Build a probability morphism from a finite weighted table.
fromWeightedK :: (Num r, Monad m) => [(b, r)] -> Prob (K m) r () b
fromWeightedK xs = Prob $ \(K k) -> K $ \(x, ()) -> do
  rs <- traverse (\(b, w) -> fmap (w *) (k (x, b))) xs
  pure (sum rs)

-- | Scale the result of a continuation.
scoreK :: (Monad m) => (r -> r) -> Prob (K m) r a a
scoreK scale = Prob $ \(K k) -> K $ \(x, a) -> fmap scale (k (x, a))

-- | Compute the total mass of an unnormalised morphism against the unit
-- continuation.
massK :: (Monad m) => r -> Prob (K m) r a b -> a -> m r
massK one (Prob f) a = runK (f (K (\_ -> pure one))) ((), a)

-- | Deterministic copy.
copyPK :: Prob (K m) r a (a, a)
copyPK = embedK (\a -> (a, a))

-- | Deterministic discard.
discardPK :: Prob (K m) r a ()
discardPK = embedK (const ())

-- | Binary choice combined by a scalar operation.
choiceByK ::
  (Monad m) =>
  (r -> r -> r) ->
  Prob (K m) r a b ->
  Prob (K m) r a b ->
  Prob (K m) r a b
choiceByK (<+>) (Prob f) (Prob g) = Prob $ \k -> K $ \p -> do
  rf <- runK (f k) p
  rg <- runK (g k) p
  pure (rf <+> rg)

-- | Angelic choice for @r = Bool@.
orPK ::
  (Monad m) =>
  Prob (K m) Bool a b ->
  Prob (K m) Bool a b ->
  Prob (K m) Bool a b
orPK = choiceByK (||)

-- ---------------------------------------------------------------------------
-- Cartesian structural instances
-- ---------------------------------------------------------------------------

instance (Monad m) => Assoc (,) (Prob (K m) r) where
  assoc = embedK assoc
  assoc' = embedK assoc'

instance (Monad m) => Slide (,) (Prob (K m) r) where
  slide = embedK slide

instance (Monad m) => Strength (,) (Prob (K m) r) where
  strength (Prob f) = Prob $ \k -> f (k . assoc) . assoc'

-- ---------------------------------------------------------------------------
-- Cocartesian structural instances
-- ---------------------------------------------------------------------------

instance (Monad m) => Assoc Either (Prob (K m) r) where
  assoc = embedK assoc
  assoc' = embedK assoc'

instance (Monad m) => Slide Either (Prob (K m) r) where
  slide = embedK slide

instance (Monad m) => Strength Either (Prob (K m) r) where
  strength (Prob f) = Prob $ \(K k) -> K $ \(x, e) -> case e of
    Left a -> k (x, Left a)
    Right b -> runK (f (K (\(x', c) -> k (x', Right c)))) (x, b)

-- ---------------------------------------------------------------------------
-- Parallel nestings (Fubini on the linear/commutative fragment)
-- ---------------------------------------------------------------------------

-- | Parallel composition: @g@ runs at context @(x, b)@, @f@ runs at context
-- @(x, c)@.  One of two lawful nestings; operationally distinct from 'parGFK'
-- when the underlying monad has ordered effects.
parFGK ::
  Prob (K m) r a b ->
  Prob (K m) r c d ->
  Prob (K m) r (a, c) (b, d)
parFGK (Prob f) (Prob g) = Prob $ \(K k) ->
  let kg = K $ \((ctx, b), d) -> k (ctx, (b, d))
      K gc = g kg
      kf = K $ \((ctx, c), b) -> gc ((ctx, b), c)
      K fa = f kf
   in K $ \(ctx, (a, c)) -> fa ((ctx, c), a)

-- | Parallel composition: @f@ runs at context @(x, d)@, @g@ runs at context
-- @(x, a)@.  The other nesting; agrees with 'parFGK' on distribution for the
-- linear fragment, but differs operationally on ordered effects.
parGFK ::
  Prob (K m) r a b ->
  Prob (K m) r c d ->
  Prob (K m) r (a, c) (b, d)
parGFK (Prob f) (Prob g) = Prob $ \(K k) ->
  let kf = K $ \((ctx, d), b) -> k (ctx, (b, d))
      K fa = f kf
      kg = K $ \((ctx, a), d) -> fa ((ctx, d), a)
      K gb = g kg
   in K $ \(ctx, (a, c)) -> gb ((ctx, a), c)

-- ---------------------------------------------------------------------------
-- Traced Either (productive under effectful base arrows)
-- ---------------------------------------------------------------------------

-- | Least-fixpoint trace over the 'Either' tensor for @K m@.
--
-- Recursive re-entries are productive because each recursive call is an
-- effectful action in @m@.  For almost-surely terminating bodies (e.g. a
-- geometric sampler) the trace returns a sample rather than diverging.
traceEK ::
  Prob (K m) r (Either a s) (Either b s) ->
  Prob (K m) r a b
traceEK (Prob f) = Prob $ \(K k) ->
  let step (x, Left b) = k (x, b)
      step (x, Right s) = runK (f (K step)) (x, Right s)
   in K $ \(x, a) -> runK (f (K step)) (x, Left a)

-- | Fuel-bounded variant of 'traceEK'.
traceENK ::
  (Monad m) =>
  r ->
  Int ->
  Prob (K m) r (Either a s) (Either b s) ->
  Prob (K m) r a b
traceENK zero n0 (Prob f) = Prob $ \(K k) ->
  let step _ (x, Left b) = k (x, b)
      step n (x, Right s)
        | n <= 0 = pure zero
        | otherwise = runK (f (K (step (n - 1)))) (x, Right s)
   in K $ \(x, a) -> runK (f (K (step n0))) (x, Left a)
