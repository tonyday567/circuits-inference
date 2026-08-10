-- | Finite-state stationary distribution via linear solve.
--
-- A 3-state Markov chain transition matrix P. The stationary distribution
-- π satisfies π·P = π with Σπ = 1.
-- Oracle: power iteration converges to exact solution within 1e-12.
module Circuit.Inference.LinearSolve
  ( transition,
    exactStationary,
    powerIteration,
  )
where

-- | 3-state transition matrix: rows sum to 1.
transition :: [[Double]]
transition =
  [ [0.5, 0.3, 0.2],
    [0.1, 0.7, 0.2],
    [0.3, 0.3, 0.4]
  ]

-- | Exact stationary distribution: solved from π·(P-I) = 0, Σπ = 1.
-- π = [0.25, 0.5, 0.25]
exactStationary :: [Double]
exactStationary = [0.25, 0.5, 0.25]

-- | Power iteration converges to stationary distribution.
powerIteration :: [Double]
powerIteration =
  let step v = [sum [v !! j * transition !! j !! i | j <- [0 .. 2]] | i <- [0 .. 2]]
   in converge step [1 / 3, 1 / 3, 1 / 3]
  where
    converge step v =
      let v' = map (/ sum v) (step v)
       in if maxDiff v v' < 1e-14 then v' else converge step v'
    maxDiff v w = maximum (zipWith (\x y -> abs (x - y)) v w)
