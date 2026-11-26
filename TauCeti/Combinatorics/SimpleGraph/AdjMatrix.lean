/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Changing the coefficients of the adjacency and degree matrices

The adjacency matrix `G.adjMatrix R` and the degree matrix `G.degMatrix R` of a simple graph have
entries built from `0`, `1` and natural-number casts, so applying a coefficient map entrywise
gives the same matrix over the target ring.

## Main results

* `SimpleGraph.adjMatrix_map`: the adjacency matrix is preserved by any map sending `0` to `0`
  and `1` to `1`.
* `SimpleGraph.degMatrix_map`: the degree matrix is preserved by any additive map sending `1`
  to `1`.
-/

public section

open Matrix

namespace SimpleGraph

variable {V R S F : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] [FunLike F R S]

/-- The adjacency matrix is preserved by any map sending `0` to `0` and `1` to `1`. -/
@[simp]
theorem adjMatrix_map [Zero R] [One R] [Zero S] [One S] [ZeroHomClass F R S] [OneHomClass F R S]
    (f : F) : (G.adjMatrix R).map f = G.adjMatrix S := by
  ext v w
  simp [apply_ite f]

/-- The degree matrix is preserved by any additive map sending `1` to `1`. -/
@[simp]
theorem degMatrix_map [AddMonoidWithOne R] [AddMonoidWithOne S] [AddMonoidHomClass F R S]
    [OneHomClass F R S] [Fintype V] [DecidableEq V] (f : F) :
    (G.degMatrix R).map f = G.degMatrix S := by
  ext v w
  simp [degMatrix, diagonal_apply, apply_ite f, map_natCast' f (map_one f)]

end SimpleGraph
