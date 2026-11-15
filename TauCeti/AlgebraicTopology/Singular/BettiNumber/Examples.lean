/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.BettiNumber.Sphere

/-!
# Betti numbers of small spaces

The Betti number `bettiNumber k X j` is the dimension of `Hⱼ(X; k)`, with the junk value `0` when
that homology is infinite-dimensional. This file computes it on a few small spaces, which test
both the dimension count and the junk value.

* **Infinitely many path components.** The zeroth homology of the discrete space `ℕ` is free on
  countably many generators, so it has rank `ℵ₀` (`TauCeti.rank_singularHomology_zero_nat`), and
  the zeroth Betti number of `ℕ` is the junk value `0` (`TauCeti.bettiNumber_zero_nat`). A
  cardinal-valued count, `TauCeti.rank_singularHomology_zero`, records `ℵ₀` instead.
* **A point, the circle, the punctured plane and the disc.** A point has Betti numbers
  `1, 0, 0, …` over every division ring. The circle and the punctured plane `ℝ² ∖ {0}`, which
  deformation retracts onto it, both have first Betti number `1`, while the closed disc, which is
  contractible, has first Betti number `0`. These are instances of
  `TauCeti.bettiNumber_zero_eq_one`, `TauCeti.bettiNumber_eq_zero_of_contractibleSpace`,
  `TauCeti.bettiNumber_sphere` and `TauCeti.bettiNumber_compl_singleton`, recorded below as
  examples.

## Main results

* `TauCeti.rank_singularHomology_zero_nat`: the zeroth homology of `ℕ` has rank `ℵ₀`.
* `TauCeti.bettiNumber_zero_nat`: the zeroth Betti number of `ℕ` is `0`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.7 and Corollary 2.14.
-/

public section

noncomputable section

open Metric Module

namespace TauCeti

section Nat

variable (k : Type) [Ring k] [StrongRankCondition k]

/-- **The zeroth homology of `ℕ` has rank `ℵ₀`.** With the discrete topology, `ℕ` has countably
many path components, its points, and `H₀(ℕ; k)` is free on them. -/
theorem rank_singularHomology_zero_nat :
    Module.rank k (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} k) 0).obj
      (ModuleCat.of k k)).obj (TopCat.of ℕ)) = Cardinal.aleph0 := by
  rw [rank_singularHomology_zero_of_discreteTopology, Cardinal.mk_nat]

/-- **The zeroth Betti number of `ℕ` is the junk value `0`.** The zeroth homology of the discrete
space `ℕ` is infinite-dimensional (`TauCeti.rank_singularHomology_zero_nat`), so its dimension
`Module.finrank` is `0`, although `ℕ` has infinitely many path components. -/
theorem bettiNumber_zero_nat : bettiNumber k ℕ 0 = 0 := by
  rw [bettiNumber_def, Module.finrank, rank_singularHomology_zero_nat, Cardinal.aleph0_toNat]

end Nat

section Examples

variable (k : Type) [DivisionRing k]

/-- A point has zeroth Betti number `1`. -/
example : bettiNumber k PUnit 0 = 1 := bettiNumber_zero_eq_one k

/-- A point has no homology in positive degrees. -/
example {j : ℕ} (hj : j ≠ 0) : bettiNumber k PUnit j = 0 :=
  bettiNumber_eq_zero_of_contractibleSpace k hj

/-- The circle has first Betti number `1`. -/
example : bettiNumber k (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) 1 = 1 := by
  simp [bettiNumber_sphere k (finrank_euclideanSpace_fin (n := 2))]

/-- The punctured plane `ℝ² ∖ {0}` has first Betti number `1`. -/
example : bettiNumber k ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) 1 = 1 := by
  simp [bettiNumber_compl_singleton k (finrank_euclideanSpace_fin (n := 2))]

/-- The closed disc has first Betti number `0`. -/
example : bettiNumber k (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) 1 = 0 :=
  have := (convex_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1).contractibleSpace
    (nonempty_closedBall.2 zero_le_one)
  bettiNumber_eq_zero_of_contractibleSpace k one_ne_zero

end Examples

end TauCeti
