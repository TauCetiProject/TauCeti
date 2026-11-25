/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Sphere

/-!
# Betti numbers of small spaces

The Betti number `bettiNumber k X j` is the dimension of `Hⱼ(X; k)`. These examples read it off on
a few small spaces over a division ring.

A point has Betti numbers `1, 0, 0, …`. The circle and the punctured plane `ℝ² ∖ {0}`, which
deformation retracts onto it, both have first Betti number `1`, while the closed disc, which is
contractible, has first Betti number `0`. These are instances of
`TauCeti.finrank_singularHomology₀_eq_one`, `TauCeti.bettiNumber_eq_zero_of_contractibleSpace`,
`TauCeti.bettiNumber_sphere` and `TauCeti.bettiNumber_compl_singleton`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Proposition 2.7 and Corollary 2.14.
-/

public section

noncomputable section

open Metric Module

namespace TauCeti.Examples

variable (k : Type) [DivisionRing k]

/-- A point has zeroth Betti number `1`. -/
example : bettiNumber k PUnit 0 = 1 :=
  (bettiNumber_def k PUnit 0).trans (finrank_singularHomology₀_eq_one (TopCat.of PUnit))

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
  have := contractibleSpace_closedBall (x := (0 : EuclideanSpace ℝ (Fin 2))) zero_le_one
  bettiNumber_eq_zero_of_contractibleSpace k one_ne_zero

end TauCeti.Examples
