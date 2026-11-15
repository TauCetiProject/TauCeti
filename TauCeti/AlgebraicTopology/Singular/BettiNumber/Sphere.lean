/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.BettiNumber.Basic
public import TauCeti.AlgebraicTopology.Singular.Sphere
public import TauCeti.Topology.Homotopy.PuncturedStarConvex
import TauCeti.Algebra.Category.ModuleCat.Finrank

/-!
# Betti numbers of spheres and punctured vector spaces

Let `E` be a real normed space of dimension `d + 1`. Over a ring with the strong rank condition,
such as a field, the unit sphere `S(E) ≅ Sᵈ` has Betti numbers `1` in degrees `0` and `d` and `0`
in every other degree, with `b₀(S⁰) = 2` when `d = 0` (`TauCeti.bettiNumber_sphere`). The
complement `E ∖ {y}` of a point deformation retracts onto a sphere about `y`, so it has the same
Betti numbers (`TauCeti.bettiNumber_compl_singleton`). For instance the circle and the punctured
plane `ℝ² ∖ {0}` both have first Betti number `1`, while the closed disc, which is contractible,
has first Betti number `0` (`TauCeti.bettiNumber_eq_zero_of_contractibleSpace`).

## Main results

* `TauCeti.bettiNumber_sphere`: the Betti numbers of the unit sphere of a space of dimension
  `d + 1`.
* `TauCeti.bettiNumber_compl_singleton`: the Betti numbers of the complement of a point in such
  a space.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.1, Corollary 2.14.
-/

public section

noncomputable section

open Metric Module

universe u

namespace TauCeti

variable (k : Type u) [Ring k] [StrongRankCondition k] {E : Type u} [NormedAddCommGroup E]
  [NormedSpace ℝ E] {d : ℕ}

/-- **The Betti numbers of a sphere.** If the real normed space `E` has dimension `d + 1`, its
unit sphere has Betti number `1` in degree `d`, plus `1` in degree zero, and `0` in every other
degree. So `Sᵈ` has Betti numbers `1` in degrees `0` and `d` for `d > 0`, and `S⁰`, two points,
has `b₀ = 2`. -/
theorem bettiNumber_sphere (hE : finrank ℝ E = d + 1) (j : ℕ) :
    bettiNumber k (sphere (0 : E) 1) j = (if j = d then 1 else 0) + if j = 0 then 1 else 0 := by
  have := Module.finite_of_finrank_eq_succ hE
  rw [bettiNumber_def,
    ModuleCat.finrank_singularHomology_sphere_of_finrank_eq_succ (ModuleCat.of k k) hE j,
    ModuleCat.finrank_of_self]

/-- **The Betti numbers of a punctured vector space.** If the real normed space `E` has dimension
`d + 1`, the complement of a point `y` has the Betti numbers of the sphere `Sᵈ`, onto which it
deformation retracts: `1` in degree `d`, plus `1` in degree zero, and `0` in every other degree. -/
theorem bettiNumber_compl_singleton (hE : finrank ℝ E = d + 1) (y : E) (j : ℕ) :
    bettiNumber k ({y}ᶜ : Set E) j = (if j = d then 1 else 0) + if j = 0 then 1 else 0 := by
  rw [(complSingletonHomotopyEquivSphere y).bettiNumber_eq, bettiNumber_sphere k hE]

end TauCeti
