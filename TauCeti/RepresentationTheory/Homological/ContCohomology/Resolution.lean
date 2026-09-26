/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# Pointwise formulas for the coinduced resolution

Mathlib computes the continuous cohomology of a topological representation `X` from the coinduced
resolution `TopRep.resolutionX X n`, the iterated function space `C(G, C(G, …, C(G, X)))`, whose
differential `TopRep.d` is defined recursively by `d (n + 1) F x = F - d n (F x)`. This file
records the pointwise formulas that the recursion gives for the action and for the differential on
a successor level, and their consequence that evaluation at `1` contracts the resolution:
`d n (F 1) + (d (n + 1) F) 1 = F`. Evaluation at `1` is not `G`-equivariant, so the contraction
does not descend to the invariants, which are the homogeneous cochains; it is nevertheless what
drives the acyclicity of coinduced modules.

## Main results

* `TopRep.resolutionX_succ_ρ_apply_apply` and `TopRep.hom_d_succ_apply_apply`: the action and
  the differential on a successor level of the resolution, at a point.
* `TopRep.d_apply_one_add_d_apply_one`: evaluation at `1` contracts the coinduced resolution.
-/

public section

namespace TopRep

variable {k : Type*} [Ring k] [TopologicalSpace k] {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (X : TopRep k G)

/-- The action on a successor level of the coinduced resolution, at a point:
`(g • F) x = g • F (g⁻¹ * x)`. -/
@[simp]
theorem resolutionX_succ_ρ_apply_apply (n : ℕ) (g : G) (F : (resolutionX X (n + 1)).V) (x : G) :
    ((resolutionX X (n + 1)).ρ g F) x = (resolutionX X n).ρ g (F (g⁻¹ * x)) :=
  ContRepresentation.coind₁_apply_apply (resolutionX X n).ρ g F x

/-- The successor differential of the coinduced resolution, at a point:
`(d (n + 1) F) x = F - d n (F x)`. -/
@[simp]
theorem hom_d_succ_apply_apply (n : ℕ) (F : (resolutionX X (n + 1)).V) (x : G) :
    ((d X (n + 1)).hom F) x = F - (d X n).hom (F x) :=
  (rfl)

/-- **Evaluation at `1` contracts the coinduced resolution**: every `F` in level `n + 1`
satisfies `F = d n (F 1) + (d (n + 1) F) 1`. Evaluation at `1` is not `G`-equivariant, so this
contraction does not descend to the homogeneous cochains. -/
theorem d_apply_one_add_d_apply_one (n : ℕ) (F : (resolutionX X (n + 1)).V) :
    (d X n).hom (F 1) + ((d X (n + 1)).hom F) 1 = F := by
  rw [hom_d_succ_apply_apply, add_sub_cancel]

end TopRep
