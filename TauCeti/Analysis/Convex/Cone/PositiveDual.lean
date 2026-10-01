/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Cone.Dual

/-!
# Monotone continuous functionals determine a closed order

Let `E` be a locally convex real topological vector space with a partial order compatible with
its module structure, whose positive cone `{x | 0 ≤ x}` is closed. Farkas' lemma
(`ProperCone.hyperplane_separation_point`) separates a point outside this cone from the cone by a
continuous linear functional that is nonnegative on it, that is, by a monotone one. Consequently
`x ≤ y` exactly when `f x ≤ f y` for every monotone continuous linear functional `f`, and such
functionals separate the points of `E`.

This reduces statements about vectors with nonnegative coordinates in an ordered space to
statements about nonnegative real numbers, one monotone functional at a time.

## Main results

* `TauCeti.le_iff_forall_monotone_dual_le`: `x ≤ y` if and only if `f x ≤ f y` for every
  monotone continuous linear functional `f`.
* `TauCeti.eq_of_forall_monotone_dual_eq`: monotone continuous linear functionals separate points.
-/

public section

namespace TauCeti

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  [Module ℝ E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [PartialOrder E]
  [IsOrderedAddMonoid E] [PosSMulMono ℝ E] [OrderClosedTopology E] {x y : E}

/-- **Closed orders are determined by monotone functionals.** In a locally convex real ordered
vector space with closed positive cone, `x ≤ y` if and only if `f x ≤ f y` for every monotone
continuous linear functional `f`. -/
theorem le_iff_forall_monotone_dual_le :
    x ≤ y ↔ ∀ f : StrongDual ℝ E, Monotone f → f x ≤ f y := by
  refine ⟨fun hxy f hf ↦ hf hxy, fun h ↦ ?_⟩
  -- Otherwise `y - x` lies outside the closed positive cone, and Farkas' lemma separates them.
  by_contra hxy
  obtain ⟨f, hf, hfyx⟩ := (ProperCone.positive ℝ E).hyperplane_separation_point
    (x₀ := y - x) (by simpa [sub_nonneg] using hxy)
  have hmono : Monotone f :=
    (monotone_iff_map_nonneg f).2 fun z hz ↦ hf z (ProperCone.mem_positive.2 hz)
  have := h f hmono
  rw [map_sub] at hfyx
  linarith

/-- **Monotone functionals separate points.** In a locally convex real ordered vector space with
closed positive cone, two vectors on which every monotone continuous linear functional agrees are
equal. -/
theorem eq_of_forall_monotone_dual_eq (h : ∀ f : StrongDual ℝ E, Monotone f → f x = f y) :
    x = y :=
  le_antisymm (le_iff_forall_monotone_dual_le.2 fun f hf ↦ (h f hf).le)
    (le_iff_forall_monotone_dual_le.2 fun f hf ↦ (h f hf).ge)

end TauCeti
