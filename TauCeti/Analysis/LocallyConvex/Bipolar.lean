/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LocallyConvex.Polar

/-!
# The bipolar theorem

The bipolar of a nonempty absolutely convex set in a real or complex locally convex
space is its closure. Equivalently, continuous linear functionals bounded by one on
the set characterize its closure. No completeness or Hausdorff hypothesis is needed.

For an arbitrary set, the bipolar is the closed absolutely convex hull after adjoining
zero. Adjoining zero matters for the empty set, since Mathlib's absolutely convex hull
of the empty set is empty, whereas a bipolar always contains zero.

The pairing and both polars are Mathlib's `topDualPairing`, `StrongDual.polar`, and
`LinearMap.polar`; no separate bipolar carrier is introduced. The separation argument
uses `RCLike.geometric_hahn_banach_closed_point` and rotates each value of a functional
by `RCLike.exists_norm_eq_mul_self` to pass from real-part bounds to absolute bounds.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.6 (the bipolar theorem).
* Christopher Hoskin, [Mathlib PR #26345](https://github.com/leanprover-community/mathlib4/pull/26345),
  for the formulation for bilinear pairings with their weak topology.
-/

public section

open Set Topology
open scoped ComplexOrder

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] [LocallyConvexSpace ℝ E]

namespace AbsConvex

/-- A point outside the closure of a nonempty absolutely convex set is separated by a
continuous linear functional whose absolute value is at most one on the set and
strictly greater than one at the point. -/
theorem exists_mem_polar_norm_apply_gt_one {s : Set E} (hs : AbsConvex 𝕜 s)
    (hne : s.Nonempty) {x : E} (hx : x ∉ _root_.closure s) :
    ∃ f ∈ StrongDual.polar 𝕜 s, 1 < ‖f x‖ := by
  have : ContinuousSMul ℝ E := IsScalarTower.continuousSMul 𝕜
  obtain ⟨f, u, hfu, hux⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
    (hs.2.lift ℝ).closure isClosed_closure hx
  have hu : 0 < u := by
    simpa using hfu 0 (subset_closure (hs.1.zero_mem hne))
  have hnorm (y : E) (hy : y ∈ s) : ‖f y‖ ≤ u := by
    obtain ⟨c, hc, heq⟩ := RCLike.exists_norm_eq_mul_self (f y)
    have h := hfu (c • y) (subset_closure (hs.1.smul_mem hc.le hy))
    simpa only [map_smul, smul_eq_mul, ← heq, RCLike.ofReal_re] using h.le
  refine ⟨(u⁻¹ : ℝ) • f, ?_, ?_⟩
  · rw [StrongDual.mem_polar_iff]
    intro y hy
    simpa only [smul_apply, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hu, ← div_eq_inv_mul, div_self hu.ne'] using
      (div_le_div_of_nonneg_right (hnorm y hy) hu.le)
  · have hlt : u < ‖f x‖ := hux.trans_le (RCLike.re_le_norm _)
    simpa only [smul_apply, norm_smul, Real.norm_eq_abs,
      abs_inv, abs_of_pos hu, ← div_eq_inv_mul] using (one_lt_div hu).mpr hlt

/-- **The bipolar theorem:** the bipolar of a nonempty absolutely convex set equals
its closure in the original locally convex topology. -/
theorem bipolar_eq_closure {s : Set E} (hs : AbsConvex 𝕜 s) (hne : s.Nonempty) :
    (topDualPairing 𝕜 E).polar (StrongDual.polar 𝕜 s) = _root_.closure s := by
  refine Subset.antisymm (fun x hx ↦ ?_) ?_
  · by_contra h
    obtain ⟨f, hf, hfx⟩ := hs.exists_mem_polar_norm_apply_gt_one hne h
    exact hfx.not_ge (hx f hf)
  · intro x hx f hf
    exact closure_minimal hf (isClosed_le f.continuous.norm continuous_const) hx

end AbsConvex

namespace StrongDual

variable (𝕜) in
/-- **The bipolar theorem for an arbitrary set.** Its bipolar is the closed absolutely
convex hull of the set together with zero, including when the set is empty. -/
theorem bipolar_eq_closedAbsConvexHull (s : Set E) :
    (topDualPairing 𝕜 E).polar (polar 𝕜 s) = closedAbsConvexHull 𝕜 (insert 0 s) := by
  have hpolar : polar 𝕜 (insert 0 s) = polar 𝕜 s := by
    ext f
    simp [mem_polar_iff]
  have hne : (closedAbsConvexHull 𝕜 (insert 0 s)).Nonempty :=
    ⟨0, subset_closedAbsConvexHull (mem_insert _ _)⟩
  have h := absConvex_convexClosedHull.bipolar_eq_closure (𝕜 := 𝕜) hne
  simpa only [polar_closedAbsConvexHull, hpolar, isClosed_closedAbsConvexHull.closure_eq]
    using h

/-- Membership in a closed absolutely convex hull is tested by continuous linear
functionals bounded by one on the original nonempty set. -/
theorem mem_closedAbsConvexHull_iff {s : Set E} (hne : s.Nonempty) {x : E} :
    x ∈ closedAbsConvexHull 𝕜 s ↔ ∀ f ∈ polar 𝕜 s, ‖f x‖ ≤ 1 := by
  have hzero : (0 : E) ∈ closedAbsConvexHull 𝕜 s :=
    absConvex_convexClosedHull.1.zero_mem (hne.mono subset_closedAbsConvexHull)
  have heq : closedAbsConvexHull 𝕜 (insert 0 s) = closedAbsConvexHull 𝕜 s :=
    (closedAbsConvexHull_min (insert_subset hzero subset_closedAbsConvexHull)
      absConvex_convexClosedHull isClosed_closedAbsConvexHull).antisymm
      ((closedAbsConvexHull 𝕜).monotone (subset_insert _ _))
  rw [← heq, ← bipolar_eq_closedAbsConvexHull 𝕜 s]
  rfl

end StrongDual
