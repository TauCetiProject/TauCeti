/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Body
public import Mathlib.Analysis.Convex.Gauge

/-!
# Sublevel sets of the gauge as dilates

For a convex neighbourhood `s` of `0` in a real topological vector space, Mathlib's
`gauge_le_one_iff_mem_closure` identifies the sublevel set `{x | gauge s x ≤ 1}` with the closure
of `s`. This file records the dilated form: for `0 < t`, the sublevel set `{x | gauge s x ≤ t}` is
`t • closure s`. For a convex body, which is closed, this turns bounds on the gauge into
membership in a dilate of the body (`ConvexBody.gauge_le_iff_mem_smul`), which is how successive
minima are stated. For such a body, the gauge is also positive away from `0`
(`ConvexBody.gauge_pos_iff`). The gauge of the preimage of a set under a linear map is the gauge
of the set at the image point (`gauge_preimage_linearMap`).
-/

public section

open scoped Pointwise Topology

section TopologicalVectorSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] {s : Set E} {t : ℝ} {x : E}

/-- For a convex neighbourhood `s` of `0` and `0 < t`, the gauge of `x` is at most `t` exactly when
`x` lies in the dilate `t • closure s`. -/
theorem gauge_le_iff_mem_smul_closure (hc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) (ht : 0 < t) :
    gauge s x ≤ t ↔ x ∈ t • closure s := by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne', ← gauge_le_one_iff_mem_closure hc hs₀,
    gauge_smul_of_nonneg (inv_nonneg.2 ht.le), smul_eq_mul, inv_mul_le_iff₀ ht, mul_one]

end TopologicalVectorSpace

/-- The gauge of the preimage of `s` under a linear map `f` is the gauge of `s` at `f x`. -/
theorem gauge_preimage_linearMap {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
    [Module ℝ F] (f : E →ₗ[ℝ] F) (s : Set F) (x : E) : gauge (f ⁻¹' s) x = gauge s (f x) := by
  simp only [gauge_def', Set.mem_preimage, map_smul]

/-- For a convex body `K` with `0` in its interior and `0 < t`, the gauge of `x` is at most `t`
exactly when `x` lies in the dilate `t • K`. -/
theorem ConvexBody.gauge_le_iff_mem_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : ConvexBody E} (hK : 0 ∈ interior (K : Set E)) {t : ℝ} (ht : 0 < t) {x : E} :
    gauge (K : Set E) x ≤ t ↔ x ∈ t • (K : Set E) := by
  rw [gauge_le_iff_mem_smul_closure K.convex (mem_interior_iff_mem_nhds.1 hK) ht,
    K.isClosed.closure_eq]

/-- For a convex body `K` with `0` in its interior, the gauge of `x` is positive exactly when
`x ≠ 0`. -/
theorem ConvexBody.gauge_pos_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : ConvexBody E} (hK : 0 ∈ interior (K : Set E)) {x : E} :
    0 < gauge (K : Set E) x ↔ x ≠ 0 :=
  gauge_pos (absorbent_nhds_zero (mem_interior_iff_mem_nhds.1 hK))
    ((NormedSpace.isVonNBounded_iff ℝ).2 K.isBounded)
