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
`t • closure s`, which is the closure of the dilate `t • s`
(`setOfPred_gauge_le_eq_closure_smul_of_pos`); for bounded `s` in a `T1Space` the set form also
holds at `t = 0` (`setOfPred_gauge_le_eq_closure_smul`). For a convex body, which is closed, this
turns bounds on the gauge into membership in a dilate of the body
(`ConvexBody.gauge_le_iff_mem_smul`), which is how successive minima are stated. For such a body,
the gauge is also positive away from `0` (`ConvexBody.gauge_pos_iff`). The gauge of the preimage
of a set under a linear map is the gauge of the set at the image point
(`LinearMap.gauge_preimage`).

The two set forms `setOfPred_gauge_le_eq_closure_smul_of_pos` and
`setOfPred_gauge_le_eq_closure_smul` follow Mathlib's successive-minima proposal (mathlib4 PR
35812 by Alex J. Best, Yaël Dillies and Kevin H. Wilson, file `Mathlib/Analysis/Convex/Gauge.lean`
at revision `8423d1c`), with `setOfPred` in place of its `setOf` after Mathlib's renaming.
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

/-- For a convex neighbourhood `s` of `0` and `0 < t`, the gauge sublevel set
`{x | gauge s x ≤ t}` is the closure of the dilate `t • s`. See
`setOfPred_gauge_le_eq_closure_smul` for `t = 0`, for bounded `s` in a `T1Space`. -/
theorem setOfPred_gauge_le_eq_closure_smul_of_pos (hc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0)
    (ht : 0 < t) : {x | gauge s x ≤ t} = closure (t • s) := by
  ext x
  rw [Set.mem_ofPred_eq, gauge_le_iff_mem_smul_closure hc hs₀ ht, closure_smul₀' ht.ne']

/-- For a bounded convex neighbourhood `s` of `0` in a `T1Space` and `0 ≤ t`, the gauge sublevel
set `{x | gauge s x ≤ t}` is the closure of the dilate `t • s`. At `t = 0` both sides are `{0}`. -/
theorem setOfPred_gauge_le_eq_closure_smul [T1Space E] (hc : Convex ℝ s)
    (hb : Bornology.IsVonNBounded ℝ s) (hs₀ : s ∈ 𝓝 0) (ht : 0 ≤ t) :
    {x | gauge s x ≤ t} = closure (t • s) := by
  obtain rfl | ht := ht.eq_or_lt
  · ext x
    rw [Set.mem_ofPred_eq, Set.zero_smul_set (Set.nonempty_of_mem (mem_of_mem_nhds hs₀)),
      ← Set.singleton_zero, closure_singleton, Set.mem_singleton_iff,
      ← gauge_eq_zero (absorbent_nhds_zero hs₀) hb]
    exact ⟨fun h ↦ h.antisymm (gauge_nonneg x), le_of_eq⟩
  · exact setOfPred_gauge_le_eq_closure_smul_of_pos hc hs₀ ht

end TopologicalVectorSpace

/-- The gauge of the preimage of `s` under a linear map `f` is the gauge of `s` at `f x`. -/
theorem LinearMap.gauge_preimage {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F]
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
