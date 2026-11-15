/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Lipschitz real functions

Basic Lipschitz-continuity lemmas for real-valued operations: the shifted positive part
`t ↦ max (t - k) 0` on `ℝ`, and pointwise infima `x ↦ sInf ((F x) '' S)` of uniformly `K`-Lipschitz
families bounded below at each point.

## Main results

* `TauCeti.lipschitzWith_max_sub_const_zero`: the shifted positive part is `1`-Lipschitz.
* `TauCeti.lipschitzWith_sInf_image`: pointwise infimum over an index set `S` preserves a uniform
  Lipschitz constant `K` when each slice `(F x) '' S` is bounded below.

## References

* H. Federer, *Geometric Measure Theory*, Springer (1969), Section 2.2.7.
-/

public section

namespace TauCeti

/-- The shifted positive part `t ↦ max (t - k) 0` is `1`-Lipschitz on the real line. -/
theorem lipschitzWith_max_sub_const_zero (k : ℝ) : LipschitzWith 1 (fun t : ℝ => max (t - k) 0) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, sub_sub_sub_cancel_right] using
      abs_max_sub_max_le_abs (x - k) (y - k) 0

/-- Pointwise infimum over an index set `S` preserves a uniform Lipschitz constant `K` when each
slice `(F x) '' S` is bounded below. -/
theorem lipschitzWith_sInf_image {α ι : Type*} [PseudoMetricSpace α] {S : Set ι} {F : α → ι → ℝ}
    {K : NNReal} (hbdd : ∀ x, BddBelow ((F x) '' S))
    (hlip : ∀ i ∈ S, LipschitzWith K (fun x ↦ F x i)) :
    LipschitzWith K (fun x ↦ sInf ((F x) '' S)) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.dist_eq]
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp only [Set.image_empty, Real.sInf_empty, sub_self, abs_zero]
    positivity
  · have hle (u v : α) : sInf ((F u) '' S) - (K : ℝ) * dist u v ≤ sInf ((F v) '' S) := by
      refine le_csInf (hS.image _) ?_
      rintro _ ⟨i, hi, rfl⟩
      have hdist : F u i - F v i ≤ (K : ℝ) * dist u v :=
        (le_abs_self _).trans (by simpa only [Real.dist_eq] using (hlip i hi).dist_le_mul u v)
      have hmin : sInf ((F u) '' S) ≤ F u i := csInf_le (hbdd u) ⟨i, hi, rfl⟩
      linarith
    rw [abs_sub_le_iff]
    refine ⟨by linarith [hle x y], ?_⟩
    have := hle y x
    rw [dist_comm] at this
    linarith

end TauCeti
