/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.SymmetricGauge.Basic

/-!
# The ℓᵖ symmetric gauges

For a finite real exponent `p ≥ 1`, the ℓᵖ norm on finitely supported nonnegative sequences
is a symmetric gauge. Its extension to arbitrary nonnegative extended-real sequences is
the `p`-th root of the sum of their `p`-th powers, including when the sum is infinite.
Applied to approximation numbers, these gauges construct the Schatten operator ideals.

## References

* B. Simon, *Trace Ideals and Their Applications*, second edition, AMS, 2005, Chapter 2.
-/

public section

open Finset
open scoped NNReal ENNReal

namespace TauCeti.SymmetricGauge

/-- The ℓᵖ norm of a finitely supported nonnegative sequence, as a symmetric gauge. -/
noncomputable def lpGauge (p : ℝ) (hp : 1 ≤ p) : SymmetricGauge where
  toFun a := (a.sum fun _ x ↦ x ^ p) ^ (1 / p)
  map_add_le' a b := by
    -- The triangle inequality reuses Mathlib's `NNReal.Lp_add_le`.
    classical
    have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
    rw [Finsupp.sum_of_support_subset _ Finsupp.support_add _ (by simp [hp0]),
      Finsupp.sum_of_support_subset _ subset_union_left _ (by simp [hp0]),
      Finsupp.sum_of_support_subset _ subset_union_right _ (by simp [hp0])]
    simpa using NNReal.Lp_add_le (a.support ∪ b.support) a b hp
  map_smul' c a := by
    have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
    rw [Finsupp.sum_smul_index (by simp [hp0])]
    simp only [NNReal.mul_rpow, Finsupp.sum, ← Finset.mul_sum]
    rw [NNReal.rpow_inv_rpow_self hp0]
  map_equivMapDomain' σ a := by rw [Finsupp.sum_equivMapDomain]
  monotone' a b hab := by
    apply NNReal.rpow_le_rpow _ (by positivity)
    exact Finsupp.sum_le_sum_index hab (fun _ _ ↦ fun _ _ h ↦
      NNReal.rpow_le_rpow h (zero_le_one.trans hp)) (by simp [(zero_lt_one.trans_le hp).ne'])
  map_single_zero_one' := by simp [(zero_lt_one.trans_le hp).ne']

/-- The defining finite power-sum formula for the ℓᵖ gauge. -/
@[simp]
theorem lpGauge_apply (p : ℝ) (hp : 1 ≤ p) (a : ℕ →₀ ℝ≥0) :
    lpGauge p hp a = (a.sum fun _ x ↦ x ^ p) ^ (1 / p) := (rfl)

private theorem extend_lpGauge_coe (p : ℝ) (hp : 1 ≤ p) (a : ℕ → ℝ≥0) :
    (lpGauge p hp).extend (fun n ↦ a n) = (∑' n, (a n : ℝ≥0∞) ^ p) ^ (1 / p) := by
  classical
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  have hsum (b : ℕ →₀ ℝ≥0) :
      (lpGauge p hp b : ℝ≥0∞) =
        (∑ n ∈ b.support, (b n : ℝ≥0∞) ^ p) ^ (1 / p) := by
    simp [Finsupp.sum, ENNReal.coe_rpow_of_nonneg, hp0.le]
  refine le_antisymm ((extend_le_iff _).mpr fun b hb ↦ ?_) ?_
  · rw [hsum]
    gcongr
    exact (Finset.sum_le_sum fun n _ ↦ ENNReal.rpow_le_rpow (hb n) hp0.le).trans
      (ENNReal.sum_le_tsum _)
  · rw [one_div, ENNReal.rpow_inv_le_iff hp0, ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N ↦ ?_
    have h := (lpGauge p hp).apply_le_extend
      (b := Finsupp.indicator (range N) fun n _ ↦ a n) (a := fun n ↦ a n) (by
        intro n
        rw [Finsupp.indicator_apply]
        split_ifs <;> simp)
    rw [hsum, one_div, ENNReal.rpow_inv_le_iff hp0] at h
    convert h using 1
    symm
    exact (Finsupp.sum_of_support_subset _ (Finsupp.support_indicator_subset _ _)
      (fun (_ : ℕ) (x : ℝ≥0) ↦ (x : ℝ≥0∞) ^ p) (by simp [hp0])).trans
      (Finset.sum_congr rfl fun n hn ↦ by simp [Finsupp.indicator_apply, hn])

/-- The extension of the ℓᵖ gauge is the `p`-th root of the sum of the `p`-th powers.
No finiteness or summability hypotheses are needed. -/
@[simp]
theorem extend_lpGauge (p : ℝ) (hp : 1 ≤ p) (a : ℕ → ℝ≥0∞) :
    (lpGauge p hp).extend a = (∑' n, a n ^ p) ^ (1 / p) := by
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  by_cases ha : ∃ n, a n = ⊤
  · obtain ⟨n, hn⟩ := ha
    have htop : (lpGauge p hp).extend a = ⊤ :=
      top_unique (hn ▸ (le_iSup a n).trans ((lpGauge p hp).iSup_le_extend a))
    have hsum : ∑' n, a n ^ p = ⊤ :=
      top_unique (by simpa [hn, hp0] using ENNReal.le_tsum n (f := fun k ↦ a k ^ p))
    rw [htop, hsum, ENNReal.top_rpow_of_pos (one_div_pos.mpr hp0)]
  · push Not at ha
    lift a to ℕ → ℝ≥0 using ha
    exact extend_lpGauge_coe p hp a

end TauCeti.SymmetricGauge
