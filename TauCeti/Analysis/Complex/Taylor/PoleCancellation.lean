/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import TauCeti.Analysis.Normed.Field.Lipschitz
import TauCeti.Analysis.Normed.Ring.ProdSubProd

/-!
# Cancellation of nearby simple fractions

Compare the Taylor coefficients of a simple fraction at `1` with those from one real zero in a
local divisor disc. When the zero misses the disc, a geometric bound for the pole alone replaces
the bound for their difference. This is the scalar estimate in the Deuring–Heilbronn argument.
-/

public section

open Metric

namespace Complex

open Classical in
/-- The difference of the reciprocal powers for a pole at `1` and a real zero `β` is small when
the zero is in the local disc. Outside the disc the coefficient of the pole alone is small. -/
theorem norm_inv_pow_one_sub_cutoff_inv_pow_le {z : ℂ} (hz : 2 ≤ z.re) {β : ℝ}
    (hβ : β ∈ Set.Icc 0 1) (j : ℕ) :
    ‖((z - 1) ^ j)⁻¹ - (if (β : ℂ) ∈ closedBall z 3 then ((z - β) ^ j)⁻¹ else 0)‖ ≤
      if (β : ℂ) ∈ closedBall z 3 then (j : ℝ) * (1 - β) else (2⁻¹ : ℝ) ^ j := by
  have hp : 1 ≤ ‖z - 1‖ := by
    have h := re_le_norm (z - 1)
    simp only [sub_re, one_re] at h
    linarith
  have hgap : ‖(1 : ℂ) - β‖ = 1 - β := by
    rw [← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hβ.2)]
  by_cases hmem : (β : ℂ) ∈ closedBall z 3
  · have hzero : 1 ≤ ‖z - β‖ := by
      have h := re_le_norm (z - (β : ℂ))
      simp only [sub_re, ofReal_re] at h
      linarith [hβ.2]
    have hdiff : ‖(z - 1) - (z - (β : ℂ))‖ = 1 - β := by
      rw [sub_sub_sub_cancel_left, norm_sub_rev, hgap]
    have hinv (w : ℂ) (hw : 1 ≤ ‖w‖) : ‖w⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      simpa only [inv_one] using inv_anti₀ zero_lt_one hw
    have hpow : ‖(z - 1)⁻¹ ^ j - (z - β)⁻¹ ^ j‖ ≤ (j : ℝ) * ‖(z - 1)⁻¹ - (z - β)⁻¹‖ := by
      simpa using TauCeti.norm_prod_sub_prod_le_sum_norm_sub (Finset.range j)
        (a := fun _ ↦ (z - 1)⁻¹) (b := fun _ ↦ (z - β)⁻¹)
        (fun _ _ ↦ hinv _ hp) (fun _ _ ↦ hinv _ hzero)
    have hdist : ‖(z - 1)⁻¹ - (z - β)⁻¹‖ ≤ 1 - β := by
      rw [← hdiff]
      simpa only [one_pow, one_div] using
        TauCeti.norm_sq_div_sub_sq_div_le (c := (1 : ℂ))
          (by simpa using hp) (by simpa using hzero)
    simpa only [ite_eq_left hmem, ← inv_pow] using
      hpow.trans (mul_le_mul_of_nonneg_left hdist (Nat.cast_nonneg j))
  · have hfar : 3 < ‖z - β‖ := by
      simpa only [mem_closedBall_iff_norm', not_le] using hmem
    have htri := norm_sub_le_norm_sub_add_norm_sub z (1 : ℂ) (β : ℂ)
    have hp' : 2 ≤ ‖z - 1‖ := by linarith [hβ.1]
    simp only [ite_eq_right hmem, sub_zero, ← inv_pow, norm_pow, norm_inv]
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ (by norm_num) hp') j

end Complex
