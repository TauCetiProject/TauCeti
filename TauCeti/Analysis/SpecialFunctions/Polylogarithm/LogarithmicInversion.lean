/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Weight-one polylogarithm inversion

The principal weight-one polylogarithm satisfies
`Li₁(z) - Li₁(1/z) = -Log(-z)` outside the real segment `[0, 1]`.
This is the logarithmic base case for Bernoulli inversion in higher weight.
The identity holds on the real ray `(1, ∞)` with Mathlib's total principal values,
not just away from the real axis. On `(0, 1)` its defect is exactly `2πi`.
We compute that defect and characterize the domain of the uncorrected identity.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762,
  Astérisque 216 (1993), §1.3, (5), p. 51.
-/

public section

namespace TauCeti.Polylog

private theorem arg_one_sub_div_neg {z : ℂ} (hz₁ : z ≠ 1) :
    Complex.arg ((1 - z) / (-z)) =
      Complex.arg (1 - z) - Complex.arg (-z) +
        if z.im = 0 ∧ 0 < z.re ∧ z.re < 1 then 2 * Real.pi else 0 := by
  by_cases hz₀ : z = 0
  · subst z; simp
  rcases lt_trichotomy z.im 0 with him | him | him
  · rw [ite_eq_right (by grind), Complex.arg_div_of_im_pos (by simpa using him)
      (by simpa using him)]
    ring
  · have hzreal : z = (z.re : ℂ) := Complex.ext (by simp) (by simpa using him)
    have hr₀ : z.re ≠ 0 := by intro h; apply hz₀; rw [hzreal, h]; rfl
    have hr₁ : z.re ≠ 1 := by intro h; apply hz₁; rw [hzreal, h]; rfl
    -- Put each real-axis expression under one coercion to apply the real-argument lemmas.
    rw [hzreal, show (1 - (z.re : ℂ)) = ((1 - z.re : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_neg, ← Complex.ofReal_div]
    simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
    rcases lt_or_gt_of_ne hr₀ with hr | hr
    · have hquot : 0 ≤ (1 - z.re) / (-z.re) :=
        div_nonneg (by linarith) (by linarith)
      rw [ite_eq_right (by grind), Complex.arg_ofReal_of_nonneg hquot,
        Complex.arg_ofReal_of_nonneg (by linarith),
        Complex.arg_ofReal_of_nonneg (by linarith)]
      ring
    · rcases lt_or_gt_of_ne hr₁ with hr' | hr'
      · have hquot : (1 - z.re) / (-z.re) < 0 := div_neg_of_pos_of_neg (by linarith)
          (by linarith)
        rw [ite_eq_left ⟨hr, hr'⟩, Complex.arg_ofReal_of_neg hquot,
          Complex.arg_ofReal_of_nonneg (by linarith), Complex.arg_ofReal_of_neg (by linarith)]
        ring
      · have hquot : 0 ≤ (1 - z.re) / (-z.re) :=
          div_nonneg_of_nonpos (by linarith) (by linarith)
        rw [ite_eq_right (by grind), Complex.arg_ofReal_of_nonneg hquot,
          Complex.arg_ofReal_of_neg (by linarith), Complex.arg_ofReal_of_neg (by linarith)]
        ring
  · rw [ite_eq_right (by grind), Complex.arg_div_of_im_neg (by simpa using him)
      (by simpa using him)]
    ring

/-- The inversion defect in weight one is `2πi` precisely on the open real segment `(0, 1)`.
At zero the identity holds by totalisation; only the singular point `1` is excluded. -/
theorem polylog_one_sub_inv_eq (z : ℂ) (hz₁ : z ≠ 1) :
    polylog 1 z - polylog 1 z⁻¹ = -Complex.log (-z) +
      if z.im = 0 ∧ 0 < z.re ∧ z.re < 1 then 2 * Real.pi * Complex.I else 0 := by
  by_cases hz₀ : z = 0
  · subst z; simp
  have hquot : 1 - z⁻¹ = (1 - z) / (-z) := by field_simp; ring
  have hlog : Complex.log ((1 - z) / (-z)) =
      Complex.log (1 - z) - Complex.log (-z) +
        if z.im = 0 ∧ 0 < z.re ∧ z.re < 1 then 2 * Real.pi * Complex.I else 0 := by
    apply Complex.ext
    · simp only [Complex.log_re, Complex.add_re, Complex.sub_re, norm_div]
      rw [Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz₁.symm))
        (norm_ne_zero_iff.mpr (neg_ne_zero.mpr hz₀))]
      split_ifs <;> simp
    · have harg := arg_one_sub_div_neg hz₁
      split_ifs at harg ⊢ <;> simpa [Complex.log_im, Complex.mul_im, Complex.mul_re] using harg
  rw [polylog_one, polylog_one, hquot, hlog]
  ring

/-- Principal weight-one inversion off `(0, 1]`, including the lower values on `(1, ∞)`.
The extra point `0` satisfies the identity by totalisation, not by an analytic limit. -/
theorem polylog_one_inversion {z : ℂ}
    (hz : z.im ≠ 0 ∨ z.re ≤ 0 ∨ 1 < z.re) :
    polylog 1 z - polylog 1 z⁻¹ = -Complex.log (-z) := by
  have hz₁ : z ≠ 1 := by intro h; norm_num [h] at hz
  rw [polylog_one_sub_inv_eq z hz₁, ite_eq_right (by grind), add_zero]

/-- Away from `1`, the uncorrected inversion identity fails exactly on `(0, 1)`.
This detects the principal branch convention rather than merely equality of exponentials. -/
theorem polylog_one_inversion_iff {z : ℂ} (hz₁ : z ≠ 1) :
    polylog 1 z - polylog 1 z⁻¹ = -Complex.log (-z) ↔
      ¬ (z.im = 0 ∧ 0 < z.re ∧ z.re < 1) := by
  rw [polylog_one_sub_inv_eq z hz₁, add_eq_left]
  split_ifs with h
  · simp [h, mul_eq_zero, Real.pi_ne_zero]
  · simp [h]

end TauCeti.Polylog
