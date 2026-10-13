/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Hölder's inequality with Young's exponents

For `1 ≤ p ≤ q` and `1/p + 1/r = 1 + 1/q`, and functions `k g : β → ℝ≥0∞`,

`∫⁻ k g ≤ (∫⁻ k ^ r g ^ p) ^ (1/q) (∫⁻ k ^ r) ^ (1 - 1/p) (∫⁻ g ^ p) ^ (1/p - 1/q)`.

This is the pointwise step in the proof of Young's inequality for integral kernels,
`TauCeti.lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq`: integrating it in the remaining
variable and applying Tonelli's theorem gives the `Lᵖ → L^q` bound for the integral operator.

The statement is in `ℝ≥0∞`, so it needs no integrability hypotheses.

## Main declarations

* `TauCeti.lintegral_mul_le_of_inv_add_inv_eq`: the three-exponent Hölder inequality.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  proof of Proposition 6.36.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

variable {β : Type*} [MeasurableSpace β] {ν : Measure β}

/-- **Hölder's inequality for Young's exponents.** Let `1 ≤ p ≤ q` and let `r` be the exponent with
`1/p + 1/r = 1 + 1/q`. Then
`∫⁻ k g ≤ (∫⁻ k ^ r g ^ p) ^ (1/q) (∫⁻ k ^ r) ^ (1 - 1/p) (∫⁻ g ^ p) ^ (1/p - 1/q)`.

This is Hölder's inequality with the three exponents `1/q`, `1 - 1/p` and `1/p - 1/q`, which add
up to `1`, applied to the factorization
`k g = (k ^ r g ^ p) ^ (1/q) (k ^ r) ^ (1 - 1/p) (g ^ p) ^ (1/p - 1/q)`. -/
theorem lintegral_mul_le_of_inv_add_inv_eq {k g : β → ℝ≥0∞} (hk : AEMeasurable k ν)
    (hg : AEMeasurable g ν) {p q r : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (hr : p⁻¹ + r⁻¹ = 1 + q⁻¹) :
    ∫⁻ y, k y * g y ∂ν ≤ (∫⁻ y, k y ^ r * g y ^ p ∂ν) ^ q⁻¹ * (∫⁻ y, k y ^ r ∂ν) ^ (1 - p⁻¹) *
      (∫⁻ y, g y ^ p ∂ν) ^ (p⁻¹ - q⁻¹) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have ha : 0 ≤ q⁻¹ := inv_nonneg.2 hq0.le
  have hb : 0 ≤ 1 - p⁻¹ := sub_nonneg.2 (inv_le_one_of_one_le₀ hp)
  have hc : 0 ≤ p⁻¹ - q⁻¹ := sub_nonneg.2 (inv_anti₀ hp0 hpq)
  have hr0 : 0 < r := inv_pos.1 (by linarith [inv_pos.2 hq0])
  have hkr : r * q⁻¹ + r * (1 - p⁻¹) = 1 := by
    rw [← mul_add, show q⁻¹ + (1 - p⁻¹) = r⁻¹ by linarith, mul_inv_cancel₀ hr0.ne']
  have hgp : p * q⁻¹ + p * (p⁻¹ - q⁻¹) = 1 := by field_simp; ring
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := ν) Finset.univ
    (f := ![fun y => k y ^ r * g y ^ p, fun y => k y ^ r, fun y => g y ^ p])
    (p := ![q⁻¹, 1 - p⁻¹, p⁻¹ - q⁻¹])
    (fun i _ => by
      fin_cases i
      · exact (hk.pow_const r).mul (hg.pow_const p)
      · exact hk.pow_const r
      · exact hg.pow_const p)
    (by simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]; ring)
    (fun i _ => by fin_cases i <;> [exact ha; exact hb; exact hc])
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h
  refine le_trans (lintegral_mono fun y => le_of_eq ?_) h
  rw [ENNReal.mul_rpow_of_nonneg _ _ ha, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  calc k y * g y = k y ^ (r * q⁻¹ + r * (1 - p⁻¹)) * g y ^ (p * q⁻¹ + p * (p⁻¹ - q⁻¹)) := by
        rw [hkr, hgp, ENNReal.rpow_one, ENNReal.rpow_one]
    _ = _ := by
        rw [ENNReal.rpow_add_of_nonneg _ _ (by positivity) (mul_nonneg hr0.le hb),
          ENNReal.rpow_add_of_nonneg _ _ (by positivity) (mul_nonneg hp0.le hc)]
        ring

end TauCeti
