/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Basic.Real.ConjExponents
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
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

For conjugate exponents `p'` and `p` and `(γ - 1) p' = q`, Hölder's inequality also bounds
`∫⁻ w ^ (γ - 1) ‖g‖ₑ` by `(∫⁻ w ^ q) ^ (1/p') ‖g‖_{Lᵖ}`. This is the step of Maz'ya's truncation
method that bounds the gradient of a power `w ^ γ` of a truncation through the `Lᵖ` norm of the
gradient of the original function.

## Main declarations

* `TauCeti.lintegral_mul_le_of_inv_add_inv_eq`: the three-exponent Hölder inequality.
* `TauCeti.lintegral_ofReal_rpow_mul_enorm_le`: Hölder's inequality for `w ^ (γ - 1) ‖g‖ₑ`.

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
`∫⁻ k g ≤ (∫⁻ k ^ r g ^ p) ^ (1/q) (∫⁻ k ^ r) ^ (1 - 1/p) (∫⁻ g ^ p) ^ (1/p - 1/q)`. -/
theorem lintegral_mul_le_of_inv_add_inv_eq {k g : β → ℝ≥0∞} (hk : AEMeasurable k ν)
    (hg : AEMeasurable g ν) {p q r : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (hr : p⁻¹ + r⁻¹ = 1 + q⁻¹) :
    ∫⁻ y, k y * g y ∂ν ≤ (∫⁻ y, k y ^ r * g y ^ p ∂ν) ^ q⁻¹ * (∫⁻ y, k y ^ r ∂ν) ^ (1 - p⁻¹) *
      (∫⁻ y, g y ^ p ∂ν) ^ (p⁻¹ - q⁻¹) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have ha : 0 ≤ q⁻¹ := by positivity
  have hb : 0 ≤ 1 - p⁻¹ := sub_nonneg.2 (inv_le_one_of_one_le₀ hp)
  have hc : 0 ≤ p⁻¹ - q⁻¹ := sub_nonneg.2 (inv_anti₀ hp0 hpq)
  have hr0 : 0 < r := inv_pos.1 (by linarith [inv_pos.2 hq0])
  have hr' : q⁻¹ + (1 - p⁻¹) = r⁻¹ := by linarith
  have hkr : r * (q⁻¹ + (1 - p⁻¹)) = 1 := by rw [hr', mul_inv_cancel₀ hr0.ne']
  have hgp : p * (q⁻¹ + (p⁻¹ - q⁻¹)) = 1 := by rw [add_sub_cancel, mul_inv_cancel₀ hp0.ne']
  -- Hölder's inequality with the three exponents `1/q`, `1 - 1/p` and `1/p - 1/q`, which add up
  -- to `1`, applied to the factorization
  -- `k g = (k ^ r g ^ p) ^ (1/q) (k ^ r) ^ (1 - 1/p) (g ^ p) ^ (1/p - 1/q)`.
  have h := ENNReal.lintegral_prod_norm_pow_le (μ := ν) Finset.univ
    (f := ![fun y => k y ^ r * g y ^ p, fun y => k y ^ r, fun y => g y ^ p])
    (p := ![q⁻¹, 1 - p⁻¹, p⁻¹ - q⁻¹])
    (fun i _ => by
      fin_cases i
      · exact (hk.pow_const r).mul (hg.pow_const p)
      · exact hk.pow_const r
      · exact hg.pow_const p)
    (by simp [Fin.sum_univ_three]; ring)
    (fun i _ => by fin_cases i <;> [exact ha; exact hb; exact hc])
  simp only [Fin.prod_univ_three, Matrix.cons_val] at h
  refine le_trans (lintegral_mono fun y => le_of_eq ?_) h
  -- The pointwise factorization: expand the powers, split the exponents of `k y` and `g y`
  -- with `hkr` and `hgp`, and regroup.
  rw [ENNReal.mul_rpow_of_nonneg _ _ ha, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  calc k y * g y = k y ^ (r * (q⁻¹ + (1 - p⁻¹))) * g y ^ (p * (q⁻¹ + (p⁻¹ - q⁻¹))) := by
        rw [hkr, hgp, ENNReal.rpow_one, ENNReal.rpow_one]
    _ = _ := by
        rw [mul_add, mul_add,
          ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hr0.le ha) (mul_nonneg hr0.le hb),
          ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg hp0.le ha) (mul_nonneg hp0.le hc)]
        ring

/-- **Hölder's inequality for a power times a norm.** If `p'` and `p` are conjugate exponents and
`(γ - 1) p' = q`, then `∫⁻ w ^ (γ - 1) ‖g‖ₑ ≤ (∫⁻ w ^ q) ^ (1/p') ‖g‖_{Lᵖ}`. -/
theorem lintegral_ofReal_rpow_mul_enorm_le {F : Type*} [NormedAddCommGroup F] {w : β → ℝ}
    {g : β → F} (hw : AEMeasurable w ν) (hg : AEStronglyMeasurable g ν) {p : ℝ≥0∞} {γ p' q : ℝ}
    (hconj : p'.HolderConjugate p.toReal) (hγp' : (γ - 1) * p' = q) :
    ∫⁻ x, ENNReal.ofReal (w x) ^ (γ - 1) * ‖g x‖ₑ ∂ν ≤
      (∫⁻ x, ENNReal.ofReal (w x) ^ q ∂ν) ^ p'⁻¹ * eLpNorm g p ν := by
  have hp : 0 < p.toReal := zero_lt_one.trans hconj.symm.lt
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hconj
    (f := fun x => ENNReal.ofReal (w x) ^ (γ - 1)) (g := fun x => ‖g x‖ₑ)
    ((ENNReal.measurable_ofReal.comp_aemeasurable hw).pow_const _) hg.enorm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.toReal_pos_iff.1 hp).1.ne'
    (ENNReal.toReal_pos_iff.1 hp).2.ne hg]
  refine h.trans_eq ?_
  simp_rw [← ENNReal.rpow_mul, hγp', one_div]

end TauCeti
