/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Variants of Hölder's inequality

For `1 ≤ p ≤ q` and `1/p + 1/r = 1 + 1/q`, and functions `k g : β → ℝ≥0∞`,

`∫⁻ k g ≤ (∫⁻ k ^ r g ^ p) ^ (1/q) (∫⁻ k ^ r) ^ (1 - 1/p) (∫⁻ g ^ p) ^ (1/p - 1/q)`.

This is the pointwise step in the proof of Young's inequality for integral kernels,
`TauCeti.lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq`: integrating it in the remaining
variable and applying Tonelli's theorem gives the `Lᵖ → L^q` bound for the integral operator.

The statement is in `ℝ≥0∞`, so it needs no integrability hypotheses.

For a weight `0 ≤ w ≤ K` and Hölder conjugate exponents `p, q`, the bound `w ^ p ≤ K ^ (p - 1) w`
turns Hölder's inequality into
`∫ w g ≤ (K ^ (p - 1) ∫ w) ^ (1/p) (∫ g ^ q) ^ (1/q)` for `g ≥ 0`, which controls `∫ w g` by the
`L¹` norm of the weight. With `w` the deviation of a coefficient from a constant, this is how a
mean oscillation enters the error estimates of frozen-coefficient arguments.

The file also records the weighted Young inequality for a pairing,
`∫ w ⟪G, η⟫ ≤ (δ / 2) ∫ w ‖η‖² + (2 δ)⁻¹ ∫ w ‖G‖²` for a nonnegative weight `w` and `δ > 0`,
which absorbs a pairing into a coercive term in energy estimates.

## Main declarations

* `TauCeti.lintegral_mul_le_of_inv_add_inv_eq`: the three-exponent Hölder inequality.
* `TauCeti.integral_mul_le_L1_mul_Lq_of_le`: Hölder's inequality with a bounded weight.
* `TauCeti.integral_mul_inner_le`: the weighted Young inequality for a pairing.

## References

* G. B. Folland, *Real Analysis: Modern Techniques and Their Applications*, 2nd ed.,
  proof of Proposition 6.36.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal InnerProductSpace

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

/-- **Hölder's inequality with a bounded weight.** Let `p, q` be Hölder conjugate exponents, let
`w` be measurable with `0 ≤ w ≤ K` on a finite measure space and let `0 ≤ g ∈ L^q`. Then
`∫ w g ≤ (K ^ (p - 1) ∫ w) ^ (1/p) (∫ g ^ q) ^ (1/q)`: the `Lᵖ` norm of the weight in Hölder's
inequality is replaced by its `L¹` norm, since `w ^ p ≤ K ^ (p - 1) w`. -/
theorem integral_mul_le_L1_mul_Lq_of_le [IsFiniteMeasure ν] {p q K : ℝ}
    (hpq : p.HolderConjugate q) {w g : β → ℝ} (hwm : AEStronglyMeasurable w ν)
    (hw : ∀ᵐ x ∂ν, 0 ≤ w x ∧ w x ≤ K) (hg0 : 0 ≤ᵐ[ν] g) (hg : MemLp g (ENNReal.ofReal q) ν) :
    ∫ x, w x * g x ∂ν ≤ (K ^ (p - 1) * ∫ x, w x ∂ν) ^ p⁻¹ * (∫ x, g x ^ q ∂ν) ^ q⁻¹ := by
  have hwK : ∀ᵐ x ∂ν, ‖w x‖ ≤ K := hw.mono fun x hx => by rw [Real.norm_of_nonneg hx.1]; exact hx.2
  refine (integral_mul_le_Lp_mul_Lq_of_nonneg hpq (hw.mono fun x hx => hx.1) hg0
    (MemLp.of_bound hwm K hwK) hg).trans ?_
  rw [one_div, one_div]
  refine mul_le_mul_of_nonneg_right (Real.rpow_le_rpow
    (integral_nonneg_of_ae (hw.mono fun x hx => Real.rpow_nonneg hx.1 _)) ?_ hpq.inv_nonneg)
    (Real.rpow_nonneg (integral_nonneg_of_ae (hg0.mono fun x hx => Real.rpow_nonneg hx _)) _)
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (hw.mono fun x hx => Real.rpow_nonneg hx.1 _)
    ((memLp_one_iff_integrable.1 (MemLp.of_bound hwm K hwK)).const_mul _) (hw.mono fun x hx => ?_)
  -- `w ^ p = w ^ (p - 1) w ≤ K ^ (p - 1) w`.
  calc w x ^ p = w x ^ (p - 1) * w x := by
        rw [← Real.rpow_add_one' hx.1 (by linarith [hpq.lt]), sub_add_cancel]
    _ ≤ K ^ (p - 1) * w x :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx.1 hx.2 hpq.sub_one_pos.le) hx.1

/-- **Weighted Young inequality for a pairing.** For a nonnegative weight `w` and `δ > 0`,

`∫ w ⟪G, η⟫ ≤ (δ / 2) ∫ w ‖η‖² + (2 δ)⁻¹ ∫ w ‖G‖²`,

provided the two integrals on the right exist. -/
theorem integral_mul_inner_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {w : β → ℝ} {G η : β → F} (hw : ∀ z, 0 ≤ w z)
    (hη : Integrable (fun z ↦ w z * ‖η z‖ ^ 2) ν) (hG : Integrable (fun z ↦ w z * ‖G z‖ ^ 2) ν)
    {δ : ℝ} (hδ : 0 < δ) :
    ∫ z, w z * ⟪G z, η z⟫_ℝ ∂ν ≤
      δ / 2 * (∫ z, w z * ‖η z‖ ^ 2 ∂ν) + 1 / (2 * δ) * ∫ z, w z * ‖G z‖ ^ 2 ∂ν := by
  have i₁ := hη.const_mul (δ / 2)
  have i₂ := hG.const_mul (1 / (2 * δ))
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add i₁ i₂]
  by_cases hi : Integrable (fun z ↦ w z * ⟪G z, η z⟫_ℝ) ν
  · refine integral_mono hi (i₁.add i₂) fun z ↦ ?_
    have h := real_inner_le_norm (G z) (η z)
    have hq : ‖G z‖ * ‖η z‖ ≤ δ / 2 * ‖η z‖ ^ 2 + 1 / (2 * δ) * ‖G z‖ ^ 2 := by
      have e : δ / 2 * ‖η z‖ ^ 2 + 1 / (2 * δ) * ‖G z‖ ^ 2 =
          (δ ^ 2 * ‖η z‖ ^ 2 + ‖G z‖ ^ 2) / (2 * δ) := by
        field_simp
      rw [e, le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (δ * ‖η z‖ - ‖G z‖)]
    have := mul_le_mul_of_nonneg_left (h.trans hq) (hw z)
    linarith
  · rw [integral_undef hi]
    exact integral_nonneg fun z ↦ by
      have := hw z
      positivity

end TauCeti
