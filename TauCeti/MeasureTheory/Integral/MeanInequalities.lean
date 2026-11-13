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
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Variants of Hölder's inequality

For `1 ≤ p ≤ q` and `1/p + 1/r = 1 + 1/q`, and functions `k g : β → ℝ≥0∞`,

`∫⁻ k g ≤ (∫⁻ k ^ r g ^ p) ^ (1/q) (∫⁻ k ^ r) ^ (1 - 1/p) (∫⁻ g ^ p) ^ (1/p - 1/q)`.

This is the pointwise step in the proof of Young's inequality for integral kernels,
`TauCeti.lintegral_rpow_lintegral_mul_le_of_inv_add_inv_eq`: integrating it in the remaining
variable and applying Tonelli's theorem gives the `Lᵖ → L^q` bound for the integral operator.

The statement is in `ℝ≥0∞`, so it needs no integrability hypotheses.

The file also records the weighted Young inequality for a pairing,
`∫ w ⟪G, η⟫ ≤ (δ / 2) ∫ w ‖η‖² + (2 δ)⁻¹ ∫ w ‖G‖²` for a nonnegative weight `w` and `δ > 0`,
which absorbs a pairing into a coercive term in energy estimates.

On a finite measure space, a weight `0 ≤ θ ≤ K` and a function with `‖g‖ ∈ L^{2q}` satisfy

`∫ θ² ‖g‖² ≤ (K^(2q' - 1) ∫ θ)^(1/q') (∫ ‖g‖^(2q))^(1/q)`

for Hölder conjugate exponents `q, q'`, so the weighted integral is small when the mean of `θ` is
small. This is how the mean oscillation of the coefficients enters regularity estimates for
divergence-form equations.

## Main declarations

* `TauCeti.lintegral_mul_le_of_inv_add_inv_eq`: the three-exponent Hölder inequality.
* `TauCeti.integral_mul_inner_le`: the weighted Young inequality for a pairing.
* `TauCeti.integral_sq_mul_norm_sq_le_of_ae_le`: Hölder's inequality with a bounded weight.

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

/-- **Hölder's inequality with a bounded weight.** On a finite measure space, let `θ` be a
measurable weight with `0 ≤ θ ≤ K` almost everywhere, and let `‖g‖ ∈ L^{2q}` for a pair of Hölder
conjugate exponents `q, q'`. Then
`∫ θ² ‖g‖² ≤ (K^(2q' - 1) ∫ θ)^(1/q') (∫ ‖g‖^(2q))^(1/q)`. -/
theorem integral_sq_mul_norm_sq_le_of_ae_le {E : Type*} [NormedAddCommGroup E]
    [IsFiniteMeasure ν] {θ : β → ℝ} {g : β → E} {K q q' : ℝ} (hq : q.HolderConjugate q')
    (hθm : AEStronglyMeasurable θ ν) (hθ : ∀ᵐ x ∂ν, 0 ≤ θ x ∧ θ x ≤ K)
    (hg : MemLp g (ENNReal.ofReal (2 * q)) ν) :
    ∫ x, θ x ^ 2 * ‖g x‖ ^ 2 ∂ν ≤
      (K ^ (2 * q' - 1) * ∫ x, θ x ∂ν) ^ q'⁻¹ * (∫ x, ‖g x‖ ^ (2 * q) ∂ν) ^ q⁻¹ := by
  have hθi : Integrable θ ν := Integrable.of_bound hθm K (hθ.mono fun x hx => by
    rw [Real.norm_of_nonneg hx.1]
    exact hx.2)
  -- Hölder's inequality with exponents `q'` and `q`.
  have hg2 : MemLp (fun x => ‖g x‖ ^ 2) (ENNReal.ofReal q) ν := by
    have h := hg.norm_rpow_div (ENNReal.ofReal 2)
    rw [← ENNReal.ofReal_div_of_pos two_pos, ENNReal.toReal_ofReal zero_le_two,
      show 2 * q / 2 = q by ring] at h
    simpa only [Real.rpow_two] using h
  have hθ2 : MemLp (fun x => θ x ^ 2) (ENNReal.ofReal q') ν :=
    MemLp.of_bound (hθm.pow 2) (K ^ 2) (hθ.mono fun x hx => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ hx.1 hx.2 2)
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg hq.symm
    (ae_of_all _ fun x => sq_nonneg (θ x)) (ae_of_all _ fun x => sq_nonneg ‖g x‖) hθ2 hg2
  -- Since `0 ≤ θ ≤ K`, `(θ²)^q' = θ^(2q' - 1) θ ≤ K^(2q' - 1) θ`.
  have hθq : ∫ x, (θ x ^ 2) ^ q' ∂ν ≤ K ^ (2 * q' - 1) * ∫ x, θ x ∂ν := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) (hθi.const_mul _)
      (hθ.mono fun x hx => ?_)
    have h1 : 0 < 2 * q' - 1 := by linarith [hq.symm.lt]
    calc (θ x ^ 2) ^ q' = θ x ^ (2 * q' - 1) * θ x := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hx.1, ← Real.rpow_add_one' hx.1 (by linarith)]
          norm_num
      _ ≤ K ^ (2 * q' - 1) * θ x :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx.1 hx.2 h1.le) hx.1
  have hgq : ∫ x, (‖g x‖ ^ 2) ^ q ∂ν = ∫ x, ‖g x‖ ^ (2 * q) ∂ν := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  refine hHolder.trans ?_
  rw [hgq, one_div, one_div]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (integral_nonneg fun x => by positivity)
    hθq hq.symm.inv_nonneg) (Real.rpow_nonneg (integral_nonneg fun x => by positivity) _)

end TauCeti
