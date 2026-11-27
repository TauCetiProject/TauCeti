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
public import Mathlib.Basic.Real.ConjExponents
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Average
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.MeanInequalities
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Variants of Hölder's inequality

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

The file also records the weighted Young inequality for a pairing,
`∫ w ⟪G, η⟫ ≤ (δ / 2) ∫ w ‖η‖² + (2 δ)⁻¹ ∫ w ‖G‖²` for a nonnegative weight `w` and `δ > 0`,
which absorbs a pairing into a coercive term in energy estimates. Absorbing it into a weighted
coercivity estimate `δ ∫ w ‖η‖² ≤ ∫ w ⟪G, η⟫` bounds `∫ w ‖η‖²` by `δ⁻² ∫ w ‖G‖²`.

On a finite measure space, a weight `0 ≤ θ ≤ K` and a function with `‖g‖ ∈ L^{γq}`, `γ ≥ 1`,
satisfy

`∫ θ^γ ‖g‖^γ ≤ (K^(γq' - 1) ∫ θ)^(1/q') (∫ ‖g‖^(γq))^(1/q)`

for Hölder conjugate exponents `q, q'`, and the same holds for averages over a set of finite
measure, so the weighted integral is small when the mean of `θ` is
small. This is how the mean oscillation of the coefficients enters regularity estimates for
divergence-form equations. Combined with a volume ratio `|t| = δ^N |s|`, it turns a decay estimate
for integrals over `t ⊆ s` with such a weighted error into the same estimate for averages.

For a product of `k` functions, the norm of its integral is at most the average of their `k`th
absolute moments. This form of the arithmetic-geometric mean inequality gives uniform bounds on
expected products without any independence assumption.

## Main declarations

* `TauCeti.lintegral_mul_le_of_inv_add_inv_eq`: the three-exponent Hölder inequality.
* `TauCeti.lintegral_mul_le_rpow_mul_eLpNorm`: uniform `1 < p ≤ ∞` Hölder bound
  `∫⁻ k g ≤ (∫⁻ k ^ (1 - 1/p)⁻¹) ^ (1 - 1/p) * ‖g‖_p`.
* `TauCeti.lintegral_ofReal_rpow_mul_eNorm_le`: Hölder's inequality for `w ^ (γ - 1) ‖g‖ₑ`.
* `TauCeti.integral_mul_inner_le`: the weighted Young inequality for a pairing.
* `TauCeti.integral_mul_norm_sq_le_of_mul_le_integral_mul_inner` and
  `TauCeti.integral_mul_norm_sq_le_of_mul_le_integral_mul_inner_of_le`: weighted coercivity
  `δ ∫ w ‖η‖² ≤ ∫ w ⟪G, η⟫` bounds `∫ w ‖η‖²` by `δ⁻² ∫ w ‖G‖²`, also after changing to a
  comparable weight (`TauCeti.integral_mul_norm_sq_le_mul_of_le`).
* `TauCeti.integral_rpow_mul_norm_rpow_le_of_ae_le`: Hölder's inequality with a bounded weight,
  for a power `γ ≥ 1`; `TauCeti.integral_sq_mul_norm_sq_le_of_ae_le` is the case `γ = 2`.
* `TauCeti.setAverage_rpow_mul_norm_rpow_le_of_ae_le`: the same inequality for averages.
* `TauCeti.setAverage_le_of_setIntegral_le_add_sq_mul_norm_sq`: the averaged form of a decay
  estimate whose error is controlled by Hölder's inequality with a bounded weight.
* `TauCeti.setIntegral_norm_rpow_le_of_ae_norm_le`: the power-mean inequality
  `∫_s ‖φ‖^γ ≤ 2^(γ - 1) (∫_s ‖ψ‖^γ + ∫_s ‖χ‖^γ)` when `‖φ‖ ≤ ‖ψ‖ + ‖χ‖`, `γ ≥ 1`.
* `MeasureTheory.norm_integral_prod_le_inv_card_mul_sum_integral_norm_pow`:
  the absolute-moment bound for an integral of a finite product.

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

/-- **Hölder's inequality against an `eLpNorm` factor.** For `1 < p ≤ ∞` (with `1/∞` read as `0`),
`∫⁻ y, k y * g y ∂ν ≤ (∫⁻ y, k y ^ (1 - 1/p)⁻¹ ∂ν) ^ (1 - 1/p) * ‖g‖_p`. -/
theorem lintegral_mul_le_rpow_mul_eLpNorm {k g : β → ℝ≥0∞} (hk : AEMeasurable k ν)
    {p : ℝ≥0∞} (hp : 1 < p) :
    ∫⁻ y, k y * g y ∂ν ≤
      (∫⁻ y, k y ^ (1 - p.toReal⁻¹)⁻¹ ∂ν) ^ (1 - p.toReal⁻¹) * eLpNorm g p ν := by
  have : ENNReal.HolderTriple (1 - p⁻¹)⁻¹ p 1 :=
    (ENNReal.HolderConjugate.inv_one_sub_inv' hp.le).symm
  have hp_inv_lt : p⁻¹ < 1 := ENNReal.inv_lt_one.2 hp
  have hsub_pos : 0 < 1 - p⁻¹ := tsub_pos_of_lt hp_inv_lt
  have hq0 : (1 - p⁻¹)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (ENNReal.sub_ne_top ENNReal.one_ne_top)
  have hq_top : (1 - p⁻¹)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hsub_pos.ne'
  have htoReal : ((1 - p⁻¹)⁻¹).toReal = (1 - p.toReal⁻¹)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_sub_of_le hp_inv_lt.le ENNReal.one_ne_top,
      ENNReal.toReal_one, ENNReal.toReal_inv]
  calc ∫⁻ y, k y * g y ∂ν
      ≤ eLpNorm (k * g) 1 ν := by
        simpa only [Pi.mul_apply, eNorm_eq_self] using
          lintegral_eNorm_le_eLpNorm_one (f := k * g) (μ := ν)
    _ ≤ eLpNorm k (1 - p⁻¹)⁻¹ ν * eLpNorm g p ν :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_ennreal_of_pos one_pos
    _ = (∫⁻ y, k y ^ (1 - p.toReal⁻¹)⁻¹ ∂ν) ^ (1 - p.toReal⁻¹) * eLpNorm g p ν := by
        rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hq_top hk.aestronglyMeasurable, htoReal,
          one_div, inv_inv]
        simp only [eNorm_eq_self]

/-- **Hölder's inequality for a power times a norm.** If `p'` and `p` are conjugate exponents and
`(γ - 1) p' = q`, then `∫⁻ w ^ (γ - 1) ‖g‖ₑ ≤ (∫⁻ w ^ q) ^ (1/p') ‖g‖_{Lᵖ}`. -/
theorem lintegral_ofReal_rpow_mul_eNorm_le {F : Type*} [NormedAddCommGroup F] {w : β → ℝ}
    {g : β → F} (hw : AEMeasurable w ν) (hg : AEStronglyMeasurable g ν) {p : ℝ≥0∞} {γ p' q : ℝ}
    (hconj : p'.HolderConjugate p.toReal) (hγp' : (γ - 1) * p' = q) :
    ∫⁻ x, ENNReal.ofReal (w x) ^ (γ - 1) * ‖g x‖ₑ ∂ν ≤
      (∫⁻ x, ENNReal.ofReal (w x) ^ q ∂ν) ^ p'⁻¹ * eLpNorm g p ν := by
  have hp : 0 < p.toReal := zero_lt_one.trans hconj.symm.lt
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hconj
    (f := fun x => ENNReal.ofReal (w x) ^ (γ - 1)) (g := fun x => ‖g x‖ₑ)
    ((ENNReal.measurable_ofReal.comp_aemeasurable hw).pow_const _) hg.eNorm
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (ENNReal.toReal_pos_iff.1 hp).1.ne'
    (ENNReal.toReal_pos_iff.1 hp).2.ne hg]
  refine h.trans_eq ?_
  simp_rw [← ENNReal.rpow_mul, hγp', one_div]

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

/-- **Comparing weighted `L²` integrals.** A pointwise comparison `w ≤ E W` of the nonnegative
weight `w` with `W` integrates against `‖g‖²`: `∫ w ‖g‖² ≤ E ∫ W ‖g‖²`, provided the integral on
the right exists. -/
theorem integral_mul_norm_sq_le_mul_of_le {F : Type*} [NormedAddCommGroup F] {w W : β → ℝ}
    {g : β → F} {E : ℝ} (hw : ∀ z, 0 ≤ w z) (hwW : ∀ z, w z ≤ E * W z)
    (hW : Integrable (fun z ↦ W z * ‖g z‖ ^ 2) ν) :
    ∫ z, w z * ‖g z‖ ^ 2 ∂ν ≤ E * ∫ z, W z * ‖g z‖ ^ 2 ∂ν := by
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun z ↦ mul_nonneg (hw z) (sq_nonneg _))
    (hW.const_mul E) (ae_of_all _ fun z ↦ ?_)
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hwW z) (sq_nonneg ‖g z‖)

/-- **Coercivity bounds a weighted norm.** For a nonnegative weight `w` and `δ > 0`, the weighted
coercivity `δ ∫ w ‖η‖² ≤ ∫ w ⟪G, η⟫` gives `∫ w ‖η‖² ≤ δ⁻² ∫ w ‖G‖²`, provided the integrals of
`w ‖η‖²` and `w ‖G‖²` exist. -/
theorem integral_mul_norm_sq_le_of_mul_le_integral_mul_inner {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] {w : β → ℝ} {G η : β → F} (hw : ∀ z, 0 ≤ w z)
    (hη : Integrable (fun z ↦ w z * ‖η z‖ ^ 2) ν) (hG : Integrable (fun z ↦ w z * ‖G z‖ ^ 2) ν)
    {δ : ℝ} (hδ : 0 < δ) (h : δ * (∫ z, w z * ‖η z‖ ^ 2 ∂ν) ≤ ∫ z, w z * ⟪G z, η z⟫_ℝ ∂ν) :
    ∫ z, w z * ‖η z‖ ^ 2 ∂ν ≤ 1 / δ ^ 2 * ∫ z, w z * ‖G z‖ ^ 2 ∂ν := by
  have hP := integral_mul_inner_le hw hη hG hδ
  -- `δ I ≤ δ I / 2 + J / (2 δ)`, so `δ² I ≤ J`.
  have h₁ : δ / 2 * ∫ z, w z * ‖η z‖ ^ 2 ∂ν ≤ 1 / (2 * δ) * ∫ z, w z * ‖G z‖ ^ 2 ∂ν := by
    linarith [h.trans hP]
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  calc (∫ z, w z * ‖η z‖ ^ 2 ∂ν) * δ ^ 2 = 2 * δ * (δ / 2 * ∫ z, w z * ‖η z‖ ^ 2 ∂ν) := by ring
    _ ≤ 2 * δ * (1 / (2 * δ) * ∫ z, w z * ‖G z‖ ^ 2 ∂ν) := by gcongr
    _ = ∫ z, w z * ‖G z‖ ^ 2 ∂ν := by field_simp

/-- **Coercivity with a comparable weight.** If the nonnegative weights satisfy `w ≤ E W` and
`W ≤ E w`, then the weighted coercivity `δ ∫ W ‖η‖² ≤ ∫ W ⟪G, η⟫` with `δ > 0` gives
`∫ w ‖η‖² ≤ E² / δ² ∫ w ‖G‖²`. This transfers an estimate proved with a convenient weight `W`,
such as a smoothing of `w`, to the weight `w`. -/
theorem integral_mul_norm_sq_le_of_mul_le_integral_mul_inner_of_le {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] {w W : β → ℝ} {G η : β → F} {δ E : ℝ}
    (hδ : 0 < δ) (hE : 0 ≤ E) (hw : ∀ z, 0 ≤ w z) (hW : ∀ z, 0 ≤ W z)
    (hwW : ∀ z, w z ≤ E * W z) (hWw : ∀ z, W z ≤ E * w z)
    (hWη : Integrable (fun z ↦ W z * ‖η z‖ ^ 2) ν) (hWG : Integrable (fun z ↦ W z * ‖G z‖ ^ 2) ν)
    (hwG : Integrable (fun z ↦ w z * ‖G z‖ ^ 2) ν)
    (h : δ * (∫ z, W z * ‖η z‖ ^ 2 ∂ν) ≤ ∫ z, W z * ⟪G z, η z⟫_ℝ ∂ν) :
    ∫ z, w z * ‖η z‖ ^ 2 ∂ν ≤ E * E / δ ^ 2 * ∫ z, w z * ‖G z‖ ^ 2 ∂ν := by
  calc ∫ z, w z * ‖η z‖ ^ 2 ∂ν ≤ E * ∫ z, W z * ‖η z‖ ^ 2 ∂ν :=
        integral_mul_norm_sq_le_mul_of_le hw hwW hWη
    _ ≤ E * (1 / δ ^ 2 * (E * ∫ z, w z * ‖G z‖ ^ 2 ∂ν)) := by
      gcongr
      exact (integral_mul_norm_sq_le_of_mul_le_integral_mul_inner hW hWη hWG hδ h).trans
        (by gcongr; exact integral_mul_norm_sq_le_mul_of_le hW hWw hwG)
    _ = E * E / δ ^ 2 * ∫ z, w z * ‖G z‖ ^ 2 ∂ν := by ring

/-- **Hölder's inequality with a bounded weight, for a power `γ ≥ 1`.** On a finite measure
space, let `θ` be a measurable weight with `0 ≤ θ ≤ K` almost everywhere, and let `‖g‖ ∈ L^{γq}`
for a pair of Hölder conjugate exponents `q, q'`. Then
`∫ θ^γ ‖g‖^γ ≤ (K^(γq' - 1) ∫ θ)^(1/q') (∫ ‖g‖^(γq))^(1/q)`. Only the mean of `θ` enters, so
for coefficients of small mean deviation `θ` the right-hand side is small. -/
theorem integral_rpow_mul_norm_rpow_le_of_ae_le {E : Type*} [NormedAddCommGroup E]
    [IsFiniteMeasure ν] {θ : β → ℝ} {g : β → E} {K q q' γ : ℝ} (hγ : 1 ≤ γ)
    (hq : q.HolderConjugate q') (hθm : AEStronglyMeasurable θ ν)
    (hθ : ∀ᵐ x ∂ν, 0 ≤ θ x ∧ θ x ≤ K) (hg : MemLp g (ENNReal.ofReal (γ * q)) ν) :
    ∫ x, θ x ^ γ * ‖g x‖ ^ γ ∂ν ≤
      (K ^ (γ * q' - 1) * ∫ x, θ x ∂ν) ^ q'⁻¹ * (∫ x, ‖g x‖ ^ (γ * q) ∂ν) ^ q⁻¹ := by
  have hγ0 : 0 < γ := zero_lt_one.trans_le hγ
  have hθi : Integrable θ ν := Integrable.of_bound hθm K (hθ.mono fun x hx => by
    rw [Real.norm_of_nonneg hx.1]
    exact hx.2)
  -- Hölder's inequality with exponents `q'` and `q`.
  have hgγ : MemLp (fun x => ‖g x‖ ^ γ) (ENNReal.ofReal q) ν := by
    have h := hg.norm_rpow_div (ENNReal.ofReal γ)
    rwa [← ENNReal.ofReal_div_of_pos hγ0, ENNReal.toReal_ofReal hγ0.le,
      show γ * q / γ = q by field_simp] at h
  have hθγ : MemLp (fun x => θ x ^ γ) (ENNReal.ofReal q') ν :=
    MemLp.of_bound (hθm.aemeasurable.pow_const γ).aestronglyMeasurable (K ^ γ)
      (hθ.mono fun x hx => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.1 γ)]
        exact Real.rpow_le_rpow hx.1 hx.2 hγ0.le)
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg hq.symm
    (hθ.mono fun x hx => Real.rpow_nonneg hx.1 γ) (ae_of_all _ fun x => by positivity) hθγ hgγ
  -- Since `0 ≤ θ ≤ K`, `(θ^γ)^q' = θ^(γq' - 1) θ ≤ K^(γq' - 1) θ`.
  have hθq : ∫ x, (θ x ^ γ) ^ q' ∂ν ≤ K ^ (γ * q' - 1) * ∫ x, θ x ∂ν := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (hθ.mono fun x hx => by
        have := Real.rpow_nonneg hx.1 γ
        positivity) (hθi.const_mul _) (hθ.mono fun x hx => ?_)
    have h1 : 0 ≤ γ * q' - 1 := by nlinarith [hq.symm.lt]
    calc (θ x ^ γ) ^ q' = θ x ^ (γ * q' - 1) * θ x := by
          rw [← Real.rpow_mul hx.1, ← Real.rpow_add_one' hx.1 (by linarith)]
          norm_num
      _ ≤ K ^ (γ * q' - 1) * θ x :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hx.1 hx.2 h1) hx.1
  have hgq : ∫ x, (‖g x‖ ^ γ) ^ q ∂ν = ∫ x, ‖g x‖ ^ (γ * q) ∂ν :=
    integral_congr_ae (ae_of_all _ fun x => by
      simp only
      rw [← Real.rpow_mul (norm_nonneg _)])
  refine hHolder.trans ?_
  rw [hgq, one_div, one_div]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (integral_nonneg_of_ae (hθ.mono fun x hx =>
    Real.rpow_nonneg (Real.rpow_nonneg hx.1 γ) q')) hθq hq.symm.inv_nonneg)
    (Real.rpow_nonneg (integral_nonneg fun x => by positivity) _)

/-- **Hölder's inequality with a bounded weight, in averages.** On a set `s` of finite measure,
let `θ` be a measurable weight with `0 ≤ θ ≤ K` almost everywhere on `s`, and let `‖g‖ ∈ L^{γq}(s)`,
`γ ≥ 1`, for a pair of Hölder conjugate exponents `q, q'`. Then
`⨍_s θ^γ ‖g‖^γ ≤ (K^(γq' - 1) ⨍_s θ)^(1/q') (⨍_s ‖g‖^(γq))^(1/q)`. Every average is invariant
under dilations, which is the form in which the estimate enters scale-invariant arguments. -/
theorem setAverage_rpow_mul_norm_rpow_le_of_ae_le {E : Type*} [NormedAddCommGroup E] {s : Set β}
    (hs : ν s ≠ ⊤) {θ : β → ℝ} {g : β → E} {K q q' γ : ℝ} (hγ : 1 ≤ γ)
    (hq : q.HolderConjugate q') (hθm : AEStronglyMeasurable θ (ν.restrict s))
    (hθ : ∀ᵐ x ∂ν.restrict s, 0 ≤ θ x ∧ θ x ≤ K)
    (hg : MemLp g (ENNReal.ofReal (γ * q)) (ν.restrict s)) :
    ⨍ x in s, θ x ^ γ * ‖g x‖ ^ γ ∂ν ≤
      (K ^ (γ * q' - 1) * ⨍ x in s, θ x ∂ν) ^ q'⁻¹ * (⨍ x in s, ‖g x‖ ^ (γ * q) ∂ν) ^ q⁻¹ := by
  have : IsFiniteMeasure (ν.restrict s) := isFiniteMeasure_restrict.2 hs
  have h := integral_rpow_mul_norm_rpow_le_of_ae_le hγ hq hθm hθ hg
  simp only [setAverage_eq, smul_eq_mul]
  rw [mul_left_comm (K ^ (γ * q' - 1)), Real.mul_rpow_mul_mul_rpow_of_add_eq_one
    (inv_nonneg.2 measureReal_nonneg) hq.symm.inv_add_inv_eq_one]
  exact mul_le_mul_of_nonneg_left h (inv_nonneg.2 measureReal_nonneg)

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
  simpa only [Real.rpow_two] using
    integral_rpow_mul_norm_rpow_le_of_ae_le one_le_two hq hθm hθ hg

/-- **Averaged form of a decay estimate with a Hölder-controlled error.** Let `|t| = δ^N |s|` with
`δ > 0` and `0 < |s| < ∞`, let `θ` be measurable on `s` with `0 ≤ θ ≤ K` there, and let
`‖g‖ ∈ L^{2q}(s)` for a pair of Hölder conjugate exponents `q, q'`. If

`∫_t f ≤ C₁ δ^(N + 2) ∫_s F + C₂ (M ∫_s θ² ‖g‖² + ∫_s G)`

with `C₂, M ≥ 0`, then

`⨍_t f ≤ C₁ δ² ⨍_s F + C₂ δ^(-N) (M (K^(2q' - 1) ⨍_s θ)^(1/q') (⨍_s ‖g‖^(2q))^(1/q) + ⨍_s G)`.

This passes a Campanato-type decay estimate with a coefficient error to averages, which are
invariant under dilations. -/
theorem setAverage_le_of_setIntegral_le_add_sq_mul_norm_sq {E : Type*} [NormedAddCommGroup E]
    {s t : Set β} {f F G θ : β → ℝ} {g : β → E} {C₁ C₂ K M δ q q' : ℝ} {N : ℕ}
    (hs : 0 < ν.real s) (hδ : 0 < δ) (ht : ν.real t = δ ^ N * ν.real s) (hC₂ : 0 ≤ C₂)
    (hM : 0 ≤ M) (hq : q.HolderConjugate q') (hθm : AEStronglyMeasurable θ (ν.restrict s))
    (hθ : ∀ᵐ x ∂ν.restrict s, 0 ≤ θ x ∧ θ x ≤ K)
    (hg : MemLp g (ENNReal.ofReal (2 * q)) (ν.restrict s))
    (h : ∫ x in t, f x ∂ν ≤ C₁ * δ ^ (N + 2) * ∫ x in s, F x ∂ν +
      C₂ * (M * ∫ x in s, θ x ^ 2 * ‖g x‖ ^ 2 ∂ν + ∫ x in s, G x ∂ν)) :
    ⨍ x in t, f x ∂ν ≤ C₁ * δ ^ 2 * ⨍ x in s, F x ∂ν +
      C₂ * δ⁻¹ ^ N * (M * ((K ^ (2 * q' - 1) * ⨍ x in s, θ x ∂ν) ^ q'⁻¹ *
        (⨍ x in s, ‖g x‖ ^ (2 * q) ∂ν) ^ q⁻¹) + ⨍ x in s, G x ∂ν) := by
  have : IsFiniteMeasure (ν.restrict s) :=
    isFiniteMeasure_restrict.2 fun h => by simp [Measure.real, h] at hs
  have hΘ := integral_sq_mul_norm_sq_le_of_ae_le hq hθm hθ hg
  simp only [setAverage_eq, smul_eq_mul, ht]
  set V := ν.real s
  set Iθ := ∫ x in s, θ x ∂ν
  set Ig := ∫ x in s, ‖g x‖ ^ (2 * q) ∂ν
  have hsplit : (K ^ (2 * q' - 1) * (V⁻¹ * Iθ)) ^ q'⁻¹ * (V⁻¹ * Ig) ^ q⁻¹ =
      V⁻¹ * ((K ^ (2 * q' - 1) * Iθ) ^ q'⁻¹ * Ig ^ q⁻¹) := by
    rw [mul_left_comm (K ^ (2 * q' - 1)) V⁻¹ Iθ]
    exact Real.mul_rpow_mul_mul_rpow_of_add_eq_one (inv_nonneg.2 hs.le)
      hq.symm.inv_add_inv_eq_one
  rw [hsplit]
  refine (mul_le_mul_of_nonneg_left (h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hΘ hM) le_rfl) hC₂))) (by positivity)).trans_eq ?_
  have hV0 : V ≠ 0 := hs.ne'
  rw [inv_pow]
  field_simp
  ring

/-- **The power-mean inequality under a set integral.** If `‖φ‖ ≤ ‖ψ‖ + ‖χ‖` almost everywhere on
`s`, then `∫_s ‖φ‖^γ ≤ 2^(γ - 1) (∫_s ‖ψ‖^γ + ∫_s ‖χ‖^γ)` for `γ ≥ 1`. -/
theorem setIntegral_norm_rpow_le_of_ae_norm_le {F : Type*} [NormedAddCommGroup F] {s : Set β}
    {φ ψ χ : β → F} {γ : ℝ} (hγ : 1 ≤ γ) (h : ∀ᵐ x ∂ν.restrict s, ‖φ x‖ ≤ ‖ψ x‖ + ‖χ x‖)
    (hψ : IntegrableOn (fun x ↦ ‖ψ x‖ ^ γ) s ν) (hχ : IntegrableOn (fun x ↦ ‖χ x‖ ^ γ) s ν) :
    ∫ x in s, ‖φ x‖ ^ γ ∂ν ≤
      2 ^ (γ - 1) * ((∫ x in s, ‖ψ x‖ ^ γ ∂ν) + ∫ x in s, ‖χ x‖ ^ γ ∂ν) := by
  rw [← integral_add hψ hχ, ← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun _ ↦ by positivity) ((hψ.add hχ).const_mul _)
    (h.mono fun x hx ↦ ?_)
  exact (Real.rpow_le_rpow (norm_nonneg _) hx (zero_le_one.trans hγ)).trans
    (Real.rpow_add_le_mul_rpow_add_rpow (norm_nonneg _) (norm_nonneg _) hγ)

end TauCeti

namespace MeasureTheory

/-- For a nonempty finite set `s` of cardinality `k`, the norm of the integral of the product
over `s` is bounded by the average of the `k`th absolute moments. No independence or finiteness
of the underlying measure is needed. -/
theorem norm_integral_prod_le_inv_card_mul_sum_integral_norm_pow {Ω ι 𝕜 : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} [NormedCommRing 𝕜] [NormedSpace ℝ 𝕜]
    (f : ι → Ω → 𝕜) {s : Finset ι} (hs : s.Nonempty)
    (hf : ∀ i ∈ s, Integrable (fun x ↦ ‖f i x‖ ^ s.card) μ) :
    ‖∫ x, ∏ i ∈ s, f i x ∂μ‖ ≤
      (s.card : ℝ)⁻¹ * ∑ i ∈ s, ∫ x, ‖f i x‖ ^ s.card ∂μ := by
  classical
  have hk : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_ne_zero
  have hpoint (x : Ω) : ‖∏ i ∈ s, f i x‖ ≤
      ∑ i ∈ s, (s.card : ℝ)⁻¹ * ‖f i x‖ ^ s.card := by
    refine (Finset.norm_prod_le' s hs (fun i ↦ f i x)).trans ?_
    have h := Real.geom_mean_le_arith_mean_weighted s
      (fun _ : ι ↦ (s.card : ℝ)⁻¹)
      (fun i ↦ ‖f i x‖ ^ s.card)
      (fun _ _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _))
      (by simp [hk]) (fun _ _ ↦ by positivity)
    convert h using 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ hk,
      Real.rpow_one]
  have hbound := norm_integral_le_of_norm_le
    (integrable_finsetSum _ fun i hi ↦ (hf i hi).const_mul (s.card : ℝ)⁻¹)
    (Filter.Eventually.of_forall hpoint)
  simpa only [integral_finsetSum _ fun i hi ↦ (hf i hi).const_mul _, integral_const_mul,
    Finset.mul_sum] using hbound

end MeasureTheory
