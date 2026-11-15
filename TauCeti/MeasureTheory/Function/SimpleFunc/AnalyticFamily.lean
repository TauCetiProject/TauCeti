/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.MeasureTheory.Function.SimpleFunc.Basic
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Thorin's analytic family through a simple function

For a complex number `w` put `powSign w c = (c / |c|) |c| ^ w`, with `powSign w 0 = 0`
(`TauCeti.AnalyticFamily.powSign`). Through a complex simple function `u` it gives the family
`u_w = u.map (powSign w) = sgn(u) |u| ^ w`, with `u_1 = u`. Thorin's proof of the Riesz–Thorin
theorem, and Calderón's identification of the complex interpolation spaces of the Lebesgue
couple, evaluate this family along an affine exponent `w = exponent a₀ a₁ θ z`
(`TauCeti.AnalyticFamily.exponent`) normalized so that `exponent a₀ a₁ θ θ = 1`.

Choose `a_j = 1 / s_j` for exponents `s₀, s₁ ≠ 0` and let `1 / s = (1 - θ) / s₀ + θ / s₁` for some
`0 < θ < 1`. If `u` lies in the unit ball of `Lˢ`, then `u_w` lies in the unit ball of `L^{s₀}`
on the line `re z = 0` and in the unit ball of `L^{s₁}` on the line `re z = 1`
(`MeasureTheory.SimpleFunc.eLpNorm_map_powSign_exponent_le_one_of_re_eq_zero`,
`MeasureTheory.SimpleFunc.eLpNorm_map_powSign_exponent_le_one_of_re_eq_one`). Since `u` takes
finitely many values, `u_w` is the finite combination `∑ c, powSign w c • 1_{u = c}` of the fibre
indicators `MeasureTheory.SimpleFunc.fiberIndicator` of `u`
(`MeasureTheory.SimpleFunc.map_eq_sum_smul_fiberIndicator`), whose coefficients are entire
functions of `z` (`TauCeti.AnalyticFamily.differentiable_powSign_exponent`), bounded on the strip
`0 ≤ re z ≤ 1` (`TauCeti.AnalyticFamily.norm_powSign_exponent_le`). Accordingly, integration
against `u_w` expands along the fibres of `u`
(`MeasureTheory.SimpleFunc.integral_mul_map_eq_sum`).

## References

* G. O. Thorin, *An extension of a convexity theorem due to M. Riesz*, Kungl. Fysiogr. Sällsk.
  i Lund Förh. 8 (1939).
* L. Grafakos, *Classical Fourier Analysis*, proof of Theorem 1.3.4.
-/

public section

open MeasureTheory Complex
open scoped ENNReal NNReal

namespace TauCeti.AnalyticFamily

/-- `powSign w c = (c / |c|) |c| ^ w`, with `powSign w 0 = 0`. -/
noncomputable def powSign (w c : ℂ) : ℂ := c / (‖c‖ : ℂ) * exp (w * (Real.log ‖c‖ : ℂ))

/-- The defining formula of `powSign`. -/
theorem powSign_def (w c : ℂ) :
    powSign w c = c / (‖c‖ : ℂ) * exp (w * (Real.log ‖c‖ : ℂ)) :=
  (rfl)

/-- At `w = 1` the family gives back `c`. -/
@[simp]
theorem powSign_one_left (c : ℂ) : powSign 1 c = c := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [powSign]
  · have hpos : 0 < ‖c‖ := norm_pos_iff.2 hc
    rw [powSign, one_mul, ← ofReal_exp, Real.exp_log hpos,
      div_mul_cancel₀ _ (ofReal_ne_zero.2 hpos.ne')]

/-- The family vanishes at `c = 0`. -/
@[simp]
theorem powSign_zero_right (w : ℂ) : powSign w 0 = 0 := by simp [powSign]

/-- `|powSign w c| ≤ |c| ^ re w`. -/
theorem norm_powSign_le (w c : ℂ) : ‖powSign w c‖ ≤ ‖c‖ ^ w.re := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [Real.rpow_nonneg]
  · have hpos : 0 < ‖c‖ := norm_pos_iff.2 hc
    rw [powSign, norm_mul, norm_div, norm_exp, norm_real, Real.norm_of_nonneg hpos.le,
      div_self hpos.ne', one_mul, Real.rpow_def_of_pos hpos]
    simp [mul_comm]

private theorem norm_powSign_le_exp (w c : ℂ) :
    ‖powSign w c‖ ≤ Real.exp (|w.re| * |Real.log ‖c‖|) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have hpos : 0 < ‖c‖ := norm_pos_iff.2 hc
    rw [powSign, norm_mul, norm_div, norm_exp, norm_real, Real.norm_of_nonneg hpos.le,
      div_self hpos.ne', one_mul]
    gcongr
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact (le_abs_self _).trans (abs_mul _ _).le

/-- The slope `(a₁ - a₀) / a` of the exponent family, where `a = (1 - θ) a₀ + θ a₁`. -/
noncomputable def exponentSlope (a₀ a₁ θ : ℝ) : ℝ := (a₁ - a₀) / ((1 - θ) * a₀ + θ * a₁)

/-- The defining formula of `exponentSlope`. -/
theorem exponentSlope_def (a₀ a₁ θ : ℝ) :
    exponentSlope a₀ a₁ θ = (a₁ - a₀) / ((1 - θ) * a₀ + θ * a₁) :=
  (rfl)

/-- The exponent of the analytic family, `1 + (z - θ) (a₁ - a₀) / a` with
`a = (1 - θ) a₀ + θ a₁`. It equals `1` at `z = θ`. If `a ≠ 0`, its real part is `a₀ / a` on the
line `Re z = 0` and `a₁ / a` on the line `Re z = 1`. If `a = 0` (which for `a₀, a₁ ≥ 0` and
`0 < θ < 1` forces `a₀ = a₁ = 0`), the slope is `0` and the exponent is constantly `1`. -/
noncomputable def exponent (a₀ a₁ θ : ℝ) (z : ℂ) : ℂ := 1 + (z - θ) * (exponentSlope a₀ a₁ θ : ℂ)

/-- The defining formula of `exponent`. -/
theorem exponent_def (a₀ a₁ θ : ℝ) (z : ℂ) :
    exponent a₀ a₁ θ z = 1 + (z - θ) * (exponentSlope a₀ a₁ θ : ℂ) :=
  (rfl)

/-- The real part of the exponent of the analytic family. -/
theorem re_exponent (a₀ a₁ θ : ℝ) (z : ℂ) :
    (exponent a₀ a₁ θ z).re = 1 + (z.re - θ) * exponentSlope a₀ a₁ θ := by
  simp [exponent]

/-- The exponent of the analytic family is `1` at `z = θ`. -/
@[simp]
theorem exponent_self (a₀ a₁ θ : ℝ) : exponent a₀ a₁ θ θ = 1 := by simp [exponent]

private theorem re_exponent_mul {a₀ a₁ θ : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (z : ℂ) :
    (exponent a₀ a₁ θ z).re * ((1 - θ) * a₀ + θ * a₁) = (1 - z.re) * a₀ + z.re * a₁ := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  rw [re_exponent, exponentSlope]
  rcases eq_or_ne ((1 - θ) * a₀ + θ * a₁) 0 with ha | ha
  · obtain ⟨rfl, rfl⟩ : a₀ = 0 ∧ a₁ = 0 := by
      constructor <;> nlinarith [mul_nonneg (sub_pos.2 hθ1).le ha₀, mul_nonneg hθ0.le ha₁]
    simp
  · rw [add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ ha]
    ring

private theorem re_exponent_nonneg {a₀ a₁ θ : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ (exponent a₀ a₁ θ z).re := by
  have h := re_exponent_mul ha₀ ha₁ hθ z
  obtain ⟨hθ0, hθ1⟩ := hθ
  have ha : 0 ≤ (1 - θ) * a₀ + θ * a₁ := by
    have := sub_pos.2 hθ1
    positivity
  rcases ha.eq_or_lt with ha | ha
  · obtain ⟨rfl, rfl⟩ : a₀ = 0 ∧ a₁ = 0 := by
      constructor <;> nlinarith [mul_nonneg (sub_pos.2 hθ1).le ha₀, mul_nonneg hθ0.le ha₁]
    simp [re_exponent, exponentSlope]
  · have : 0 ≤ (1 - z.re) * a₀ + z.re * a₁ := by
      have := hz.1
      have := sub_nonneg.2 hz.2
      positivity
    nlinarith

private theorem abs_re_exponent_le {a₀ a₁ θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) {z : ℂ}
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1) :
    |(exponent a₀ a₁ θ z).re| ≤ 1 + |exponentSlope a₀ a₁ θ| := by
  rw [re_exponent]
  have h1 : |z.re - θ| ≤ 1 := abs_le.2 ⟨by linarith [hz.1, hθ.2], by linarith [hz.2, hθ.1]⟩
  calc _ ≤ |(1 : ℝ)| + |(z.re - θ) * exponentSlope a₀ a₁ θ| := abs_add_le _ _
    _ ≤ 1 + 1 * |exponentSlope a₀ a₁ θ| := by
        rw [abs_one, abs_mul]; gcongr
    _ = _ := by ring

/-- On the closed strip `0 ≤ Re z ≤ 1` the members of the analytic family are bounded uniformly
in `z`. -/
theorem norm_powSign_exponent_le {a₀ a₁ θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) {z : ℂ}
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1) (c : ℂ) :
    ‖powSign (exponent a₀ a₁ θ z) c‖ ≤
      Real.exp ((1 + |exponentSlope a₀ a₁ θ|) * |Real.log ‖c‖|) :=
  (norm_powSign_le_exp _ _).trans (Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_right (abs_re_exponent_le hθ hz) (abs_nonneg _)))

/-- For fixed `c`, the coefficient `powSign (exponent a₀ a₁ θ z) c` of the analytic family is an
entire function of `z`. -/
theorem differentiable_powSign_exponent (a₀ a₁ θ : ℝ) (c : ℂ) :
    Differentiable ℂ fun z => powSign (exponent a₀ a₁ θ z) c := by
  simp only [powSign, exponent]
  fun_prop

/-- Along the interpolating family, the exponent `1 / s(z)` of the endpoint spaces is reached at
the real part of `exponent`. -/
private theorem ofReal_re_exponent_mul_inv {s₀ s₁ s : ℝ≥0∞} (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) {z : ℂ}
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal (exponent (s₀⁻¹).toReal (s₁⁻¹).toReal θ z).re * s⁻¹ =
      ENNReal.ofReal (1 - z.re) * s₀⁻¹ + ENNReal.ofReal z.re * s₁⁻¹ := by
  have h₀ : s₀⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hs₀
  have h₁ : s₁⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hs₁
  have hz1 : 0 ≤ 1 - z.re := sub_nonneg.2 hz.2
  have hre := re_exponent_mul (ENNReal.toReal_nonneg (a := s₀⁻¹))
    (ENNReal.toReal_nonneg (a := s₁⁻¹)) hθ z
  have hnn := re_exponent_nonneg (ENNReal.toReal_nonneg (a := s₀⁻¹))
    (ENNReal.toReal_nonneg (a := s₁⁻¹)) hθ hz
  have h0 : (0 : ℝ) ≤ (s₀⁻¹).toReal := ENNReal.toReal_nonneg
  have h1 : (0 : ℝ) ≤ (s₁⁻¹).toReal := ENNReal.toReal_nonneg
  rw [inv_eq_ofReal_of_inv_eq hs₀ hs₁ (Set.Ioo_subset_Icc_self hθ) hs, ← ENNReal.ofReal_mul hnn,
    hre, ENNReal.ofReal_add (mul_nonneg hz1 h0) (mul_nonneg hz.1 h1),
    ENNReal.ofReal_mul hz1, ENNReal.ofReal_mul hz.1, ENNReal.ofReal_toReal h₀,
    ENNReal.ofReal_toReal h₁]

end TauCeti.AnalyticFamily

namespace MeasureTheory.SimpleFunc

open TauCeti TauCeti.AnalyticFamily

variable {γ : Type*} {mγ : MeasurableSpace γ} {ρ : Measure γ}

/-- Integration against `k.map ψ` expands along the fibres of `k`, provided `u` is integrable
against every fibre indicator `1_{k = d}` with `ψ d ≠ 0`. -/
theorem integral_mul_map_eq_sum {𝕜 β : Type*} [RCLike 𝕜] {u : γ → 𝕜} (k : SimpleFunc γ β)
    (ψ : β → 𝕜)
    (hu : ∀ d ∈ k.range, ψ d ≠ 0 → Integrable (fun x => u x * fiberIndicator 𝕜 k d x) ρ) :
    ∫ x, u x * k.map ψ x ∂ρ = ∑ d ∈ k.range, ψ d * ∫ x, u x * fiberIndicator 𝕜 k d x ∂ρ := by
  have hint : ∀ d ∈ k.range, Integrable (fun x => ψ d * (u x * fiberIndicator 𝕜 k d x)) ρ := by
    intro d hd
    by_cases h : ψ d = 0
    · simp [h]
    · exact (hu d hd h).const_mul _
  calc ∫ x, u x * k.map ψ x ∂ρ
      = ∫ x, ∑ d ∈ k.range, ψ d * (u x * fiberIndicator 𝕜 k d x) ∂ρ := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [map_apply_eq_sum_mul_fiberIndicator, Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => by ring
    _ = ∑ d ∈ k.range, ∫ x, ψ d * (u x * fiberIndicator 𝕜 k d x) ∂ρ := integral_finsetSum _ hint
    _ = _ := Finset.sum_congr rfl fun d _ => integral_const_mul _ _

/-- Dividing a complex simple function of finite nonzero `Lˢ` norm by that norm puts it on the
unit sphere of `Lˢ`. -/
theorem eLpNorm_inv_toReal_smul_eq_one (u : SimpleFunc γ ℂ) {s : ℝ≥0∞}
    (h0 : eLpNorm u s ρ ≠ 0) (htop : eLpNorm u s ρ ≠ ∞) :
    eLpNorm ⇑((((eLpNorm u s ρ).toReal⁻¹ : ℝ) : ℂ) • u) s ρ = 1 := by
  rw [FunLike.coe_smul, eLpNorm_const_smul, ← ofReal_norm, norm_real,
    Real.norm_of_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg),
    ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos h0 htop), ENNReal.ofReal_toReal htop,
    ENNReal.inv_mul_cancel h0 htop]

/-- The member `u_w = sgn(u) |u| ^ w` of the analytic family through `u` has `Lᵗ` norm at most
one, where `1 / t = Re w / s`, whenever `u` has `Lˢ` norm at most one. -/
private theorem eLpNorm_map_powSign_le_one (u : SimpleFunc γ ℂ) {s t : ℝ≥0∞} {w : ℂ}
    (hw : 0 ≤ w.re) (ht : t⁻¹ = ENNReal.ofReal w.re * s⁻¹) (hu : eLpNorm u s ρ ≤ 1) :
    eLpNorm (u.map (powSign w)) t ρ ≤ 1 :=
  (eLpNorm_le_eLpNorm_rpow hw (u.map _).aestronglyMeasurable ht
    (ae_of_all _ fun x => norm_powSign_le w (u x))).trans (ENNReal.rpow_le_one hu hw)

/-- The indicator of a nonzero fibre of a simple function `u` is in `Lᵗ` as soon as some member
`u_w` of the analytic family through `u` is. -/
theorem memLp_fiberIndicator (u : SimpleFunc γ ℂ) {t : ℝ≥0∞} {w c : ℂ} (hc : c ≠ 0)
    (hu : MemLp (u.map (powSign w)) t ρ) : MemLp (fiberIndicator ℂ u c) t ρ := by
  have hne : powSign w c ≠ 0 := by
    have : (c / (‖c‖ : ℂ)) ≠ 0 := div_ne_zero hc (ofReal_ne_zero.2 (norm_ne_zero_iff.2 hc))
    simpa [powSign] using this
  classical
  refine hu.of_le_mul (fiberIndicator ℂ u c).aestronglyMeasurable (c := ‖powSign w c‖⁻¹)
    (ae_of_all _ fun x => ?_)
  rw [fiberIndicator_apply, SimpleFunc.map_apply]
  split_ifs with h
  · rw [h, norm_one, inv_mul_cancel₀ (norm_ne_zero_iff.2 hne)]
  · simp only [norm_zero]
    positivity

/-- Let `s₀, s₁ ≠ 0`, `0 < θ < 1` and `1 / s = (1 - θ) / s₀ + θ / s₁`. If `u` lies in the unit
ball of `Lˢ`, then on the line `Re z = 0` the analytic family through `u` lies in the unit ball
of `L^{s₀}`. -/
theorem eLpNorm_map_powSign_exponent_le_one_of_re_eq_zero (u : SimpleFunc γ ℂ)
    {s₀ s₁ s : ℝ≥0∞} (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹)
    (hu : eLpNorm u s ρ ≤ 1) {z : ℂ} (hz : z.re = 0) :
    eLpNorm (u.map (powSign (exponent (s₀⁻¹).toReal (s₁⁻¹).toReal θ z))) s₀ ρ ≤ 1 := by
  have hz' : z.re ∈ Set.Icc (0 : ℝ) 1 := by simp [hz]
  refine eLpNorm_map_powSign_le_one u (re_exponent_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg hθ hz') ?_ hu
  rw [ofReal_re_exponent_mul_inv hs₀ hs₁ hθ hs hz', hz]
  simp

/-- Let `s₀, s₁ ≠ 0`, `0 < θ < 1` and `1 / s = (1 - θ) / s₀ + θ / s₁`. If `u` lies in the unit
ball of `Lˢ`, then on the line `Re z = 1` the analytic family through `u` lies in the unit ball
of `L^{s₁}`. -/
theorem eLpNorm_map_powSign_exponent_le_one_of_re_eq_one (u : SimpleFunc γ ℂ)
    {s₀ s₁ s : ℝ≥0∞} (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹)
    (hu : eLpNorm u s ρ ≤ 1) {z : ℂ} (hz : z.re = 1) :
    eLpNorm (u.map (powSign (exponent (s₀⁻¹).toReal (s₁⁻¹).toReal θ z))) s₁ ρ ≤ 1 := by
  have hz' : z.re ∈ Set.Icc (0 : ℝ) 1 := by simp [hz]
  refine eLpNorm_map_powSign_le_one u (re_exponent_nonneg ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg hθ hz') ?_ hu
  rw [ofReal_re_exponent_mul_inv hs₀ hs₁ hθ hs hz', hz]
  simp

/-- The analytic family through `u` passes through `u` at `w = 1`. -/
@[simp]
theorem map_powSign_one (u : SimpleFunc γ ℂ) : u.map (powSign 1) = u :=
  SimpleFunc.ext fun x => powSign_one_left (u x)

end MeasureTheory.SimpleFunc
