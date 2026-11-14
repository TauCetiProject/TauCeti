/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.SimpleFunc.Basic

/-!
# Thorin's analytic family through a simple function

For a complex number `w` put `powSign w c = (c / |c|) |c| ^ w`, with `powSign w 0 = 0`
(`TauCeti.RieszThorin.powSign`). Through a complex simple function `u` it gives the family
`u_w = u.map (powSign w) = sgn(u) |u| ^ w`, with `u_1 = u`. Thorin's proof of the Riesz–Thorin
theorem, and Calderón's identification of the complex interpolation spaces of the Lebesgue
couple, evaluate this family along an affine exponent `w = expo a₀ a₁ θ z`
(`TauCeti.RieszThorin.expo`) normalized so that `expo a₀ a₁ θ θ = 1`.

Choose `a_j = 1 / s_j` for exponents `s₀, s₁` and let `1 / s = (1 - θ) / s₀ + θ / s₁` for some
`0 < θ < 1`. If `u` lies in the unit ball of `Lˢ`, then `u_w` lies in the unit ball of `L^{s₀}`
on the line `re z = 0` and in the unit ball of `L^{s₁}` on the line `re z = 1`
(`MeasureTheory.SimpleFunc.eLpNorm_map_powSign_expo_le_one_of_re_eq_zero`,
`MeasureTheory.SimpleFunc.eLpNorm_map_powSign_expo_le_one_of_re_eq_one`). Since `u` takes finitely
many values, `u_w` is the finite combination `∑ c, powSign w c • 1_{u = c}` of the fibre
indicators `MeasureTheory.SimpleFunc.fiberInd` of `u`
(`MeasureTheory.SimpleFunc.map_eq_sum_smul_fiberInd`), whose coefficients are entire functions
of `z` (`TauCeti.RieszThorin.differentiable_powSign_expo`), bounded on the strip
`0 ≤ re z ≤ 1` (`TauCeti.RieszThorin.norm_powSign_expo_le`).

## References

* G. O. Thorin, *An extension of a convexity theorem due to M. Riesz*, Kungl. Fysiogr. Sällsk.
  i Lund Förh. 8 (1939).
* L. Grafakos, *Classical Fourier Analysis*, proof of Theorem 1.3.4.
-/

public section

open MeasureTheory Complex
open scoped ENNReal NNReal

namespace TauCeti.RieszThorin

/-- `powSign w c = (c / |c|) |c| ^ w`, with `powSign w 0 = 0`. -/
noncomputable def powSign (w c : ℂ) : ℂ := c / (‖c‖ : ℂ) * exp (w * (Real.log ‖c‖ : ℂ))

/-- At `w = 1` the family gives back `c`. -/
theorem powSign_one (c : ℂ) : powSign 1 c = c := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [powSign]
  · have hpos : 0 < ‖c‖ := norm_pos_iff.2 hc
    rw [powSign, one_mul, ← ofReal_exp, Real.exp_log hpos,
      div_mul_cancel₀ _ (ofReal_ne_zero.2 hpos.ne')]

/-- The family vanishes at `c = 0`. -/
theorem powSign_zero_right (w : ℂ) : powSign w 0 = 0 := by simp [powSign]

/-- `|powSign w c| ≤ |c| ^ re w`, with equality for `c ≠ 0`. -/
theorem norm_powSign_le (w c : ℂ) : ‖powSign w c‖ ≤ ‖c‖ ^ w.re := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [powSign_zero_right, Real.rpow_nonneg]
  · have hpos : 0 < ‖c‖ := norm_pos_iff.2 hc
    rw [powSign, norm_mul, norm_div, norm_exp, norm_real, Real.norm_of_nonneg hpos.le,
      div_self hpos.ne', one_mul, Real.rpow_def_of_pos hpos]
    simp [mul_comm]

private theorem norm_powSign_le_exp (w c : ℂ) :
    ‖powSign w c‖ ≤ Real.exp (|w.re| * |Real.log ‖c‖|) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [powSign_zero_right]
  · have hpos : 0 < ‖c‖ := norm_pos_iff.2 hc
    rw [powSign, norm_mul, norm_div, norm_exp, norm_real, Real.norm_of_nonneg hpos.le,
      div_self hpos.ne', one_mul]
    gcongr
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact (le_abs_self _).trans (abs_mul _ _).le

/-- The slope `(a₁ - a₀) / a` of the exponent family, where `a = (1 - θ) a₀ + θ a₁`. -/
noncomputable def slope (a₀ a₁ θ : ℝ) : ℝ := (a₁ - a₀) / ((1 - θ) * a₀ + θ * a₁)

/-- The exponent of the analytic family, `1 + (z - θ) (a₁ - a₀) / a`. It equals `1` at `z = θ`,
and its real part is `a₀ / a` on the line `Re z = 0` and `a₁ / a` on the line `Re z = 1`. If
`a = 0` then `a₀ = a₁ = 0` and the exponent is constantly `1`. -/
noncomputable def expo (a₀ a₁ θ : ℝ) (z : ℂ) : ℂ := 1 + (z - θ) * (slope a₀ a₁ θ : ℂ)

private theorem re_expo (a₀ a₁ θ : ℝ) (z : ℂ) :
    (expo a₀ a₁ θ z).re = 1 + (z.re - θ) * slope a₀ a₁ θ := by
  simp [expo]

/-- The exponent of the analytic family is `1` at `z = θ`. -/
theorem expo_self (a₀ a₁ θ : ℝ) : expo a₀ a₁ θ θ = 1 := by simp [expo]

private theorem re_expo_mul {a₀ a₁ θ : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (z : ℂ) :
    (expo a₀ a₁ θ z).re * ((1 - θ) * a₀ + θ * a₁) = (1 - z.re) * a₀ + z.re * a₁ := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  rw [re_expo, slope]
  rcases eq_or_ne ((1 - θ) * a₀ + θ * a₁) 0 with ha | ha
  · obtain ⟨rfl, rfl⟩ : a₀ = 0 ∧ a₁ = 0 := by
      constructor <;> nlinarith [mul_nonneg (sub_pos.2 hθ1).le ha₀, mul_nonneg hθ0.le ha₁]
    simp
  · rw [add_mul, one_mul, mul_assoc, div_mul_cancel₀ _ ha]
    ring

private theorem re_expo_nonneg {a₀ a₁ θ : ℝ} (ha₀ : 0 ≤ a₀) (ha₁ : 0 ≤ a₁)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    {z : ℂ} (hz : z.re ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ (expo a₀ a₁ θ z).re := by
  have h := re_expo_mul ha₀ ha₁ hθ z
  obtain ⟨hθ0, hθ1⟩ := hθ
  have ha : 0 ≤ (1 - θ) * a₀ + θ * a₁ := by
    have := sub_pos.2 hθ1
    positivity
  rcases ha.eq_or_lt with ha | ha
  · obtain ⟨rfl, rfl⟩ : a₀ = 0 ∧ a₁ = 0 := by
      constructor <;> nlinarith [mul_nonneg (sub_pos.2 hθ1).le ha₀, mul_nonneg hθ0.le ha₁]
    simp [re_expo, slope]
  · have : 0 ≤ (1 - z.re) * a₀ + z.re * a₁ := by
      have := hz.1
      have := sub_nonneg.2 hz.2
      positivity
    nlinarith

private theorem abs_re_expo_le {a₀ a₁ θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) {z : ℂ}
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1) :
    |(expo a₀ a₁ θ z).re| ≤ 1 + |slope a₀ a₁ θ| := by
  rw [re_expo]
  have h1 : |z.re - θ| ≤ 1 := abs_le.2 ⟨by linarith [hz.1, hθ.2], by linarith [hz.2, hθ.1]⟩
  calc _ ≤ |(1 : ℝ)| + |(z.re - θ) * slope a₀ a₁ θ| := abs_add_le _ _
    _ ≤ 1 + 1 * |slope a₀ a₁ θ| := by
        rw [abs_one, abs_mul]; gcongr
    _ = _ := by ring

/-- On the closed strip `0 ≤ Re z ≤ 1` the members of the analytic family are bounded uniformly
in `z`. -/
theorem norm_powSign_expo_le {a₀ a₁ θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) {z : ℂ}
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1) (c : ℂ) :
    ‖powSign (expo a₀ a₁ θ z) c‖ ≤ Real.exp ((1 + |slope a₀ a₁ θ|) * |Real.log ‖c‖|) :=
  (norm_powSign_le_exp _ _).trans (Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_right (abs_re_expo_le hθ hz) (abs_nonneg _)))

/-- For fixed `c`, the coefficient `powSign (expo a₀ a₁ θ z) c` of the analytic family is an
entire function of `z`. -/
theorem differentiable_powSign_expo (a₀ a₁ θ : ℝ) (c : ℂ) :
    Differentiable ℂ fun z => powSign (expo a₀ a₁ θ z) c := by
  simp only [powSign, expo]
  fun_prop

/-- Along the interpolating family, the exponent `1 / s(z)` of the endpoint spaces is reached at
the real part of `expo`. -/
private theorem ofReal_re_expo_mul_inv {s₀ s₁ s : ℝ≥0∞} (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹) {z : ℂ}
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1) :
    ENNReal.ofReal (expo (s₀⁻¹).toReal (s₁⁻¹).toReal θ z).re * s⁻¹ =
      ENNReal.ofReal (1 - z.re) * s₀⁻¹ + ENNReal.ofReal z.re * s₁⁻¹ := by
  have h₀ : s₀⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hs₀
  have h₁ : s₁⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hs₁
  have hz1 : 0 ≤ 1 - z.re := sub_nonneg.2 hz.2
  have hre := re_expo_mul (ENNReal.toReal_nonneg (a := s₀⁻¹)) (ENNReal.toReal_nonneg (a := s₁⁻¹))
    hθ z
  have hnn := re_expo_nonneg (ENNReal.toReal_nonneg (a := s₀⁻¹))
    (ENNReal.toReal_nonneg (a := s₁⁻¹)) hθ hz
  have h0 : (0 : ℝ) ≤ (s₀⁻¹).toReal := ENNReal.toReal_nonneg
  have h1 : (0 : ℝ) ≤ (s₁⁻¹).toReal := ENNReal.toReal_nonneg
  rw [inv_eq_ofReal_of_inv_eq hs₀ hs₁ (Set.Ioo_subset_Icc_self hθ) hs, ← ENNReal.ofReal_mul hnn,
    hre, ENNReal.ofReal_add (mul_nonneg hz1 h0) (mul_nonneg hz.1 h1),
    ENNReal.ofReal_mul hz1, ENNReal.ofReal_mul hz.1, ENNReal.ofReal_toReal h₀,
    ENNReal.ofReal_toReal h₁]

end TauCeti.RieszThorin

namespace MeasureTheory.SimpleFunc

open TauCeti TauCeti.RieszThorin

variable {γ : Type*} {mγ : MeasurableSpace γ} {ρ : Measure γ}

/-- The indicator of the fibre `u ⁻¹' {c}` of a simple function. -/
noncomputable def fiberInd (u : SimpleFunc γ ℂ) (c : ℂ) : SimpleFunc γ ℂ :=
  (SimpleFunc.const γ (1 : ℂ)).restrict (u ⁻¹' {c})

/-- The fibre indicator `1_{u = c}` is `1` on the fibre and `0` off it. -/
theorem fiberInd_apply (u : SimpleFunc γ ℂ) (c : ℂ) (x : γ) :
    fiberInd u c x = if u x = c then 1 else 0 := by
  simp only [fiberInd, SimpleFunc.restrict_apply _ (u.measurableSet_fiber c), SimpleFunc.coe_const]
  by_cases h : u x = c <;> simp [h]

private theorem smul_fiberInd (u : SimpleFunc γ ℂ) (a c : ℂ) :
    a • fiberInd u c = (SimpleFunc.const γ a).restrict (u ⁻¹' {c}) := by
  ext x
  simp [fiberInd_apply, SimpleFunc.restrict_apply _ (u.measurableSet_fiber c), Set.indicator]

/-- `u.map ψ` is the combination `∑ c ∈ u.range, ψ c • 1_{u = c}` of the fibre indicators of
`u`. -/
theorem map_eq_sum_smul_fiberInd (u : SimpleFunc γ ℂ) (ψ : ℂ → ℂ) :
    u.map ψ = ∑ c ∈ u.range, ψ c • fiberInd u c := by
  simp_rw [smul_fiberInd]
  exact u.map_eq_sum_restrict_const ψ

/-- Pointwise form of `MeasureTheory.SimpleFunc.map_eq_sum_smul_fiberInd`. -/
theorem map_apply_eq_sum_mul_fiberInd (u : SimpleFunc γ ℂ) (ψ : ℂ → ℂ) (x : γ) :
    u.map ψ x = ∑ c ∈ u.range, ψ c * fiberInd u c x := by
  rw [u.map_apply_eq_sum_restrict_const]
  simp_rw [← smul_fiberInd, _root_.smul_apply, smul_eq_mul]

/-- The member `u_w = sgn(u) |u| ^ w` of the analytic family through `u` has `Lᵗ` norm at most
one, where `1 / t = Re w / s`, whenever `u` has `Lˢ` norm at most one. -/
private theorem eLpNorm_map_powSign_le_one (u : SimpleFunc γ ℂ) {s t : ℝ≥0∞} {w : ℂ}
    (hw : 0 ≤ w.re) (ht : t⁻¹ = ENNReal.ofReal w.re * s⁻¹) (hu : eLpNorm u s ρ ≤ 1) :
    eLpNorm (u.map (powSign w)) t ρ ≤ 1 :=
  (eLpNorm_le_eLpNorm_rpow hw (u.map _).aestronglyMeasurable ht
    (ae_of_all _ fun x => norm_powSign_le w (u x))).trans (ENNReal.rpow_le_one hu hw)

/-- A fibre indicator of a simple function is in `Lᵗ` as soon as some member `u_w` of the
analytic family through `u` is. -/
theorem memLp_fiberInd (u : SimpleFunc γ ℂ) {t : ℝ≥0∞} {w c : ℂ} (hc : c ≠ 0)
    (hu : MemLp (u.map (powSign w)) t ρ) : MemLp (fiberInd u c) t ρ := by
  have hne : powSign w c ≠ 0 := by
    have : (c / (‖c‖ : ℂ)) ≠ 0 := div_ne_zero hc (ofReal_ne_zero.2 (norm_ne_zero_iff.2 hc))
    simpa [powSign] using this
  refine hu.of_le_mul (fiberInd u c).aestronglyMeasurable (c := ‖powSign w c‖⁻¹)
    (ae_of_all _ fun x => ?_)
  rw [fiberInd_apply, SimpleFunc.map_apply]
  split_ifs with h
  · rw [h, norm_one, inv_mul_cancel₀ (norm_ne_zero_iff.2 hne)]
  · simp only [norm_zero]
    positivity

/-- On the line `Re z = 0` the analytic family through `u` lies in the unit ball of `L^{s₀}`. -/
theorem eLpNorm_map_powSign_expo_le_one_of_re_eq_zero (u : SimpleFunc γ ℂ)
    {s₀ s₁ s : ℝ≥0∞} (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹)
    (hu : eLpNorm u s ρ ≤ 1) {z : ℂ} (hz : z.re = 0) :
    eLpNorm (u.map (powSign (expo (s₀⁻¹).toReal (s₁⁻¹).toReal θ z))) s₀ ρ ≤ 1 := by
  have hz' : z.re ∈ Set.Icc (0 : ℝ) 1 := by simp [hz]
  refine eLpNorm_map_powSign_le_one u (re_expo_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    hθ hz') ?_ hu
  rw [ofReal_re_expo_mul_inv hs₀ hs₁ hθ hs hz', hz]
  simp

/-- On the line `Re z = 1` the analytic family through `u` lies in the unit ball of `L^{s₁}`. -/
theorem eLpNorm_map_powSign_expo_le_one_of_re_eq_one (u : SimpleFunc γ ℂ)
    {s₀ s₁ s : ℝ≥0∞} (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹)
    (hu : eLpNorm u s ρ ≤ 1) {z : ℂ} (hz : z.re = 1) :
    eLpNorm (u.map (powSign (expo (s₀⁻¹).toReal (s₁⁻¹).toReal θ z))) s₁ ρ ≤ 1 := by
  have hz' : z.re ∈ Set.Icc (0 : ℝ) 1 := by simp [hz]
  refine eLpNorm_map_powSign_le_one u (re_expo_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    hθ hz') ?_ hu
  rw [ofReal_re_expo_mul_inv hs₀ hs₁ hθ hs hz', hz]
  simp

/-- The analytic family through `u` passes through `u` at `w = 1`. -/
theorem map_powSign_one (u : SimpleFunc γ ℂ) : u.map (powSign 1) = u :=
  SimpleFunc.ext fun x => powSign_one (u x)


end MeasureTheory.SimpleFunc
