/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.Complex.Hadamard
import TauCeti.Data.ENNReal.InterpolatedExponent
import TauCeti.MeasureTheory.Function.Lp.Duality
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent
import TauCeti.MeasureTheory.Function.SimpleFunc

/-!
# The Riesz–Thorin interpolation theorem

Let `T` be a complex-linear operator from simple functions on `(α, μ)` to measurable functions on
`(β, ν)`, bounded from `L^{p₀}` to `L^{q₀}` with norm `M₀` and from `L^{p₁}` to `L^{q₁}` with
norm `M₁`. For `0 < θ < 1` define the intermediate exponents by

`1 / p = (1 - θ) / p₀ + θ / p₁` and `1 / q = (1 - θ) / q₀ + θ / q₁`.

Then `‖T f‖_q ≤ M₀ ^ (1 - θ) M₁ ^ θ ‖f‖_p` for every simple `f`
(`TauCeti.eLpNorm_le_rpow_mul_rpow_mul_eLpNorm`). The exponents are arbitrary in `(0, ∞]` on
the source side (an exponent `0` makes the statement trivial) and in `[1, ∞]` on the target
side, and the constant is the weighted geometric mean of the two endpoint norms. The scalars
are complex: for real scalars the bound holds in general only up to a factor `2`. The target
measure is σ-finite, an assumption only needed for an infinite target exponent `q`; for `q < ∞`
the theorem holds on an arbitrary measure space
(`TauCeti.eLpNorm_le_rpow_mul_rpow_mul_eLpNorm_of_ne_top`).

Compared with Marcinkiewicz interpolation, the theorem asks for strong-type bounds at both
endpoints, but it loses nothing in the constant and lets the source and target exponents move
independently. Its standard consequences, the Hausdorff–Young inequality and Young's convolution
inequality, both use an endpoint `∞`, which is why the exponents are not restricted to be finite.

## The proof

This is Thorin's complex method. By duality against simple functions
(`MeasureTheory.MemLp.eLpNorm_le_of_forall_enorm_integral_mul_le`), it suffices to bound
`|∫ T f · g|` for simple `f` with `‖f‖_p ≤ 1` and simple `g` with `‖g‖_{q'} ≤ 1`, where `q'` is
the conjugate exponent. Embed `f` and `g` in the analytic families

`f_z = sgn(f) |f| ^ {P(z)}`, `g_z = sgn(g) |g| ^ {Q(z)}`,

with affine exponents `P`, `Q` normalized so that `P(θ) = Q(θ) = 1`. Because `f` and `g` take
finitely many values and `T` is linear, `Φ(z) = ∫ T f_z · g_z` is a finite sum of exponentials in
`z`; it is entire and bounded on the strip `0 ≤ Re z ≤ 1`. On the line `Re z = 0` the functions
`f_z` and `g_z` have norm at most one in `L^{p₀}` and `L^{q₀'}`, so `|Φ| ≤ M₀` there by Hölder's
inequality, and likewise `|Φ| ≤ M₁` on `Re z = 1`. Hadamard's three-lines theorem
(`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'`) gives
`|∫ T f · g| = |Φ(θ)| ≤ M₀ ^ (1 - θ) M₁ ^ θ`.

## References

* M. Riesz, *Sur les maxima des formes bilinéaires et sur les fonctionnelles linéaires*,
  Acta Math. 49 (1927).
* G. O. Thorin, *An extension of a convexity theorem due to M. Riesz*, Kungl. Fysiogr. Sällsk.
  i Lund Förh. 8 (1939).
* L. Grafakos, *Classical Fourier Analysis*, Theorem 1.3.4.
* E. M. Stein, G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Chapter V,
  Theorem 1.3.
-/

public section

open MeasureTheory Filter Complex
open scoped ENNReal NNReal

namespace TauCeti

variable {α β γ ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {μ : Measure α} {ν : Measure β} {ρ : Measure γ}

namespace RieszThorin

/-- `powSign w c = (c / |c|) |c| ^ w`, with `powSign w 0 = 0`. -/
private noncomputable def powSign (w c : ℂ) : ℂ := c / (‖c‖ : ℂ) * exp (w * (Real.log ‖c‖ : ℂ))

private theorem powSign_one (c : ℂ) : powSign 1 c = c := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [powSign]
  · have hpos : 0 < ‖c‖ := norm_pos_iff.2 hc
    rw [powSign, one_mul, ← ofReal_exp, Real.exp_log hpos,
      div_mul_cancel₀ _ (ofReal_ne_zero.2 hpos.ne')]

private theorem powSign_zero_right (w : ℂ) : powSign w 0 = 0 := by simp [powSign]

private theorem norm_powSign_le (w c : ℂ) : ‖powSign w c‖ ≤ ‖c‖ ^ w.re := by
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
private noncomputable def slope (a₀ a₁ θ : ℝ) : ℝ := (a₁ - a₀) / ((1 - θ) * a₀ + θ * a₁)

/-- The exponent of the analytic family, `1 + (z - θ) (a₁ - a₀) / a`. It equals `1` at `z = θ`,
and its real part is `a₀ / a` on the line `Re z = 0` and `a₁ / a` on the line `Re z = 1`. If
`a = 0` then `a₀ = a₁ = 0` and the exponent is constantly `1`. -/
private noncomputable def expo (a₀ a₁ θ : ℝ) (z : ℂ) : ℂ := 1 + (z - θ) * (slope a₀ a₁ θ : ℂ)

private theorem re_expo (a₀ a₁ θ : ℝ) (z : ℂ) :
    (expo a₀ a₁ θ z).re = 1 + (z.re - θ) * slope a₀ a₁ θ := by
  simp [expo]

private theorem expo_self (a₀ a₁ θ : ℝ) : expo a₀ a₁ θ θ = 1 := by simp [expo]

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
private theorem norm_powSign_expo_le {a₀ a₁ θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) {z : ℂ}
    (hz : z.re ∈ Set.Icc (0 : ℝ) 1) (c : ℂ) :
    ‖powSign (expo a₀ a₁ θ z) c‖ ≤ Real.exp ((1 + |slope a₀ a₁ θ|) * |Real.log ‖c‖|) :=
  (norm_powSign_le_exp _ _).trans (Real.exp_le_exp.2
    (mul_le_mul_of_nonneg_right (abs_re_expo_le hθ hz) (abs_nonneg _)))

/-- The indicator of the fibre `u ⁻¹' {c}` of a simple function. -/
private noncomputable def fiberInd (u : SimpleFunc γ ℂ) (c : ℂ) : SimpleFunc γ ℂ :=
  (SimpleFunc.const γ (1 : ℂ)).restrict (u ⁻¹' {c})

private theorem fiberInd_apply (u : SimpleFunc γ ℂ) (c : ℂ) (x : γ) :
    fiberInd u c x = if u x = c then 1 else 0 := by
  simp only [fiberInd, SimpleFunc.restrict_apply _ (u.measurableSet_fiber c), SimpleFunc.coe_const]
  by_cases h : u x = c <;> simp [h]

private theorem smul_fiberInd (u : SimpleFunc γ ℂ) (a c : ℂ) :
    a • fiberInd u c = (SimpleFunc.const γ a).restrict (u ⁻¹' {c}) := by
  ext x
  simp [fiberInd_apply, SimpleFunc.restrict_apply _ (u.measurableSet_fiber c), Set.indicator]

private theorem map_eq_sum (u : SimpleFunc γ ℂ) (ψ : ℂ → ℂ) :
    u.map ψ = ∑ c ∈ u.range, ψ c • fiberInd u c := by
  simp_rw [smul_fiberInd]
  exact u.map_eq_sum_restrict_const ψ

private theorem map_apply_eq_sum (u : SimpleFunc γ ℂ) (ψ : ℂ → ℂ) (x : γ) :
    u.map ψ x = ∑ c ∈ u.range, ψ c * fiberInd u c x := by
  rw [u.map_apply_eq_sum_restrict_const]
  simp_rw [← smul_fiberInd, SimpleFunc.smul_apply, smul_eq_mul]

private theorem integral_map_powSign_eq_sum (T : SimpleFunc α ℂ →ₗ[ℂ] (β →ₘ[ν] ℂ))
    (f : SimpleFunc α ℂ) (g : SimpleFunc β ℂ) (w w' : ℂ)
    (hint : ∀ c ∈ f.range, c ≠ 0 → ∀ d ∈ g.range, d ≠ 0 →
      Integrable (fun y => T (fiberInd f c) y * fiberInd g d y) ν) :
    ∫ y, T (f.map (powSign w)) y * g.map (powSign w') y ∂ν =
      ∑ c ∈ f.range, ∑ d ∈ g.range,
        powSign w c * powSign w' d * ∫ y, T (fiberInd f c) y * fiberInd g d y ∂ν := by
  have hT : ⇑(T (f.map (powSign w))) =ᵐ[ν]
      fun y => ∑ c ∈ f.range, powSign w c * T (fiberInd f c) y := by
    rw [map_eq_sum, map_sum]
    simp_rw [map_smul]
    filter_upwards [(AEEqFun.coeFn_finsetSum _ _).trans
      (eventuallyEq_sum fun c _ => AEEqFun.coeFn_smul (powSign w c) (T (fiberInd f c)))]
      with y hy
    rw [hy, Finset.sum_apply]
    simp_rw [Pi.smul_apply, smul_eq_mul]
  -- Each term is integrable: it vanishes unless `c ≠ 0` and `d ≠ 0`.
  have hterm : ∀ c ∈ f.range, ∀ d ∈ g.range, Integrable (fun y =>
      powSign w c * powSign w' d * (T (fiberInd f c) y * fiberInd g d y)) ν := by
    intro c hc d hd
    rcases eq_or_ne c 0 with rfl | hc0
    · simp [powSign_zero_right]
    rcases eq_or_ne d 0 with rfl | hd0
    · simp [powSign_zero_right]
    exact (hint c hc hc0 d hd hd0).const_mul _
  calc ∫ y, T (f.map (powSign w)) y * g.map (powSign w') y ∂ν
      = ∫ y, ∑ c ∈ f.range, ∑ d ∈ g.range,
          powSign w c * powSign w' d * (T (fiberInd f c) y * fiberInd g d y) ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards [hT] with y hy
        rw [hy, map_apply_eq_sum g, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
    _ = ∑ c ∈ f.range, ∑ d ∈ g.range,
          powSign w c * powSign w' d * ∫ y, T (fiberInd f c) y * fiberInd g d y ∂ν := by
        rw [integral_finsetSum _ fun c hc => integrable_finsetSum _ fun d hd => hterm c hc d hd]
        refine Finset.sum_congr rfl fun c hc => ?_
        rw [integral_finsetSum _ fun d hd => hterm c hc d hd]
        exact Finset.sum_congr rfl fun d _ => integral_const_mul _ _

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

/-- The member `u_w = sgn(u) |u| ^ w` of the analytic family through `u` has `Lᵗ` norm at most
one, where `1 / t = Re w / s`, whenever `u` has `Lˢ` norm at most one. -/
private theorem eLpNorm_map_powSign_le_one (u : SimpleFunc γ ℂ) {s t : ℝ≥0∞} {w : ℂ}
    (hw : 0 ≤ w.re) (ht : t⁻¹ = ENNReal.ofReal w.re * s⁻¹) (hu : eLpNorm u s ρ ≤ 1) :
    eLpNorm (u.map (powSign w)) t ρ ≤ 1 :=
  (eLpNorm_le_eLpNorm_rpow hw u.aestronglyMeasurable (u.map _).aestronglyMeasurable ht
    (ae_of_all _ fun x => norm_powSign_le w (u x))).trans (ENNReal.rpow_le_one hu hw)

/-- A fibre indicator of a simple function is in `Lᵗ` as soon as some member `u_w` of the
analytic family through `u` is. -/
private theorem memLp_fiberInd (u : SimpleFunc γ ℂ) {t : ℝ≥0∞} {w c : ℂ} (hc : c ≠ 0)
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
private theorem eLpNorm_map_powSign_expo_le_one_of_re_eq_zero (u : SimpleFunc γ ℂ)
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
private theorem eLpNorm_map_powSign_expo_le_one_of_re_eq_one (u : SimpleFunc γ ℂ)
    {s₀ s₁ s : ℝ≥0∞} (hs₀ : s₀ ≠ 0) (hs₁ : s₁ ≠ 0) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hs : s⁻¹ = ENNReal.ofReal (1 - θ) * s₀⁻¹ + ENNReal.ofReal θ * s₁⁻¹)
    (hu : eLpNorm u s ρ ≤ 1) {z : ℂ} (hz : z.re = 1) :
    eLpNorm (u.map (powSign (expo (s₀⁻¹).toReal (s₁⁻¹).toReal θ z))) s₁ ρ ≤ 1 := by
  have hz' : z.re ∈ Set.Icc (0 : ℝ) 1 := by simp [hz]
  refine eLpNorm_map_powSign_le_one u (re_expo_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    hθ hz') ?_ hu
  rw [ofReal_re_expo_mul_inv hs₀ hs₁ hθ hs hz', hz]
  simp

private theorem map_powSign_one (u : SimpleFunc γ ℂ) : u.map (powSign 1) = u :=
  SimpleFunc.ext fun x => powSign_one (u x)

/-- One boundary line of the strip: if `T` is bounded from `L^{s}` to `L^{t}` with norm `M`, and
`u`, `v` have norm at most one in `L^{s}` and in the dual exponent `L^{t'}`, the pairing
`∫ T u · v` is at most `M`. -/
private theorem norm_integral_mul_le_of_eLpNorm_le_one (T : SimpleFunc α ℂ →ₗ[ℂ] (β →ₘ[ν] ℂ))
    {s t t' : ℝ≥0∞} [t.HolderConjugate t'] {M : ℝ≥0}
    (hT : ∀ f, eLpNorm (T f) t ν ≤ M * eLpNorm f s μ) {u : SimpleFunc α ℂ}
    {v : SimpleFunc β ℂ} (hu : eLpNorm u s μ ≤ 1) (hv : eLpNorm v t' ν ≤ 1) :
    ‖∫ y, T u y * v y ∂ν‖ ≤ M := by
  have h : ‖∫ y, T u y * v y ∂ν‖ₑ ≤ M := by
    calc ‖∫ y, T u y * v y ∂ν‖ₑ ≤ eLpNorm (T u) t ν * eLpNorm v t' ν :=
          enorm_integral_mul_le (T u).aestronglyMeasurable v.aestronglyMeasurable
      _ ≤ (M * eLpNorm u s μ) * 1 := by gcongr; exact hT u
      _ ≤ M * 1 * 1 := by gcongr
      _ = M := by simp
  exact_mod_cast enorm_le_coe.1 h

/-- **The three-lines estimate.** For simple `f`, `g` of norm at most one in `Lᵖ` and in the dual
exponent `L^{q'}`, the pairing `∫ T f · g` is at most `M₀ ^ (1 - θ) M₁ ^ θ`. -/
private theorem norm_integral_mul_le_of_le_one (T : SimpleFunc α ℂ →ₗ[ℂ] (β →ₘ[ν] ℂ))
    {p₀ p₁ p q₀ q₁ q₀' q₁' q' : ℝ≥0∞} [hq₀ : q₀.HolderConjugate q₀']
    [hq₁ : q₁.HolderConjugate q₁'] (hp₀ : p₀ ≠ 0) (hp₁ : p₁ ≠ 0) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq' : q'⁻¹ = ENNReal.ofReal (1 - θ) * q₀'⁻¹ + ENNReal.ofReal θ * q₁'⁻¹) {M₀ M₁ : ℝ≥0}
    (h₀ : ∀ f, eLpNorm (T f) q₀ ν ≤ M₀ * eLpNorm f p₀ μ)
    (h₁ : ∀ f, eLpNorm (T f) q₁ ν ≤ M₁ * eLpNorm f p₁ μ) {f : SimpleFunc α ℂ}
    {g : SimpleFunc β ℂ} (hf : eLpNorm f p μ ≤ 1) (hg : eLpNorm g q' ν ≤ 1) :
    ‖∫ y, T f y * g y ∂ν‖ ≤ (M₀ : ℝ) ^ (1 - θ) * (M₁ : ℝ) ^ θ := by
  have hq₀' : q₀' ≠ 0 := hq₀.symm.ne_zero
  have hq₁' : q₁' ≠ 0 := hq₁.symm.ne_zero
  set P := expo (p₀⁻¹).toReal (p₁⁻¹).toReal θ with hP
  set Q := expo (q₀'⁻¹).toReal (q₁'⁻¹).toReal θ with hQ
  -- The fibre indicators of `f` and `g` lie in the endpoint spaces, so the pairing of the two
  -- analytic families expands into a finite exponential sum `Φ`.
  have hint : ∀ c ∈ f.range, c ≠ 0 → ∀ d ∈ g.range, d ≠ 0 →
      Integrable (fun y => T (fiberInd f c) y * fiberInd g d y) ν := by
    intro c _ hc d _ hd
    have hχ : MemLp (fiberInd f c) p₀ μ := memLp_fiberInd f (w := P 0) hc <| memLp_iff.2 <|
      (eLpNorm_map_powSign_expo_le_one_of_re_eq_zero f hp₀ hp₁ hθ hp hf (by simp)).trans_lt
        ENNReal.one_lt_top
    have hTχ : MemLp (T (fiberInd f c)) q₀ ν :=
      memLp_iff.2 ((h₀ _).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hχ.eLpNorm_lt_top))
    have hχ' : MemLp (fiberInd g d) q₀' ν := memLp_fiberInd g (w := Q 0) hd <| memLp_iff.2 <|
      (eLpNorm_map_powSign_expo_le_one_of_re_eq_zero g hq₀' hq₁' hθ hq' hg (by simp)).trans_lt
        ENNReal.one_lt_top
    exact hTχ.integrable_mul hχ'
  set I : ℂ → ℂ → ℂ := fun c d => ∫ y, T (fiberInd f c) y * fiberInd g d y ∂ν
  set Φ : ℂ → ℂ := fun z =>
    ∑ c ∈ f.range, ∑ d ∈ g.range, powSign (P z) c * powSign (Q z) d * I c d with hΦ_def
  have hΦ : ∀ z, Φ z = ∫ y, T (f.map (powSign (P z))) y * g.map (powSign (Q z)) y ∂ν :=
    fun z => (integral_map_powSign_eq_sum T f g _ _ hint).symm
  have hdiff : Differentiable ℂ Φ := by
    simp only [hΦ_def, hP, hQ, expo, powSign]
    fun_prop
  have hbdd : BddAbove ((norm ∘ Φ) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨∑ c ∈ f.range, ∑ d ∈ g.range,
      Real.exp ((1 + |slope (p₀⁻¹).toReal (p₁⁻¹).toReal θ|) * |Real.log ‖c‖|) *
        Real.exp ((1 + |slope (q₀'⁻¹).toReal (q₁'⁻¹).toReal θ|) * |Real.log ‖d‖|) * ‖I c d‖, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hz : z.re ∈ Set.Icc (0 : ℝ) 1 := hz
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun d _ => ?_))
    rw [norm_mul, norm_mul]
    gcongr
    · exact norm_powSign_expo_le hθ hz c
    · exact norm_powSign_expo_le hθ hz d
  -- On the two boundary lines, the endpoint bounds control `Φ`.
  have hb₀ : ∀ z ∈ re ⁻¹' {(0 : ℝ)}, ‖Φ z‖ ≤ (M₀ : ℝ) := by
    intro z hz
    rw [hΦ]
    exact norm_integral_mul_le_of_eLpNorm_le_one T h₀
      (eLpNorm_map_powSign_expo_le_one_of_re_eq_zero f hp₀ hp₁ hθ hp hf hz)
      (eLpNorm_map_powSign_expo_le_one_of_re_eq_zero g hq₀' hq₁' hθ hq' hg hz)
  have hb₁ : ∀ z ∈ re ⁻¹' {(1 : ℝ)}, ‖Φ z‖ ≤ (M₁ : ℝ) := by
    intro z hz
    rw [hΦ]
    exact norm_integral_mul_le_of_eLpNorm_le_one T h₁
      (eLpNorm_map_powSign_expo_le_one_of_re_eq_one f hp₀ hp₁ hθ hp hf hz)
      (eLpNorm_map_powSign_expo_le_one_of_re_eq_one g hq₀' hq₁' hθ hq' hg hz)
  have key := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (z := (θ : ℂ)) zero_lt_one (by simp [Complex.HadamardThreeLines.verticalClosedStrip,
      hθ.1.le, hθ.2.le]) hdiff.diffContOnCl hbdd hb₀ hb₁
  rw [hΦ, hP, hQ, expo_self, expo_self, map_powSign_one, map_powSign_one] at key
  simpa using key

/-- The bilinear form of the three-lines estimate, for simple functions of arbitrary finite
norm. -/
private theorem enorm_integral_mul_le_mul (T : SimpleFunc α ℂ →ₗ[ℂ] (β →ₘ[ν] ℂ))
    {p₀ p₁ p q₀ q₁ q₀' q₁' q' : ℝ≥0∞} [hq₀ : q₀.HolderConjugate q₀']
    [hq₁ : q₁.HolderConjugate q₁'] (hp₀ : p₀ ≠ 0) (hp₁ : p₁ ≠ 0) (hp : p ≠ 0) (hq'0 : q' ≠ 0)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hpθ : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq' : q'⁻¹ = ENNReal.ofReal (1 - θ) * q₀'⁻¹ + ENNReal.ofReal θ * q₁'⁻¹) {M₀ M₁ : ℝ≥0}
    (h₀ : ∀ f, eLpNorm (T f) q₀ ν ≤ M₀ * eLpNorm f p₀ μ)
    (h₁ : ∀ f, eLpNorm (T f) q₁ ν ≤ M₁ * eLpNorm f p₁ μ) {f : SimpleFunc α ℂ}
    {g : SimpleFunc β ℂ} (hf : eLpNorm f p μ ≠ ∞) (hg : eLpNorm g q' ν ≠ ∞) :
    ‖∫ y, T f y * g y ∂ν‖ₑ ≤ ↑(M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p μ * eLpNorm g q' ν := by
  rcases eq_or_ne (eLpNorm f p μ) 0 with hf0 | hf0
  · -- `f = 0` almost everywhere, hence so is `T f`.
    have hf0' : f =ᵐ[μ] 0 := (eLpNorm_eq_zero_iff hp).1 hf0
    have hT0 : eLpNorm (T f) q₀ ν = 0 :=
      nonpos_iff_eq_zero.1 ((h₀ f).trans_eq (by rw [eLpNorm_congr_ae hf0']; simp))
    have hT0' : ⇑(T f) =ᵐ[ν] 0 := (eLpNorm_eq_zero_iff hq₀.ne_zero).1 hT0
    rw [integral_eq_zero_of_ae (hT0'.mono fun y hy => by simp [hy])]
    simp
  rcases eq_or_ne (eLpNorm g q' ν) 0 with hg0 | hg0
  · have hg0' : g =ᵐ[ν] 0 := (eLpNorm_eq_zero_iff hq'0).1 hg0
    rw [integral_eq_zero_of_ae (hg0'.mono fun y hy => by simp [hy])]
    simp
  -- Normalize `f` and `g`.
  set a := (eLpNorm f p μ).toReal
  set b := (eLpNorm g q' ν).toReal
  have ha : 0 < a := ENNReal.toReal_pos hf0 hf
  have hb : 0 < b := ENNReal.toReal_pos hg0 hg
  have hfa : eLpNorm (((a⁻¹ : ℝ) : ℂ) • f) p μ ≤ 1 := by
    rw [SimpleFunc.coe_smul, eLpNorm_const_smul, ← ofReal_norm, norm_real,
      Real.norm_of_nonneg (inv_nonneg.2 ha.le), ENNReal.ofReal_inv_of_pos ha,
      ENNReal.ofReal_toReal hf, ENNReal.inv_mul_cancel hf0 hf]
  have hgb : eLpNorm (((b⁻¹ : ℝ) : ℂ) • g) q' ν ≤ 1 := by
    rw [SimpleFunc.coe_smul, eLpNorm_const_smul, ← ofReal_norm, norm_real,
      Real.norm_of_nonneg (inv_nonneg.2 hb.le), ENNReal.ofReal_inv_of_pos hb,
      ENNReal.ofReal_toReal hg, ENNReal.inv_mul_cancel hg0 hg]
  have key := norm_integral_mul_le_of_le_one T hp₀ hp₁ hθ hpθ hq' h₀ h₁ hfa hgb
  have hscale : ∫ y, T (((a⁻¹ : ℝ) : ℂ) • f) y * ((((b⁻¹ : ℝ) : ℂ) • g) y) ∂ν =
      ((a⁻¹ * b⁻¹ : ℝ) : ℂ) * ∫ y, T f y * g y ∂ν := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [show ⇑(T (((a⁻¹ : ℝ) : ℂ) • f)) =ᵐ[ν] ((a⁻¹ : ℝ) : ℂ) • ⇑(T f) by
      rw [map_smul]; exact AEEqFun.coeFn_smul _ _] with y hy
    rw [hy, SimpleFunc.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  rw [hscale, norm_mul, norm_real, Real.norm_of_nonneg (by positivity)] at key
  have hle : ‖∫ y, T f y * g y ∂ν‖ ≤ (M₀ : ℝ) ^ (1 - θ) * (M₁ : ℝ) ^ θ * a * b := by
    refine ((le_div_iff₀' (by positivity)).2 key).trans_eq ?_
    rw [div_eq_mul_inv, mul_inv, inv_inv, inv_inv]
    ring
  calc ‖∫ y, T f y * g y ∂ν‖ₑ = ENNReal.ofReal ‖∫ y, T f y * g y ∂ν‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal ((M₀ : ℝ) ^ (1 - θ) * (M₁ : ℝ) ^ θ * a * b) := ENNReal.ofReal_le_ofReal hle
    _ = ↑(M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p μ * eLpNorm g q' ν := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_toReal hf, ENNReal.ofReal_toReal hg]
        congr
        rw [← NNReal.coe_rpow, ← NNReal.coe_rpow, ← NNReal.coe_mul, ENNReal.ofReal_coe_nnreal]

/-- The Riesz–Thorin bound, assuming `ν` σ-finite only when the target exponent `q` is infinite,
which is where the duality against simple functions needs it. -/
private theorem eLpNorm_le_of_ne_top_or_sigmaFinite
    {T : SimpleFunc α ℂ →ₗ[ℂ] (β →ₘ[ν] ℂ)} {p₀ p₁ p q₀ q₁ q : ℝ≥0∞} (hq₀ : 1 ≤ q₀)
    (hq₁ : 1 ≤ q₁) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹)
    (hν : q ≠ ∞ ∨ SigmaFinite ν) {M₀ M₁ : ℝ≥0}
    (h₀ : ∀ f, eLpNorm (T f) q₀ ν ≤ M₀ * eLpNorm f p₀ μ)
    (h₁ : ∀ f, eLpNorm (T f) q₁ ν ≤ M₁ * eLpNorm f p₁ μ) (f : SimpleFunc α ℂ) :
    eLpNorm (T f) q ν ≤ ↑(M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p μ := by
  have hθ' := Set.Ioo_subset_Icc_self hθ
  have hq1 := one_le_of_inv_eq hq₀ hq₁ hθ' hq
  have hq' := inv_conjExponent_eq_of_inv_eq hq₀ hq₁ hθ' hq
  have := ENNReal.HolderConjugate.conjExponent hq₀
  have := ENNReal.HolderConjugate.conjExponent hq₁
  have := ENNReal.HolderConjugate.conjExponent hq1
  have hq₀0 : q₀ ≠ 0 := (zero_lt_one.trans_le hq₀).ne'
  have hq₁0 : q₁ ≠ 0 := (zero_lt_one.trans_le hq₁).ne'
  -- A source exponent `0` makes the corresponding endpoint bound force `T f = 0`.
  rcases eq_or_ne p₀ 0 with rfl | hp₀
  · have hT : ⇑(T f) =ᵐ[ν] 0 :=
      (eLpNorm_eq_zero_iff hq₀0).1 (nonpos_iff_eq_zero.1
        ((h₀ f).trans_eq (by rw [eLpNorm_exponent_zero f.aestronglyMeasurable, mul_zero])))
    rw [eLpNorm_congr_ae hT]
    simp
  rcases eq_or_ne p₁ 0 with rfl | hp₁
  · have hT : ⇑(T f) =ᵐ[ν] 0 :=
      (eLpNorm_eq_zero_iff hq₁0).1 (nonpos_iff_eq_zero.1
        ((h₁ f).trans_eq (by rw [eLpNorm_exponent_zero f.aestronglyMeasurable, mul_zero])))
    rw [eLpNorm_congr_ae hT]
    simp
  -- If `M₀ ^ (1 - θ) M₁ ^ θ = 0`, one endpoint bound already forces `T f = 0`.
  by_cases hM : M₀ ^ (1 - θ) * M₁ ^ θ = 0
  · have hT : ⇑(T f) =ᵐ[ν] 0 := by
      rcases mul_eq_zero.1 hM with h | h
      · have hM₀ : M₀ = 0 := (NNReal.rpow_eq_zero_iff.1 h).1
        exact (eLpNorm_eq_zero_iff hq₀0).1 (nonpos_iff_eq_zero.1 ((h₀ f).trans_eq (by simp [hM₀])))
      · have hM₁ : M₁ = 0 := (NNReal.rpow_eq_zero_iff.1 h).1
        exact (eLpNorm_eq_zero_iff hq₁0).1 (nonpos_iff_eq_zero.1 ((h₁ f).trans_eq (by simp [hM₁])))
    rw [eLpNorm_congr_ae hT]
    simp
  rcases eq_or_ne (eLpNorm f p μ) ∞ with hf | hf
  · rw [hf, ENNReal.mul_top (by exact_mod_cast hM)]
    exact le_top
  have hp0 : p ≠ 0 := by
    rw [← ENNReal.inv_ne_top, inv_eq_ofReal_of_inv_eq hp₀ hp₁ hθ' hp]
    exact ENNReal.ofReal_ne_top
  -- The simple function `f` lies in both source spaces: its fibres have finite measure when
  -- `p < ∞`, and `p = ∞` forces `p₀ = p₁ = ∞`.
  obtain ⟨hf₀, hf₁⟩ : MemLp f p₀ μ ∧ MemLp f p₁ μ := by
    rcases eq_or_ne p ∞ with hptop | hptop
    · obtain ⟨rfl, rfl⟩ := (eq_top_iff_of_inv_eq hθ hp).1 hptop
      exact ⟨f.memLp_top μ, f.memLp_top μ⟩
    · have hfib := SimpleFunc.measure_preimage_lt_top_of_memLp hp0 hptop f (memLp_iff.2 hf.lt_top)
      exact ⟨SimpleFunc.memLp_of_finite_measure_preimage p₀ hfib,
        SimpleFunc.memLp_of_finite_measure_preimage p₁ hfib⟩
  -- `T f` lies in both target spaces, hence in the intermediate one.
  have hT₀ : MemLp (T f) q₀ ν :=
    memLp_iff.2 ((h₀ f).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf₀.eLpNorm_lt_top))
  have hT₁ : MemLp (T f) q₁ ν :=
    memLp_iff.2 ((h₁ f).trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf₁.eLpNorm_lt_top))
  have hTq : MemLp (T f) q ν := by
    rcases Set.mem_uIcc.1 (mem_uIcc_of_inv_eq hq₀0 hq₁0 hθ' hq) with ⟨h₁', h₂'⟩ | ⟨h₁', h₂'⟩
    · exact hT₀.of_le_of_le hT₁ hq₀0 h₁' h₂'
    · exact hT₁.of_le_of_le hT₀ hq₁0 h₁' h₂'
  -- Duality reduces the bound to the bilinear estimate.
  have key : ∀ g : SimpleFunc β ℂ, MemLp g q.conjExponent ν →
      ‖∫ y, T f y * g y ∂ν‖ₑ ≤ ↑(M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p μ *
        eLpNorm g q.conjExponent ν := fun g hg =>
    enorm_integral_mul_le_mul T hp₀ hp₁ hp0 (ENNReal.HolderConjugate.ne_zero _ q) hθ hp hq'
      h₀ h₁ hf hg.eLpNorm_lt_top.ne
  rcases hν with hqtop | hν
  · exact hTq.eLpNorm_le_of_forall_enorm_integral_mul_le_of_ne_top hqtop key
  · exact hTq.eLpNorm_le_of_forall_enorm_integral_mul_le key

end RieszThorin

open RieszThorin in
/-- **The Riesz–Thorin interpolation theorem.** Let `T` be a complex-linear map from simple
functions on `(α, μ)` to almost-everywhere classes on a σ-finite `(β, ν)` with
`‖T f‖_{q₀} ≤ M₀ ‖f‖_{p₀}` and `‖T f‖_{q₁} ≤ M₁ ‖f‖_{p₁}` for all simple `f`, where
`p₀, p₁ ∈ [0, ∞]` and `1 ≤ q₀, q₁ ≤ ∞`. For `0 < θ < 1` and the intermediate exponents
`1 / p = (1 - θ) / p₀ + θ / p₁`, `1 / q = (1 - θ) / q₀ + θ / q₁`,

`‖T f‖_q ≤ M₀ ^ (1 - θ) M₁ ^ θ ‖f‖_p`

for every simple `f`. σ-finiteness of `ν` is only used when `q = ∞`; for `q < ∞` see
`TauCeti.eLpNorm_le_rpow_mul_rpow_mul_eLpNorm_of_ne_top`. -/
theorem eLpNorm_le_rpow_mul_rpow_mul_eLpNorm [SigmaFinite ν]
    {T : SimpleFunc α ℂ →ₗ[ℂ] (β →ₘ[ν] ℂ)} {p₀ p₁ p q₀ q₁ q : ℝ≥0∞} (hq₀ : 1 ≤ q₀)
    (hq₁ : 1 ≤ q₁) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) {M₀ M₁ : ℝ≥0}
    (h₀ : ∀ f, eLpNorm (T f) q₀ ν ≤ M₀ * eLpNorm f p₀ μ)
    (h₁ : ∀ f, eLpNorm (T f) q₁ ν ≤ M₁ * eLpNorm f p₁ μ) (f : SimpleFunc α ℂ) :
    eLpNorm (T f) q ν ≤ ↑(M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p μ :=
  eLpNorm_le_of_ne_top_or_sigmaFinite hq₀ hq₁ hθ hp hq (Or.inr ‹_›) h₀ h₁ f

open RieszThorin in
/-- **The Riesz–Thorin interpolation theorem** for a finite target exponent, on an arbitrary
measure space `(β, ν)`: under the hypotheses of `TauCeti.eLpNorm_le_rpow_mul_rpow_mul_eLpNorm`,
if the intermediate exponent `q` is finite then `‖T f‖_q ≤ M₀ ^ (1 - θ) M₁ ^ θ ‖f‖_p` for every
simple `f`, without assuming `ν` σ-finite. -/
theorem eLpNorm_le_rpow_mul_rpow_mul_eLpNorm_of_ne_top
    {T : SimpleFunc α ℂ →ₗ[ℂ] (β →ₘ[ν] ℂ)} {p₀ p₁ p q₀ q₁ q : ℝ≥0∞} (hq₀ : 1 ≤ q₀)
    (hq₁ : 1 ≤ q₁) {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹)
    (hq : q⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * q₁⁻¹) (hqtop : q ≠ ∞)
    {M₀ M₁ : ℝ≥0} (h₀ : ∀ f, eLpNorm (T f) q₀ ν ≤ M₀ * eLpNorm f p₀ μ)
    (h₁ : ∀ f, eLpNorm (T f) q₁ ν ≤ M₁ * eLpNorm f p₁ μ) (f : SimpleFunc α ℂ) :
    eLpNorm (T f) q ν ≤ ↑(M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f p μ :=
  eLpNorm_le_of_ne_top_or_sigmaFinite hq₀ hq₁ hθ hp hq (Or.inl hqtop) h₀ h₁ f

end TauCeti
