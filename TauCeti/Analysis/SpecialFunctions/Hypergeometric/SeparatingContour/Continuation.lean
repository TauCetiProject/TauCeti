/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.SeparatingContour.Analyticity
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic

/-!
# Mellin–Barnes continuation of Euler's integral and the Gauss hypergeometric function

This module relates the separating-contour Mellin–Barnes integral `Complex.mellinBarnesIntegral`
(and hence `Complex.mellinBarnesSeparatingIntegral` at every admissible abscissa `σ < 0`), which
represents `Γ(a) Γ(b) 𝐅(a, b; c; z)` (and hence `(Γ(a) Γ(b) / Γ(c)) ₂F₁(a, b; c; z)`), to Euler's
normalized integral `Complex.eulerIntegral`, the regularized Gauss hypergeometric function
`Complex.regularizedGaussHGFun`, and the ordinary Gauss hypergeometric function
`ordinaryHypergeometric` (`₂F₁`), establishing DLMF 15.6.6 across all non-exceptional parameters
`a, b ∉ -ℕ`, including negative real parts and integer differences `a - b ∈ ℤ`.

On the negative real half-line `z = -x` (`x > 0`) in the classical convergence region
`0 < Re a`, `0 < Re b < Re c`, an abscissa `-min (Re a) (Re b) < σ < 0` reduces the functional to
a straight vertical-line integral, and Fubini's theorem interchanges the vertical Mellin–Barnes
integral of `(1 + x t)^{-a}` (`Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_sub`) with the Beta
integral on `(0, 1)`. Combining joint holomorphy of `mellinBarnesIntegral`
(`Complex.analyticOnNhd_mellinBarnesIntegral`), `eulerIntegral`
(`Complex.analyticOnNhd_eulerIntegral`), and `regularizedGaussHGFun`
(`Complex.analyticAt_uncurry_regularizedGaussHGFun`) with the slit-plane identity theorem
(`AnalyticOnNhd.eqOn_slitPlane_of_ofReal_pos_eq`), `Complex.regularizedGaussHGFun_eq_eulerIntegral`,
and identity continuation on `{w : ℂ | ∀ k : ℕ, w ≠ -k}`
(`Complex.isConnected_setOf_forall_ne_neg_natCast`) extends the representation to general
parameters.

## Main results

* `Complex.eulerIntegral_eq_mellinBarnesIntegral`,
  `Complex.eulerIntegral_eq_mellinBarnesSeparatingIntegral`: Mellin–Barnes continuation of Euler's
  integral with the `(Γ(a) Γ(b))⁻¹` prefactor for `0 < Re b < Re c`, `a ∉ -ℕ`, and
  `-z ∈ Complex.slitPlane`.
* `Complex.regularizedGaussHGFun_eq_mellinBarnesIntegral`,
  `Complex.regularizedGaussHGFun_eq_mellinBarnesSeparatingIntegral`: DLMF 15.6.6 for
  `regularizedGaussHGFun` with the `(Γ(a) Γ(b))⁻¹` prefactor across `a, b ∉ -ℕ`, arbitrary `c : ℂ`,
  `‖z‖ < 1`, and `-z ∈ slitPlane`.
* `Complex.ordinaryHypergeometric_eq_mellinBarnesIntegral`,
  `Complex.ordinaryHypergeometric_eq_mellinBarnesSeparatingIntegral`: DLMF 15.6.6 for
  `ordinaryHypergeometric` (`₂F₁`) with the `Γ(c) / (Γ(a) Γ(b))` prefactor across `a, b, c ∉ -ℕ`,
  `‖z‖ < 1`, and `-z ∈ slitPlane`.

## References

* NIST Digital Library of Mathematical Functions, §15.6(ii), equation 15.6.6.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §14.5.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 5.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Real Topology

namespace Complex

private theorem setIntegral_Ioo_zero_one_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    ∫ t in Ioo (0 : ℝ) 1, f t = ∫ t in (0 : ℝ)..1, f t := by
  rw [setIntegral_congr_set Ioo_ae_eq_Ioc, intervalIntegral.integral_of_le zero_le_one]

private theorem integrableOn_Ioo_zero_one_of_intervalIntegrable {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → E} (hf : IntervalIntegrable f volume 0 1) :
    IntegrableOn f (Ioo (0 : ℝ) 1) volume := by
  have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 hf
  rwa [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h

private def mellinBarnesFubiniKernel (a b c : ℂ) (x σ : ℝ) (t y : ℝ) : ℂ :=
  (t : ℂ) ^ (b + (σ + y * I) - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
    ((x : ℂ) ^ (σ + y * I) * (Gamma (-(σ + y * I)) * Gamma (a + (σ + y * I))))

private theorem continuousOn_mellinBarnesFubiniKernel {a b c : ℂ} {x σ : ℝ}
    (hx : 0 < x) (hσ : σ < 0) (haσ : 0 < a.re + σ) :
    ContinuousOn (Function.uncurry (mellinBarnesFubiniKernel a b c x σ))
      (Ioo (0 : ℝ) 1 ×ˢ univ) := by
  refine continuousOn_of_forall_continuousAt fun ⟨t, y⟩ ⟨ht, _⟩ => ?_
  have hs : ContinuousAt (fun p : ℝ × ℝ => (σ : ℂ) + (p.2 : ℂ) * I) (t, y) := by fun_prop
  have h1t_slit : 1 - (t : ℂ) ∈ slitPlane := by
    simpa only [ofReal_sub, ofReal_one] using ofReal_mem_slitPlane.2 (sub_pos.2 ht.2)
  have hG1 : ContinuousAt (fun p : ℝ × ℝ => Gamma (-((σ : ℂ) + p.2 * I))) (t, y) :=
    (differentiableAt_Gamma _ (ne_neg_natCast_of_re_pos (by simp; linarith))).continuousAt.comp
      hs.neg
  have hG2 : ContinuousAt (fun p : ℝ × ℝ => Gamma (a + ((σ : ℂ) + p.2 * I))) (t, y) :=
    (differentiableAt_Gamma _ (ne_neg_natCast_of_re_pos (by simp; linarith))).continuousAt.comp
      (continuousAt_const.add hs)
  exact (((ContinuousAt.cpow (by fun_prop) ((continuousAt_const.add hs).sub continuousAt_const)
      (ofReal_mem_slitPlane.2 ht.1)).mul
    (ContinuousAt.cpow (by fun_prop) continuousAt_const h1t_slit)).mul
    ((ContinuousAt.cpow continuousAt_const hs (ofReal_mem_slitPlane.2 hx)).mul (hG1.mul hG2)))

private theorem integrable_mellinBarnesFubiniKernel {a b c : ℂ} {x σ : ℝ}
    (hx : 0 < x) (hσ : σ < 0) (haσ : 0 < a.re + σ) (hbσ : 0 < b.re + σ) (hbc : b.re < c.re) :
    Integrable (Function.uncurry (mellinBarnesFubiniKernel a b c x σ))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
  let g₁ : ℝ → ℝ := fun t => ‖(t : ℂ) ^ ((b + σ : ℂ) - 1) * (1 - (t : ℂ)) ^ (c - b - 1)‖
  let g₂ : ℝ → ℝ := fun y => x ^ σ * ‖Gamma (-(σ + y * I)) * Gamma (a + (σ + y * I))‖
  have hg₁ : Integrable g₁ (volume.restrict (Ioo (0 : ℝ) 1)) :=
    (integrableOn_Ioo_zero_one_of_intervalIntegrable
      (betaIntegral_convergent (u := b + σ) (v := c - b) (by simpa using hbσ)
        (by simpa using sub_pos.2 hbc))).norm
  have hg₂ : Integrable g₂ volume := by
    have hv : Integrable (fun y : ℝ =>
        Gamma ((-σ : ℝ) + y * I) * Gamma (a - ((-σ : ℝ) + y * I))) volume :=
      verticalIntegrable_Gamma_mul_Gamma_sub (fun n _ => by linarith [n.cast_nonneg (α := ℝ)])
        (fun n _ => by linarith [n.cast_nonneg (α := ℝ)])
    refine ((hv.comp_neg.congr (Eventually.of_forall fun y => ?_)).norm.const_mul (x ^ σ))
    dsimp only
    rw [← neg_ofReal_add_mul_I, sub_neg_eq_add]
  have hmeas_prod : (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume : Measure ℝ) =
      ((volume : Measure ℝ).prod volume).restrict (Ioo (0 : ℝ) 1 ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  refine (hg₁.mul_prod hg₂).mono' (hmeas_prod ▸
    (continuousOn_mellinBarnesFubiniKernel hx hσ haσ).aestronglyMeasurable
      (measurableSet_Ioo.prod MeasurableSet.univ)) ?_
  rw [hmeas_prod]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with ⟨t, y⟩ ⟨ht, _⟩
  simp [Function.uncurry, mellinBarnesFubiniKernel, g₁, g₂, norm_cpow_eq_rpow_re_of_pos, ht.1, hx,
    mul_assoc]

private theorem integral_mellinBarnesFubiniKernel_y {a b c : ℂ} {x σ t : ℝ}
    (hx : 0 < x) (ht : t ∈ Ioo (0 : ℝ) 1) (hσ : σ < 0) (haσ : 0 < a.re + σ) :
    ∫ y : ℝ, mellinBarnesFubiniKernel a b c x σ t y =
      2 * π * Gamma a * ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (1 - (-(x : ℂ)) * (t : ℂ)) ^ (-a)) := by
  have hpoint (y : ℝ) : mellinBarnesFubiniKernel a b c x σ t y =
      ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
        (((x * t : ℝ) : ℂ) ^ ((σ : ℂ) + y * I) *
          (Gamma (-((σ : ℂ) + y * I)) * Gamma (a + ((σ : ℂ) + y * I)))) := by
    dsimp [mellinBarnesFubiniKernel]
    rw [add_sub_right_comm,
      cpow_add _ _ (ofReal_ne_zero.2 ht.1.ne'), ofReal_mul, ofReal_mul_cpow hx.le]
    ring
  simp_rw [hpoint, integral_const_mul]
  rw [← integral_neg_eq_self]
  have hneg (y : ℝ) : ((x * t : ℝ) : ℂ) ^ ((σ : ℂ) + (-y : ℝ) * I) *
      (Gamma (-((σ : ℂ) + (-y : ℝ) * I)) * Gamma (a + ((σ : ℂ) + (-y : ℝ) * I))) =
      ((x * t : ℝ) : ℂ) ^ (-((-σ : ℝ) + (y : ℂ) * I)) *
        (Gamma ((-σ : ℝ) + (y : ℂ) * I) * Gamma (a - ((-σ : ℝ) + (y : ℂ) * I))) := by
    have hpt : (σ : ℂ) + ((-y : ℝ) : ℂ) * I = -(((-σ : ℝ) : ℂ) + (y : ℂ) * I) := by
      simpa only [neg_neg] using (neg_ofReal_add_mul_I (-σ) y).symm
    rw [hpt, neg_neg, ← sub_eq_add_neg]
  simp_rw [hneg]
  rw [integral_cpow_neg_mul_Gamma_mul_Gamma_sub (by linarith) (by linarith) (mul_pos hx ht.1)]
  simp only [ofReal_mul, neg_mul, sub_neg_eq_add]
  ring

private theorem integral_mellinBarnesFubiniKernel_t {a b c : ℂ} {x σ : ℝ} (y : ℝ)
    (hbσ : 0 < b.re + σ) (hbc : b.re < c.re) :
    ∫ t in Ioo (0 : ℝ) 1, mellinBarnesFubiniKernel a b c x σ t y =
      Gamma (c - b) * mellinBarnesIntegrand a b c (-(x : ℂ)) (σ + y * I) := by
  dsimp only [mellinBarnesFubiniKernel]
  rw [integral_mul_const, setIntegral_Ioo_zero_one_eq, ← betaIntegral,
    betaIntegral_eq_Gamma_mul_div (b + (σ + y * I)) (c - b) (by simpa using hbσ)
      (by simpa using sub_pos.2 hbc),
    add_right_comm b ((σ : ℂ) + y * I) (c - b), add_sub_cancel,
    mellinBarnesIntegrand_def, neg_neg, div_eq_mul_inv]
  ring

private theorem eulerIntegral_neg_ofReal_eq_mellinBarnesIntegral {a b c : ℂ} {x : ℝ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hbc : b.re < c.re) (hx : 0 < x) :
    Gamma a * Gamma b * eulerIntegral a b c (-(x : ℂ)) =
      mellinBarnesIntegral a b c (-(x : ℂ)) := by
  let σ : ℝ := -min (min a.re b.re) 1 / 2
  have hmin : 0 < min (min a.re b.re) 1 := lt_min (lt_min ha hb) zero_lt_one
  have hσ : σ < 0 := by dsimp [σ]; linarith
  have haσ : 0 < a.re + σ := by
    dsimp [σ]; linarith [(min_le_left (min a.re b.re) 1).trans (min_le_left a.re b.re)]
  have hbσ : 0 < b.re + σ := by
    dsimp [σ]; linarith [(min_le_left (min a.re b.re) 1).trans (min_le_right a.re b.re)]
  have hswap := integral_integral_swap
    (integrable_mellinBarnesFubiniKernel hx hσ haσ hbσ hbc (c := c))
  have hGb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hGcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using sub_pos.2 hbc)
  have hlhs : (∫ t in Ioo (0 : ℝ) 1, ∫ y : ℝ, mellinBarnesFubiniKernel a b c x σ t y) =
      2 * π * Gamma (c - b) * (Gamma a * Gamma b * eulerIntegral a b c (-(x : ℂ))) := by
    rw [setIntegral_congr_fun measurableSet_Ioo fun t ht =>
        integral_mellinBarnesFubiniKernel_y hx ht hσ haσ,
      integral_const_mul, setIntegral_Ioo_zero_one_eq, eulerIntegral_def]
    have hcoeff : 2 * (π : ℂ) * Gamma a =
        2 * π * Gamma (c - b) * (Gamma a * Gamma b * (Gamma b * Gamma (c - b))⁻¹) := by
      field_simp [hGb, hGcb]
    rw [hcoeff]
    ring
  have hrhs : (∫ y : ℝ, ∫ t in Ioo (0 : ℝ) 1, mellinBarnesFubiniKernel a b c x σ t y) =
      Gamma (c - b) * ∫ y : ℝ, mellinBarnesIntegrand a b c (-(x : ℂ)) (σ + y * I) := by
    simp_rw [integral_mellinBarnesFubiniKernel_t _ hbσ hbc, integral_const_mul]
  rw [hlhs, hrhs] at hswap
  have h2pi : (2 * (π : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.2 Real.pi_ne_zero)
  rw [mellinBarnesIntegral_of_neg_re_lt c (by linarith) (by linarith) hσ
    (by simpa using ofReal_mem_slitPlane.2 hx : -(-(x : ℂ)) ∈ slitPlane)]
  have hcancel : (2 * (π : ℂ) * Gamma (c - b))⁻¹ * Gamma (c - b) = (2 * π : ℂ)⁻¹ := by
    field_simp [h2pi, hGcb]
  calc Gamma a * Gamma b * eulerIntegral a b c (-(x : ℂ))
      = (2 * π * Gamma (c - b))⁻¹ *
          (2 * π * Gamma (c - b) * (Gamma a * Gamma b * eulerIntegral a b c (-(x : ℂ)))) := by
        rw [← mul_assoc, inv_mul_cancel₀ (mul_ne_zero h2pi hGcb), one_mul]
    _ = (2 * π * Gamma (c - b))⁻¹ *
          (Gamma (c - b) * ∫ y : ℝ, mellinBarnesIntegrand a b c (-(x : ℂ)) (σ + y * I)) := by
        rw [hswap]
    _ = (2 * π : ℂ)⁻¹ * ∫ y : ℝ, mellinBarnesIntegrand a b c (-(x : ℂ)) (σ + y * I) := by
        rw [← mul_assoc, hcancel]

private theorem analyticAt_regularizedGaussHGFun_comp {f : ℂ → ℂ × ℂ × ℂ × ℂ}
    (hf : Differentiable ℂ f) {w : ℂ} (hz : ‖(f w).2.2.2‖ < 1) :
    AnalyticAt ℂ (fun x => regularizedGaussHGFun (f x).1 (f x).2.1 (f x).2.2.1 (f x).2.2.2) w :=
  (analyticAt_uncurry_regularizedGaussHGFun hz).comp_of_eq (hf.analyticAt w) rfl

private theorem analyticAt_mellinBarnesIntegral_comp {f : ℂ → ℂ × ℂ × ℂ × ℂ}
    (hf : Differentiable ℂ f) {w : ℂ} (ha : ∀ k : ℕ, (f w).1 ≠ -k)
    (hb : ∀ k : ℕ, (f w).2.1 ≠ -k) (hz : -(f w).2.2.2 ∈ slitPlane) :
    AnalyticAt ℂ (fun x => mellinBarnesIntegral (f x).1 (f x).2.1 (f x).2.2.1 (f x).2.2.2) w :=
  (analyticOnNhd_mellinBarnesIntegral (f w) ⟨ha, hb, hz⟩).comp_of_eq (hf.analyticAt w) rfl

private theorem eulerIntegral_mul_Gamma_eq_mellinBarnesIntegral {a b c z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : 0 < b.re) (hbc : b.re < c.re) (hz : -z ∈ slitPlane) :
    Gamma a * Gamma b * eulerIntegral a b c z = mellinBarnesIntegral a b c z := by
  have hb_ne := ne_neg_natCast_of_re_pos hb
  have hstep1 {a' z' : ℂ} (ha' : 0 < a'.re) (hz' : -z' ∈ slitPlane) :
      Gamma a' * Gamma b * eulerIntegral a' b c z' = mellinBarnesIntegral a' b c z' := by
    have hf : AnalyticOnNhd ℂ (fun u => Gamma a' * Gamma b * eulerIntegral a' b c (-u))
        slitPlane := fun u hu =>
      analyticAt_const.mul ((analyticOnNhd_eulerIntegral hb hbc (a', -u)
        (by simpa [sub_neg_eq_add] using
          TauCeti.ofReal_add_mem_slitPlane hu zero_le_one)).comp_of_eq
        ((by fun_prop : Differentiable ℂ fun x : ℂ => (a', -x)).analyticAt u) rfl)
    have hg : AnalyticOnNhd ℂ (fun u => mellinBarnesIntegral a' b c (-u)) slitPlane :=
      fun u hu => analyticAt_mellinBarnesIntegral_comp (f := fun x => (a', b, c, -x)) (by fun_prop)
        (ne_neg_natCast_of_re_pos ha') hb_ne (by simpa using hu)
    simpa only [neg_neg] using hf.eqOn_slitPlane_of_ofReal_pos_eq hg
      (fun x hx => eulerIntegral_neg_ofReal_eq_mellinBarnesIntegral ha' hb hbc hx) hz'
  have hf2 : AnalyticOnNhd ℂ (fun w => Gamma w * Gamma b * eulerIntegral w b c z)
      {w | ∀ k : ℕ, w ≠ -k} := fun w hw =>
    ((analyticAt_Gamma hw).mul analyticAt_const).mul
      ((analyticOnNhd_eulerIntegral hb hbc (w, z)
        (by simpa [sub_eq_add_neg] using
          TauCeti.ofReal_add_mem_slitPlane hz zero_le_one)).comp_of_eq
        ((by fun_prop : Differentiable ℂ fun x : ℂ => (x, z)).analyticAt w) rfl)
  have hg2 : AnalyticOnNhd ℂ (fun w => mellinBarnesIntegral w b c z) {w | ∀ k : ℕ, w ≠ -k} :=
    fun w hw => analyticAt_mellinBarnesIntegral_comp (f := fun x => (x, b, c, z)) (by fun_prop)
      hw hb_ne hz
  have hev : (fun w => Gamma w * Gamma b * eulerIntegral w b c z) =ᶠ[𝓝 (1 : ℂ)]
      (fun w => mellinBarnesIntegral w b c z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by simp : (0 : ℝ) < (1 : ℂ).re)] with w hw
    exact hstep1 hw hz
  exact hf2.eqOn_of_preconnected_of_eventuallyEq hg2
    isConnected_setOf_forall_ne_neg_natCast.isPreconnected
    (ne_neg_natCast_of_re_pos (by simp)) hev ha

/-- **Mellin–Barnes continuation of Euler's integral.** For `0 < Re b < Re c`, `a ∉ -ℕ`, and
`-z ∈ slitPlane`, Euler's normalized integral equals `(Γ(a) Γ(b))⁻¹` times the canonical
separating-contour Mellin–Barnes integral `mellinBarnesIntegral a b c z`. -/
theorem eulerIntegral_eq_mellinBarnesIntegral {a b c z : ℂ} (ha : ∀ k : ℕ, a ≠ -k)
    (hb : 0 < b.re) (hbc : b.re < c.re) (hz : -z ∈ slitPlane) :
    eulerIntegral a b c z = (Gamma a * Gamma b)⁻¹ * mellinBarnesIntegral a b c z := by
  rw [← eulerIntegral_mul_Gamma_eq_mellinBarnesIntegral ha hb hbc hz,
    inv_mul_cancel_left₀ (mul_ne_zero (Gamma_ne_zero ha) (Gamma_ne_zero_of_re_pos hb))]

/-- **Separating-contour Mellin–Barnes representation of Euler's integral.** For `0 < Re b < Re c`,
`a ∉ -ℕ`, `-z ∈ slitPlane`, and any admissible abscissa `σ < 0` avoiding `-Re a - ℕ` and
`-Re b - ℕ`, Euler's normalized integral equals `(Γ(a) Γ(b))⁻¹` times
`mellinBarnesSeparatingIntegral a b c z σ`. -/
theorem eulerIntegral_eq_mellinBarnesSeparatingIntegral {a b c z : ℂ} {σ : ℝ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : 0 < b.re) (hbc : b.re < c.re) (hσ : σ < 0)
    (haσ : ∀ k : ℕ, a.re + σ ≠ -k) (hbσ : ∀ k : ℕ, b.re + σ ≠ -k) (hz : -z ∈ slitPlane) :
    eulerIntegral a b c z = (Gamma a * Gamma b)⁻¹ * mellinBarnesSeparatingIntegral a b c z σ := by
  rw [eulerIntegral_eq_mellinBarnesIntegral ha hb hbc hz,
    mellinBarnesIntegral_eq_mellinBarnesSeparatingIntegral c hσ haσ hbσ hz]

private theorem regularizedGaussHGFun_mul_Gamma_eq_mellinBarnesIntegral {a b : ℂ} (c : ℂ) {z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hz_norm : ‖z‖ < 1)
    (hz_slit : -z ∈ slitPlane) :
    Gamma a * Gamma b * regularizedGaussHGFun a b c z = mellinBarnesIntegral a b c z := by
  have hstep_c {b' : ℂ} (hb' : 0 < b'.re) :
      Gamma a * Gamma b' * regularizedGaussHGFun a b' c z = mellinBarnesIntegral a b' c z := by
    have hfc : AnalyticOnNhd ℂ (fun w => Gamma a * Gamma b' * regularizedGaussHGFun a b' w z)
        univ := fun w _ => analyticAt_const.mul
      (analyticAt_regularizedGaussHGFun_comp (f := fun x => (a, b', x, z)) (by fun_prop) hz_norm)
    have hgc : AnalyticOnNhd ℂ (fun w => mellinBarnesIntegral a b' w z) univ := fun w _ =>
      analyticAt_mellinBarnesIntegral_comp (f := fun x => (a, b', x, z)) (by fun_prop)
        ha (ne_neg_natCast_of_re_pos hb') hz_slit
    have hevc : (fun w => Gamma a * Gamma b' * regularizedGaussHGFun a b' w z) =ᶠ[𝓝 (b' + 1)]
        (fun w => mellinBarnesIntegral a b' w z) := by
      filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
        (by simp : b'.re < (b' + 1).re)] with w hw
      rw [regularizedGaussHGFun_eq_eulerIntegral a hb' hw hz_norm]
      exact eulerIntegral_mul_Gamma_eq_mellinBarnesIntegral ha hb' hw hz_slit
    exact congrFun (hfc.eq_of_eventuallyEq hgc hevc) c
  have hfb : AnalyticOnNhd ℂ (fun w => Gamma a * Gamma w * regularizedGaussHGFun a w c z)
      {w | ∀ k : ℕ, w ≠ -k} := fun w hw => (analyticAt_const.mul (analyticAt_Gamma hw)).mul
    (analyticAt_regularizedGaussHGFun_comp (f := fun x => (a, x, c, z)) (by fun_prop) hz_norm)
  have hgb : AnalyticOnNhd ℂ (fun w => mellinBarnesIntegral a w c z)
      {w | ∀ k : ℕ, w ≠ -k} := fun w hw =>
    analyticAt_mellinBarnesIntegral_comp (f := fun x => (a, x, c, z)) (by fun_prop) ha hw hz_slit
  have hevb : (fun w => Gamma a * Gamma w * regularizedGaussHGFun a w c z) =ᶠ[𝓝 (1 : ℂ)]
      (fun w => mellinBarnesIntegral a w c z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by simp : (0 : ℝ) < (1 : ℂ).re)] with w hw
    exact hstep_c hw
  exact hfb.eqOn_of_preconnected_of_eventuallyEq hgb
    isConnected_setOf_forall_ne_neg_natCast.isPreconnected
    (ne_neg_natCast_of_re_pos (by simp)) hevb hb

/-- **Mellin–Barnes representation of the regularized Gauss hypergeometric function (DLMF 15.6.6)**
via the canonical separating-contour integral, giving `𝐅(a, b; c; z) = (Γ(a) Γ(b))⁻¹ *
mellinBarnesIntegral a b c z` for all `a, b ∉ -ℕ`, arbitrary `c : ℂ`, `‖z‖ < 1`, and
`-z ∈ slitPlane`. -/
theorem regularizedGaussHGFun_eq_mellinBarnesIntegral {a b : ℂ} (c : ℂ) {z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hz_norm : ‖z‖ < 1)
    (hz_slit : -z ∈ slitPlane) :
    regularizedGaussHGFun a b c z = (Gamma a * Gamma b)⁻¹ * mellinBarnesIntegral a b c z := by
  rw [← regularizedGaussHGFun_mul_Gamma_eq_mellinBarnesIntegral c ha hb hz_norm hz_slit,
    inv_mul_cancel_left₀ (mul_ne_zero (Gamma_ne_zero ha) (Gamma_ne_zero hb))]

/-- **Separating-contour Mellin–Barnes representation of `regularizedGaussHGFun` (DLMF 15.6.6)**
at any admissible abscissa `σ < 0` avoiding `-Re a - ℕ` and `-Re b - ℕ`, giving
`𝐅(a, b; c; z) = (Γ(a) Γ(b))⁻¹ * mellinBarnesSeparatingIntegral a b c z σ` for all `a, b ∉ -ℕ`,
arbitrary `c : ℂ`, `‖z‖ < 1`, and `-z ∈ slitPlane`. -/
theorem regularizedGaussHGFun_eq_mellinBarnesSeparatingIntegral {a b : ℂ} (c : ℂ) {z : ℂ} {σ : ℝ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hσ : σ < 0)
    (haσ : ∀ k : ℕ, a.re + σ ≠ -k) (hbσ : ∀ k : ℕ, b.re + σ ≠ -k)
    (hz_norm : ‖z‖ < 1) (hz_slit : -z ∈ slitPlane) :
    regularizedGaussHGFun a b c z =
      (Gamma a * Gamma b)⁻¹ * mellinBarnesSeparatingIntegral a b c z σ := by
  rw [regularizedGaussHGFun_eq_mellinBarnesIntegral c ha hb hz_norm hz_slit,
    mellinBarnesIntegral_eq_mellinBarnesSeparatingIntegral c hσ haσ hbσ hz_slit]

/-- **Mellin–Barnes representation of the ordinary Gauss hypergeometric function `₂F₁`**
(DLMF 15.6.6) via the canonical separating-contour integral, giving
`₂F₁(a, b; c; z) = (Γ(c) / (Γ(a) Γ(b))) * mellinBarnesIntegral a b c z` for all `a, b, c ∉ -ℕ`,
`‖z‖ < 1`, and `-z ∈ slitPlane`. -/
theorem ordinaryHypergeometric_eq_mellinBarnesIntegral {a b c z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hc : ∀ k : ℕ, c ≠ -k)
    (hz_norm : ‖z‖ < 1) (hz_slit : -z ∈ slitPlane) :
    ordinaryHypergeometric a b c z =
      Gamma c / (Gamma a * Gamma b) * mellinBarnesIntegral a b c z := by
  have h := ordinaryHypergeometric_div_Gamma_eq (a := a) (b := b) (z := z) hc
  rw [div_eq_iff (Gamma_ne_zero hc),
    regularizedGaussHGFun_eq_mellinBarnesIntegral c ha hb hz_norm hz_slit] at h
  rw [h, div_eq_mul_inv]
  ring

/-- **Separating-contour Mellin–Barnes representation of `ordinaryHypergeometric` (`₂F₁`)**
(DLMF 15.6.6) at any admissible abscissa `σ < 0` avoiding `-Re a - ℕ` and `-Re b - ℕ`, giving
`₂F₁(a, b; c; z) = (Γ(c) / (Γ(a) Γ(b))) * mellinBarnesSeparatingIntegral a b c z σ` for all
`a, b, c ∉ -ℕ`, `‖z‖ < 1`, and `-z ∈ slitPlane`. -/
theorem ordinaryHypergeometric_eq_mellinBarnesSeparatingIntegral {a b c z : ℂ} {σ : ℝ}
    (ha : ∀ k : ℕ, a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hc : ∀ k : ℕ, c ≠ -k) (hσ : σ < 0)
    (haσ : ∀ k : ℕ, a.re + σ ≠ -k) (hbσ : ∀ k : ℕ, b.re + σ ≠ -k)
    (hz_norm : ‖z‖ < 1) (hz_slit : -z ∈ slitPlane) :
    ordinaryHypergeometric a b c z =
      Gamma c / (Gamma a * Gamma b) * mellinBarnesSeparatingIntegral a b c z σ := by
  rw [ordinaryHypergeometric_eq_mellinBarnesIntegral ha hb hc hz_norm hz_slit,
    mellinBarnesIntegral_eq_mellinBarnesSeparatingIntegral c hσ haσ hbσ hz_slit]

end Complex
