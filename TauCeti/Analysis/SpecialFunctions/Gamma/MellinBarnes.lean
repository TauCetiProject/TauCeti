/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Calculus.RealCharts
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.MellinInversion
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical

/-!
# The Mellin–Barnes integral of `(1 + z)^{-a}` and Barnes's first lemma

For `0 < Re s < Re a` the Mellin transform of `t ↦ (1 + t)^{-a}` is Euler's Beta integral of the
second kind ([DLMF 5.12.3](https://dlmf.nist.gov/5.12.E3)),

`∫₀^∞ t^{s - 1} (1 + t)^{-a} dt = Γ(s) Γ(a - s) / Γ(a)`,

obtained from the Beta integral over `[0, 1]` by the substitution `t = u / (1 - u)`. This adapts
the real-variable proof of `TauCeti.integral_rpow_mul_one_add_rpow` to complex parameters. On
every vertical line `Re s = σ` avoiding the poles of both factors the product `Γ(s) Γ(a - s)` is
integrable, since `Γ(σ + i y)` decays faster than every power of `|y|` while `Γ(a - σ - i y)` is
bounded. For `0 < σ < Re a`, Mellin inversion then gives the Mellin–Barnes integral of the
binomial on `(0, ∞)`,

`Γ(a) (1 + u)^{-a} = (1 / 2π) ∫ Γ(σ + i y) Γ(a - σ - i y) u^{-σ - i y} dy`   for `u > 0`.

Stirling's vertical estimates (`TauCeti.exists_norm_Gamma_vertical_line_le` and
`TauCeti.exists_norm_Gamma_sub_mul_I_le`) sharpen the vertical decay to
`‖Γ(σ + i y) Γ(a - σ - i y)‖ = O((1 + |y|)^{Re a - 1} e^{-π |y|})`, so the slit-plane holomorphy of
the Mellin–Barnes kernel (`TauCeti.analyticOnNhd_integral_cpow_neg_smul_slitPlane`) and the
positive-axis identity principle `AnalyticOnNhd.eqOn_slitPlane_of_ofReal_pos_eq` continue the
representation to the whole cut plane `z ∈ Complex.slitPlane`:

`(2π)⁻¹ ∫_ℝ Γ(σ + i y) Γ(a - σ - i y) z^{-(σ + i y)} dy = Γ(a) (1 + z)^{-a}`.

Inserting this representation of `Γ(b + d) (1 + u)^{-(b + d)}` (translated along the vertical line
to `s = d - i y`) against `u^{a + d - 1} (1 + u)^{-(a + c)}` on `(0, ∞)` and exchanging the order of
integration by Fubini's theorem yields Barnes's first lemma
([DLMF 5.13.3](https://dlmf.nist.gov/5.13.E3)): for `a, b, c, d : ℂ` in the open right half-plane,

`(2π)⁻¹ ∫_ℝ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`.

## Main results

* `Complex.hasMellin_one_add_cpow_neg`, `Complex.integrableOn_cpow_mul_one_add_cpow_Ioi`,
  `Complex.integral_cpow_mul_one_add_cpow_Ioi`: the Mellin transform of `(1 + t)^{-a}` on `(0, ∞)`
  (DLMF 5.12.3).
* `Complex.verticalIntegrable_Gamma_mul_Gamma_sub`,
  `Complex.integrable_Gamma_mul_Gamma_sub_mul_cpow_neg`,
  `Complex.integrable_Gamma_add_mul_Gamma_neg_mul_cpow`: vertical integrability of
  `Γ(s) Γ(a - s)` and its slit-plane Mellin–Barnes integrands.
* `Complex.mellinInv_Gamma_mul_Gamma_sub`, `Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_sub`,
  `Complex.integral_Gamma_mul_Gamma_sub_mul_cpow_neg`,
  `Complex.integral_Gamma_add_mul_Gamma_neg_mul_cpow`: the Mellin–Barnes integral representation of
  `Γ(a) (1 + z)^{-a}` on `(0, ∞)` and on `Complex.slitPlane`, in both sign conventions.
* `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`,
  `Complex.integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`,
  `Complex.integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub`: Barnes's first lemma
  (DLMF 5.13.3) and its shifted-contour corollary.

## References

* [NIST Digital Library of Mathematical Functions, §5.12.3, §5.13.3, and §15.6](https://dlmf.nist.gov/5.13).
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §§12.41 and 14.5–14.52.
-/

public section

open Real Set MeasureTheory Filter Topology Function
open Complex hiding exp continuous_exp log

namespace Complex

/-! ### Mellin transform of `(1 + t)^{-a}` (DLMF 5.12.3) -/

/-- Under the chart `u ↦ u / (1 - u)` of `(0, 1)` onto `(0, ∞)`, the Mellin integrand of
`(1 + t)^{-a}` at `s` becomes the integrand of the Beta integral with parameters `s` and
`a - s`. -/
private lemma abs_deriv_smul_cpow_mul_one_add_cpow (s a : ℂ) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    |((1 - u) ^ 2)⁻¹| • (((u / (1 - u) : ℝ) : ℂ) ^ (s - 1) • (1 + ((u / (1 - u) : ℝ) : ℂ)) ^ (-a)) =
      (u : ℂ) ^ (s - 1) * (1 - (u : ℂ)) ^ (a - s - 1) := by
  obtain ⟨hu0, hu1⟩ := hu
  have h1u : 0 < 1 - u := by linarith
  -- every power below has a positive real base, so it is `exp (Real.log x * w)`
  have hexp {x : ℝ} (hx : 0 < x) (w : ℂ) : (x : ℂ) ^ w = cexp (Real.log x * w) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ofReal_log hx.le]
  have hbase : 1 + ((u / (1 - u) : ℝ) : ℂ) = (((1 - u)⁻¹ : ℝ) : ℂ) := by
    have hr : 1 + u / (1 - u) = (1 - u)⁻¹ := by field_simp; ring
    rw [← hr]
    push_cast
    ring
  have hsub : (1 - (u : ℂ)) = ((1 - u : ℝ) : ℂ) := by push_cast; ring
  have hfac : ((|((1 - u) ^ 2)⁻¹| : ℝ) : ℂ) = cexp (-(2 * Real.log (1 - u))) := by
    have hr : |((1 - u) ^ 2)⁻¹| = Real.exp (-(2 * Real.log (1 - u))) := by
      rw [abs_of_nonneg (by positivity), Real.exp_neg,
        show 2 * Real.log (1 - u) = Real.log ((1 - u) ^ 2) by rw [Real.log_pow]; norm_num,
        Real.exp_log (by positivity)]
    rw [hr, ofReal_exp]
    push_cast
    ring_nf
  rw [real_smul, smul_eq_mul, hbase, hsub, hfac,
    hexp (div_pos hu0 h1u), hexp (inv_pos.mpr h1u), hexp hu0, hexp h1u,
    Real.log_div hu0.ne' h1u.ne',
    Real.log_inv, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Euler's Beta integral of the second kind** (DLMF 5.12.3). For `0 < Re s < Re a` the Mellin
transform of `t ↦ (1 + t)^{-a}` converges at `s` and equals `Γ(s) Γ(a - s) / Γ(a)`. -/
theorem hasMellin_one_add_cpow_neg {s a : ℂ} (hs : 0 < s.re) (hsa : s.re < a.re) :
    HasMellin (fun t : ℝ ↦ (1 + (t : ℂ)) ^ (-a)) s (Gamma s * Gamma (a - s) / Gamma a) := by
  have has : 0 < (a - s).re := by simpa using hsa
  have hchart : (fun u : ℝ ↦ u / (1 - u)) '' Ioo 0 1 = Ioi 0 := by
    rw [TauCeti.image_div_one_sub_Ioo (u0 := 0) zero_lt_one]
    norm_num
  have hderiv : ∀ u ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun u : ℝ ↦ u / (1 - u)) ((1 - u) ^ 2)⁻¹ (Ioo 0 1) u :=
    fun u hu ↦ (TauCeti.hasDerivAt_div_one_sub hu.2.ne).hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ ↦ u / (1 - u)) (Ioo 0 1) :=
    TauCeti.strictMonoOn_div_one_sub.injOn.mono Ioo_subset_Iio_self
  -- the Beta integrand on `(0, 1)`, as an integrable function on `Ioo 0 1`
  have hbeta : IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * (1 - (u : ℂ)) ^ (a - s - 1))
      (Ioo 0 1) := by
    have h := betaIntegral_convergent hs has
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
    exact h.mono_set Ioo_subset_Ioc_self
  refine ⟨?_, ?_⟩
  · rw [MellinConvergent, ← hchart,
      integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hderiv hinj]
    exact hbeta.congr_fun (fun u hu ↦ (abs_deriv_smul_cpow_mul_one_add_cpow s a hu).symm)
      measurableSet_Ioo
  · rw [mellin, ← hchart,
      integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj,
      setIntegral_congr_fun measurableSet_Ioo
        fun u hu ↦ abs_deriv_smul_cpow_mul_one_add_cpow s a hu,
      setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      ← betaIntegral, betaIntegral_eq_Gamma_mul_div _ _ hs has, add_sub_cancel]

/-- For `0 < Re s < Re a`, the complex Euler beta integrand `t^{s-1} (1 + t)^{-a}` is integrable on
`(0, ∞)`. -/
theorem integrableOn_cpow_mul_one_add_cpow_Ioi {s a : ℂ} (hs : 0 < s.re) (hsa : s.re < a.re) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) * (1 + (t : ℂ)) ^ (-a)) (Ioi 0) := by
  simpa only [MellinConvergent, smul_eq_mul] using (hasMellin_one_add_cpow_neg hs hsa).1

/-- **Complex Euler second beta integral (DLMF 5.12.3)**: for `0 < Re s < Re a`,
`∫₀^∞ t^{s-1} (1 + t)^{-a} dt = Γ(s) Γ(a - s) / Γ(a)`. -/
theorem integral_cpow_mul_one_add_cpow_Ioi {s a : ℂ} (hs : 0 < s.re) (hsa : s.re < a.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (1 + (t : ℂ)) ^ (-a) =
      Gamma s * Gamma (a - s) / Gamma a := by
  simpa only [mellin, smul_eq_mul] using (hasMellin_one_add_cpow_neg hs hsa).2

/-! ### Mellin–Barnes integral of `(1 + z)^{-a}` on `(0, ∞)` and on the slit plane -/

/-- On every vertical line `Re s = σ` with neither `σ` nor `Re a - σ` a nonpositive integer, the
product `Γ(s) Γ(a - s)` is integrable. -/
theorem verticalIntegrable_Gamma_mul_Gamma_sub {a : ℂ} {σ : ℝ} (hσ : ∀ n : ℕ, σ ≠ -n)
    (haσ : ∀ n : ℕ, a.re - σ ≠ -n) :
    VerticalIntegrable (fun s ↦ Gamma s * Gamma (a - s)) σ := by
  have hsub (y : ℝ) : a - (σ + y * I) = ↑(a.re - σ) + ↑(a.im - y) * I := by
    apply Complex.ext <;> simp
  obtain ⟨C, hC⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow haσ 0
  refine (verticalIntegrable_Gamma hσ).mul_bdd (c := C) ?_
    (Eventually.of_forall fun y ↦ by simpa [hsub] using hC (a.im - y))
  refine Continuous.aestronglyMeasurable (continuous_iff_continuousAt.mpr fun y ↦ ?_)
  refine (differentiableAt_Gamma _ fun m h ↦ haσ m ?_).continuousAt.comp (by fun_prop)
  simpa using congrArg re h

/-- **The Mellin–Barnes integral of `(1 + u)^{-a}`.** On every vertical line `Re s = σ` with
`0 < σ < Re a`, Mellin inversion of `Γ(s) Γ(a - s)` gives `Γ(a) (1 + u)^{-a}` for `u > 0`:
`(1 / 2π) ∫ u^{-(σ + i y)} Γ(σ + i y) Γ(a - σ - i y) dy = Γ(a) (1 + u)^{-a}`. -/
theorem mellinInv_Gamma_mul_Gamma_sub {a : ℂ} {σ : ℝ} (hσ : 0 < σ) (hσa : σ < a.re) {u : ℝ}
    (hu : 0 < u) :
    mellinInv σ (fun s ↦ Gamma s * Gamma (a - s)) u = Gamma a * (1 + (u : ℂ)) ^ (-a) := by
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos (hσ.trans hσa)
  have hline : ∀ y : ℝ, Gamma (σ + y * I) * Gamma (a - (σ + y * I)) =
      mellin (fun t : ℝ ↦ Gamma a • (1 + (t : ℂ)) ^ (-a)) (σ + y * I) := by
    intro y
    rw [mellin_const_smul, (hasMellin_one_add_cpow_neg (by simpa using hσ)
      (by simpa using hσa)).2, smul_eq_mul, mul_div_cancel₀ _ hΓa]
  have hint : VerticalIntegrable (mellin fun t : ℝ ↦ Gamma a • (1 + (t : ℂ)) ^ (-a)) σ :=
    (verticalIntegrable_Gamma_mul_Gamma_sub (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
      (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])).congr (Eventually.of_forall hline)
  have hconv := (hasMellin_one_add_cpow_neg (s := σ) (a := a) (by simpa using hσ)
    (by simpa using hσa)).1.const_smul (Gamma a)
  have hcont : ContinuousAt (fun t : ℝ ↦ Gamma a • (1 + (t : ℂ)) ^ (-a)) u := by
    refine ((continuousAt_cpow_const ?_).comp (f := fun t : ℝ ↦ 1 + (t : ℂ))
      (by fun_prop)).const_smul (Gamma a)
    rw [← ofReal_one, ← ofReal_add]
    exact ofReal_mem_slitPlane.mpr (by linarith)
  rw [mellinInv]
  simp_rw [hline]
  rw [← mellinInv, mellinInv_mellin_eq σ _ hu hconv hint hcont]
  exact smul_eq_mul _ _

/-- **The Mellin–Barnes integral of `(1 + u)^{-a}`**, as an unnormalised vertical integral: on
every line `Re s = σ` with `0 < σ < Re a`,
`∫ u^{-(σ + i y)} Γ(σ + i y) Γ(a - σ - i y) dy = 2π Γ(a) (1 + u)^{-a}` for `u > 0`. -/
theorem integral_cpow_neg_mul_Gamma_mul_Gamma_sub {a : ℂ} {σ : ℝ} (hσ : 0 < σ) (hσa : σ < a.re)
    {u : ℝ} (hu : 0 < u) :
    ∫ y : ℝ, (u : ℂ) ^ (-(σ + y * I)) * (Gamma (σ + y * I) * Gamma (a - (σ + y * I))) =
      2 * π * (Gamma a * (1 + (u : ℂ)) ^ (-a)) := by
  have h := mellinInv_Gamma_mul_Gamma_sub hσ hσa hu
  rw [mellinInv, real_smul] at h
  simp only [smul_eq_mul] at h
  rw [← h, ← mul_assoc,
    show (2 * π : ℂ) * ((1 / (2 * π) : ℝ) : ℂ) = 1 by push_cast; field_simp, one_mul]

/-- Continuity and `O((1 + |y|)^{Re a - 1} e^{-π |y|})` decay of `y ↦ Γ(σ + i y) Γ(a - σ - i y)`
along any vertical line `Re s = σ` avoiding the poles of both Gamma factors. -/
private theorem continuous_and_norm_Gamma_mul_Gamma_sub_le {a : ℂ} {σ : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ -n) (haσ : ∀ n : ℕ, a.re - σ ≠ -n) :
    Continuous (fun y : ℝ ↦ Gamma (σ + y * I) * Gamma (a - (σ + y * I))) ∧
      ∃ C > 0, ∀ y : ℝ, ‖Gamma (σ + y * I) * Gamma (a - (σ + y * I))‖ ≤
        C * (1 + |y|) ^ (a.re - 1) * Real.exp (-π * |y|) := by
  have hcont : Continuous fun y : ℝ ↦ Gamma (σ + y * I) * Gamma (a - (σ + y * I)) := by
    refine Continuous.mul (continuous_iff_continuousAt.2 fun y ↦ ?_)
      (continuous_iff_continuousAt.2 fun y ↦ ?_)
    · exact (differentiableAt_Gamma _ fun m hm ↦
        hσ m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
    · exact (differentiableAt_Gamma _ fun m hm ↦
        haσ m (by simpa [sub_re] using congrArg re hm)).continuousAt.comp (by fun_prop)
  obtain ⟨C₁, hC₁, h₁⟩ := TauCeti.exists_norm_Gamma_vertical_line_le hσ
  obtain ⟨C₂, hC₂, h₂⟩ := TauCeti.exists_norm_Gamma_sub_mul_I_le (z := a - σ)
    (by simpa [sub_re] using haσ)
  refine ⟨hcont, C₁ * C₂, mul_pos hC₁ hC₂, fun y ↦ ?_⟩
  have h1y : 0 < 1 + |y| := by linarith [abs_nonneg y]
  have hsub : a - ((σ : ℂ) + y * I) = a - σ - y * I := by ring
  have h2y := h₂ y
  simp only [sub_re, ofReal_re] at h2y
  rw [hsub, norm_mul]
  calc ‖Gamma (σ + y * I)‖ * ‖Gamma (a - σ - y * I)‖
      ≤ (C₁ * (1 + |y|) ^ (σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (C₂ * (1 + |y|) ^ (a.re - σ - 1 / 2) * Real.exp (-π * |y| / 2)) :=
        mul_le_mul (h₁ y) h2y (norm_nonneg _) (by positivity)
    _ = C₁ * C₂ * ((1 + |y|) ^ (σ - 1 / 2) * (1 + |y|) ^ (a.re - σ - 1 / 2)) *
          (Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2)) := by ring
    _ = C₁ * C₂ * (1 + |y|) ^ (a.re - 1) * Real.exp (-π * |y|) := by
        rw [← Real.rpow_add h1y, ← Real.exp_add]
        have hr : σ - 1 / 2 + (a.re - σ - 1 / 2) = a.re - 1 := by ring
        have he : -π * |y| / 2 + -π * |y| / 2 = -π * |y| := by ring
        rw [hr, he]

/-- For `z ∈ Complex.slitPlane` and `σ : ℝ` avoiding the poles of `Γ(s)` and `Γ(a - s)`, the
Mellin–Barnes integrand `y ↦ Γ(σ + i y) Γ(a - (σ + i y)) z^{-(σ + i y)}` is integrable on `ℝ`. -/
theorem integrable_Gamma_mul_Gamma_sub_mul_cpow_neg {a z : ℂ} {σ : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ -n) (haσ : ∀ n : ℕ, a.re - σ ≠ -n) (hz : z ∈ slitPlane) :
    Integrable fun y : ℝ ↦ Gamma (σ + y * I) * Gamma (a - (σ + y * I)) * z ^ (-(σ + y * I)) := by
  obtain ⟨hcont, C, _, hbound⟩ := continuous_and_norm_Gamma_mul_Gamma_sub_le hσ haσ
  have h := TauCeti.integrable_cpow_neg_smul_of_norm_le_exp_neg_pi_mul_abs
    hcont.aestronglyMeasurable ⟨C, a.re - 1, hbound⟩ σ hz
  exact h.congr (Eventually.of_forall fun y ↦ by simp [smul_eq_mul, mul_comm, mul_assoc])

/-- **Mellin–Barnes integral representation of `(1 + z)^{-a}`** on the slit plane: for
`0 < σ < Re a` and `z ∈ Complex.slitPlane`,
`(2π)⁻¹ ∫_ℝ Γ(σ + i y) Γ(a - (σ + i y)) z^{-(σ + i y)} dy = Γ(a) (1 + z)^{-a}`. -/
theorem integral_Gamma_mul_Gamma_sub_mul_cpow_neg {a z : ℂ} {σ : ℝ} (hσ : 0 < σ) (hσa : σ < a.re)
    (hz : z ∈ slitPlane) :
    (2 * π : ℂ)⁻¹ *
        ∫ y : ℝ, Gamma (σ + y * I) * Gamma (a - (σ + y * I)) * z ^ (-(σ + y * I)) =
      Gamma a * (1 + z) ^ (-a) := by
  have hσ_ne : ∀ n : ℕ, σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have haσ_ne : ∀ n : ℕ, a.re - σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg (α := ℝ)]
  obtain ⟨hcont, C, _, hbound⟩ := continuous_and_norm_Gamma_mul_Gamma_sub_le hσ_ne haσ_ne
  let L : ℂ → ℂ := fun w ↦ (2 * π : ℂ)⁻¹ *
    ∫ y : ℝ, Gamma (σ + y * I) * Gamma (a - (σ + y * I)) * w ^ (-(σ + y * I))
  let R : ℂ → ℂ := fun w ↦ Gamma a * (1 + w) ^ (-a)
  have hanL : AnalyticOnNhd ℂ L slitPlane := by
    refine analyticOnNhd_const.mul ?_
    refine (TauCeti.analyticOnNhd_integral_cpow_neg_smul_slitPlane hcont.aestronglyMeasurable
      ⟨C, a.re - 1, hbound⟩ σ).congr isOpen_slitPlane fun w _ ↦ ?_
    exact integral_congr_ae (Eventually.of_forall fun y ↦ by
      simp [smul_eq_mul, mul_comm, mul_assoc])
  have hanR : AnalyticOnNhd ℂ R slitPlane := by
    refine DifferentiableOn.analyticOnNhd (fun w hw ↦ ?_) isOpen_slitPlane
    have h1w : 1 + w ∈ slitPlane := by
      simpa using TauCeti.ofReal_add_mem_slitPlane hw zero_le_one
    exact (((differentiableAt_id.const_add 1).cpow (differentiableAt_const _) h1w).const_mul
      _).differentiableWithinAt
  have hreal (r : ℝ) (hr : 0 < r) : L r = R r := by
    have hm := mellinInv_Gamma_mul_Gamma_sub hσ hσa hr
    unfold mellinInv at hm
    rw [real_smul] at hm
    dsimp [L, R]
    rw [← hm]
    push_cast
    rw [one_div]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun y ↦ by
      simp [smul_eq_mul, mul_comm, mul_assoc])
  exact hanL.eqOn_slitPlane_of_ofReal_pos_eq hanR hreal hz

/-- Positive-exponent companion to `Complex.integrable_Gamma_mul_Gamma_sub_mul_cpow_neg`:
`y ↦ Γ(a + (σ + i y)) Γ(-(σ + i y)) z^{σ + i y}` is integrable on `ℝ` whenever `-σ` and
`Re a + σ` avoid the nonpositive integers and `z ∈ Complex.slitPlane`. -/
theorem integrable_Gamma_add_mul_Gamma_neg_mul_cpow {a z : ℂ} {σ : ℝ}
    (hσ : ∀ n : ℕ, -σ ≠ -n) (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hz : z ∈ slitPlane) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) * z ^ ((σ : ℂ) + y * I) := by
  have h := integrable_Gamma_mul_Gamma_sub_mul_cpow_neg (a := a) (z := z) (σ := -σ)
    hσ (by simpa [sub_neg_eq_add] using haσ) hz
  refine h.comp_neg.congr (Eventually.of_forall fun y ↦ ?_)
  dsimp only [Function.comp_def]
  rw [ofReal_neg, ofReal_neg]
  have e1 : -(σ : ℂ) + -(y : ℂ) * I = -((σ : ℂ) + y * I) := by ring
  rw [e1, sub_neg_eq_add, neg_neg, mul_comm (Gamma _)]

/-- Positive-exponent form of the Mellin–Barnes integral of `(1 + z)^{-a}`: for `-Re a < σ < 0` and
`z ∈ Complex.slitPlane`,
`(2π)⁻¹ ∫_ℝ Γ(a + (σ + i y)) Γ(-(σ + i y)) z^{σ + i y} dy = Γ(a) (1 + z)^{-a}`. -/
theorem integral_Gamma_add_mul_Gamma_neg_mul_cpow {a z : ℂ} {σ : ℝ} (hσ : σ < 0)
    (haσ : -a.re < σ) (hz : z ∈ slitPlane) :
    (2 * π : ℂ)⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) * z ^ (σ + y * I) =
      Gamma a * (1 + z) ^ (-a) := by
  have h := integral_Gamma_mul_Gamma_sub_mul_cpow_neg (a := a) (z := z) (σ := -σ)
    (neg_pos.2 hσ) (by linarith) hz
  rw [← h]
  congr 1
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  rw [ofReal_neg, ofReal_neg]
  have e1 : -((σ : ℂ) + -(y : ℂ) * I) = -(σ : ℂ) + (y : ℂ) * I := by ring
  have e2 : a + ((σ : ℂ) + -(y : ℂ) * I) = a - (-(σ : ℂ) + (y : ℂ) * I) := by ring
  have e3 : (σ : ℂ) + -(y : ℂ) * I = -(-(σ : ℂ) + (y : ℂ) * I) := by ring
  rw [e1, e2, e3, mul_comm (Gamma _)]

/-! ### Barnes's first lemma (DLMF 5.13.3) -/

/-- The four-Gamma integrand `y ↦ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y)` of Barnes's first
lemma is integrable on `ℝ` whenever the real parts of `a`, `b`, `c`, `d` avoid the nonpositive
integers. -/
theorem integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ}
    (ha : ∀ n : ℕ, a.re ≠ -n) (hb : ∀ n : ℕ, b.re ≠ -n)
    (hc : ∀ n : ℕ, c.re ≠ -n) (hd : ∀ n : ℕ, d.re ≠ -n) :
    Integrable fun y : ℝ ↦
      Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
  obtain ⟨C₁, hC₁, h₁⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le ha
  obtain ⟨C₂, hC₂, h₂⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le hb
  obtain ⟨C₃, hC₃, h₃⟩ := TauCeti.exists_norm_Gamma_sub_mul_I_le hc
  obtain ⟨C₄, _, h₄⟩ := TauCeti.exists_norm_Gamma_sub_mul_I_le hd
  have hcont : Continuous fun y : ℝ ↦
      Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
    have hc_add {z : ℂ} (hz : ∀ n : ℕ, z.re ≠ -n) : Continuous fun y : ℝ ↦ Gamma (z + y * I) :=
      continuous_iff_continuousAt.2 fun y ↦
        (differentiableAt_Gamma _ fun m hm ↦
          hz m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
    have hc_sub {z : ℂ} (hz : ∀ n : ℕ, z.re ≠ -n) : Continuous fun y : ℝ ↦ Gamma (z - y * I) :=
      continuous_iff_continuousAt.2 fun y ↦
        (differentiableAt_Gamma _ fun m hm ↦
          hz m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
    exact (((hc_add ha).mul (hc_add hb)).mul (hc_sub hc)).mul (hc_sub hd)
  refine ((TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs
    (show 0 < 2 * π by positivity) (a.re + b.re + c.re + d.re - 2)).const_mul
    (C₁ * C₂ * C₃ * C₄)).mono' hcont.aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
  have h1y : 0 < 1 + |y| := by linarith [abs_nonneg y]
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖Gamma (a + y * I)‖ * ‖Gamma (b + y * I)‖ * ‖Gamma (c - y * I)‖ * ‖Gamma (d - y * I)‖
      ≤ (C₁ * (1 + |y|) ^ (a.re - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (C₂ * (1 + |y|) ^ (b.re - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (C₃ * (1 + |y|) ^ (c.re - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (C₄ * (1 + |y|) ^ (d.re - 1 / 2) * Real.exp (-π * |y| / 2)) := by
        refine mul_le_mul
          (mul_le_mul (mul_le_mul (h₁ y) (h₂ y) (norm_nonneg _) (by positivity)) (h₃ y)
            (norm_nonneg _) (by positivity))
          (h₄ y) (norm_nonneg _) (by positivity)
    _ = C₁ * C₂ * C₃ * C₄ *
          ((1 + |y|) ^ (a.re - 1 / 2) * (1 + |y|) ^ (b.re - 1 / 2) *
            (1 + |y|) ^ (c.re - 1 / 2) * (1 + |y|) ^ (d.re - 1 / 2)) *
          (Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2) *
            Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2)) := by ring
    _ = C₁ * C₂ * C₃ * C₄ *
          ((1 + |y|) ^ (a.re + b.re + c.re + d.re - 2) * Real.exp (-(2 * π) * |y|)) := by
        rw [← Real.rpow_add h1y, ← Real.rpow_add h1y, ← Real.rpow_add h1y,
          ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        ring_nf

/-- **Barnes's first lemma (DLMF 5.13.3)**: for `a, b, c, d : ℂ` in the open right half-plane,
`(2π)⁻¹ ∫_ℝ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) *
        Gamma (d - y * I) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  have hb_ne : ∀ n : ℕ, b.re ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have hd_ne : ∀ n : ℕ, d.re ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have hbd_mb (u : ℝ) (hu : 0 < u) :
      Gamma (b + d) * (1 + (u : ℂ)) ^ (-(b + d)) =
        (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (b + y * I) * Gamma (d - y * I) * (u : ℂ) ^ (y * I - d) := by
    have hmb := integral_Gamma_mul_Gamma_sub_mul_cpow_neg (a := b + d) (z := (u : ℂ)) (σ := d.re)
      hd (by simp [add_re, hb]) (ofReal_mem_slitPlane.2 hu)
    rw [← hmb]
    congr 1
    rw [← integral_sub_left_eq_self _ volume d.im]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    dsimp only
    have hd_eq : (d.re : ℂ) + ((d.im - y : ℝ) : ℂ) * I = d - y * I := by
      apply Complex.ext <;> simp
    rw [hd_eq, show b + d - (d - y * I) = b + y * I by ring,
      show -(d - y * I) = y * I - d by ring, mul_comm (Gamma (d - y * I))]
  let F : ℝ → ℝ → ℂ := fun u y ↦
    Gamma (b + y * I) * Gamma (d - y * I) *
      ((u : ℂ) ^ (a + y * I - 1) * (1 + (u : ℂ)) ^ (-(a + c)))
  -- Product-measure integrability on `(0, ∞) × ℝ` via factored real majorants.
  have hF_int : Integrable (uncurry F) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    have hφ : Integrable (fun u : ℝ ↦ ‖(u : ℂ) ^ ((a.re : ℂ) - 1) *
        (1 + (u : ℂ)) ^ (-((a.re + c.re : ℝ) : ℂ))‖) (volume.restrict (Ioi 0)) :=
      (integrableOn_cpow_mul_one_add_cpow_Ioi (s := a.re) (a := (a.re + c.re : ℝ))
        (by simpa using ha) (by simp [hc])).norm
    obtain ⟨C₁, hC₁, h₁⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le hb_ne
    obtain ⟨C₂, _, h₂⟩ := TauCeti.exists_norm_Gamma_sub_mul_I_le hd_ne
    have hψ_cont : Continuous fun y : ℝ ↦ ‖Gamma (b + y * I) * Gamma (d - y * I)‖ := by
      refine Continuous.norm (Continuous.mul (continuous_iff_continuousAt.2 fun y ↦ ?_)
        (continuous_iff_continuousAt.2 fun y ↦ ?_))
      · exact (differentiableAt_Gamma _ fun m hm ↦
          hb_ne m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
      · exact (differentiableAt_Gamma _ fun m hm ↦
          hd_ne m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
    have hψ : Integrable (fun y : ℝ ↦ ‖Gamma (b + y * I) * Gamma (d - y * I)‖) volume := by
      refine ((TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs Real.pi_pos
        (b.re + d.re - 1)).const_mul (C₁ * C₂)).mono' hψ_cont.aestronglyMeasurable
        (Eventually.of_forall fun y ↦ ?_)
      have h1y : 0 < 1 + |y| := by linarith [abs_nonneg y]
      rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul]
      calc ‖Gamma (b + y * I)‖ * ‖Gamma (d - y * I)‖
          ≤ (C₁ * (1 + |y|) ^ (b.re - 1 / 2) * Real.exp (-π * |y| / 2)) *
              (C₂ * (1 + |y|) ^ (d.re - 1 / 2) * Real.exp (-π * |y| / 2)) :=
            mul_le_mul (h₁ y) (h₂ y) (norm_nonneg _) (by positivity)
        _ = C₁ * C₂ * ((1 + |y|) ^ (b.re - 1 / 2) * (1 + |y|) ^ (d.re - 1 / 2)) *
              (Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2)) := by ring
        _ = C₁ * C₂ * ((1 + |y|) ^ (b.re + d.re - 1) * Real.exp (-π * |y|)) := by
            rw [← Real.rpow_add h1y, ← Real.exp_add]
            ring_nf
    have hmeas_eq : (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ) =
        ((volume : Measure ℝ).prod volume).restrict (Ioi (0 : ℝ) ×ˢ univ) := by
      simpa only [Measure.restrict_univ] using
        Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
          (Ioi (0 : ℝ)) univ
    have hF_meas : AEStronglyMeasurable (uncurry F)
        ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
      rw [hmeas_eq]
      refine ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ).prod volume) ?_
        (measurableSet_Ioi.prod MeasurableSet.univ)
      rintro ⟨u, y⟩ ⟨hu : 0 < u, -⟩
      have hu_slit : (u : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 hu
      have h1u_slit : 1 + (u : ℂ) ∈ slitPlane := by
        simpa using TauCeti.ofReal_add_mem_slitPlane hu_slit zero_le_one
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.mul (ContinuousAt.mul ?_ ?_) (ContinuousAt.mul ?_ ?_)
      · exact (differentiableAt_Gamma _ fun m hm ↦
          hb_ne m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
      · exact (differentiableAt_Gamma _ fun m hm ↦
          hd_ne m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
      · exact ContinuousAt.cpow (by fun_prop) (by fun_prop) hu_slit
      · exact ContinuousAt.cpow (by fun_prop) continuousAt_const h1u_slit
    refine (hφ.mul_prod hψ).mono' hF_meas ?_
    rw [hmeas_eq]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with ⟨u, y⟩ ⟨hu, _⟩
    have hu' : 0 < u := hu
    have h1u : 0 < 1 + u := by linarith
    dsimp [uncurry, F]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, ← ofReal_one, ← ofReal_add,
      norm_cpow_eq_rpow_re_of_pos hu', norm_cpow_eq_rpow_re_of_pos h1u,
      norm_cpow_eq_rpow_re_of_pos hu', norm_cpow_eq_rpow_re_of_pos h1u]
    simp only [sub_re, add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, neg_re]
    ring_nf
    exact le_rfl
  -- Evaluate `∫_{u > 0} ∫_y F u y` both ways via `integral_integral_swap`.
  have hLHS : (2 * π : ℂ)⁻¹ * ∫ u in Ioi (0 : ℝ), ∫ y : ℝ, F u y =
      Gamma (b + d) * (Gamma (a + d) * Gamma (b + c) / Gamma (a + b + c + d)) := by
    have hinner (u : ℝ) (hu : 0 < u) :
        (2 * π : ℂ)⁻¹ * ∫ y : ℝ, F u y =
          Gamma (b + d) * ((u : ℂ) ^ (a + d - 1) * (1 + (u : ℂ)) ^ (-(a + b + c + d))) := by
      have hu_ne : (u : ℂ) ≠ 0 := ofReal_ne_zero.2 hu.ne'
      have h1u_ne : 1 + (u : ℂ) ≠ 0 := by
        rw [← ofReal_one, ← ofReal_add]
        exact ofReal_ne_zero.2 (by linarith)
      have hpull : (∫ y : ℝ, F u y) =
          ((u : ℂ) ^ (a + d - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
            ∫ y : ℝ, Gamma (b + y * I) * Gamma (d - y * I) * (u : ℂ) ^ (y * I - d) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
        dsimp [F]
        have hpow : (u : ℂ) ^ (a + d - 1) * (u : ℂ) ^ (y * I - d) = (u : ℂ) ^ (a + y * I - 1) := by
          rw [← cpow_add _ _ hu_ne]
          congr 1
          ring
        rw [← hpow]
        ring
      have h1pow : (1 + (u : ℂ)) ^ (-(a + c)) * (1 + (u : ℂ)) ^ (-(b + d)) =
          (1 + (u : ℂ)) ^ (-(a + b + c + d)) := by
        rw [← cpow_add _ _ h1u_ne]
        congr 1
        ring
      rw [hpull, ← mul_left_comm ((u : ℂ) ^ (a + d - 1) * _), ← hbd_mb u hu]
      linear_combination Gamma (b + d) * (u : ℂ) ^ (a + d - 1) * h1pow
    rw [← integral_const_mul, setIntegral_congr_fun measurableSet_Ioi hinner, integral_const_mul,
      integral_cpow_mul_one_add_cpow_Ioi (s := a + d) (a := a + b + c + d)
        (by simp [add_re]; linarith) (by simp [add_re]; linarith),
      show a + b + c + d - (a + d) = b + c by ring]
  have hRHS : (2 * π : ℂ)⁻¹ * ∫ y : ℝ, ∫ u in Ioi (0 : ℝ), F u y =
      ((2 * π : ℂ)⁻¹ * ∫ y : ℝ,
        Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I)) /
          Gamma (a + c) := by
    have hinner (y : ℝ) :
        ∫ u in Ioi (0 : ℝ), F u y =
          (Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I)) /
            Gamma (a + c) := by
      dsimp [F]
      rw [integral_const_mul,
        integral_cpow_mul_one_add_cpow_Ioi (s := a + y * I) (a := a + c)
          (by simpa using ha) (by simp [add_re, hc]),
        show a + c - (a + y * I) = c - y * I by ring]
      ring
    simp_rw [hinner, integral_div, mul_div_assoc]
  have hswap : (2 * π : ℂ)⁻¹ * ∫ u in Ioi (0 : ℝ), ∫ y : ℝ, F u y =
      (2 * π : ℂ)⁻¹ * ∫ y : ℝ, ∫ u in Ioi (0 : ℝ), F u y := by
    rw [integral_integral_swap hF_int]
  rw [hLHS, hRHS] at hswap
  have hΓac : Gamma (a + c) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [add_re]; linarith)
  rw [eq_div_iff hΓac] at hswap
  rw [← hswap]
  ring

/-- Shifted-contour form of Barnes's first lemma: on any vertical line `Re s = σ` separating the
left-opening poles `-a - ℕ`, `-b - ℕ` from the right-opening poles `c + ℕ`, `d + ℕ`
(that is, `-Re a < σ`, `-Re b < σ`, `σ < Re c`, `σ < Re d`),
`(2π)⁻¹ ∫_ℝ Γ(a + (σ + i y)) Γ(b + (σ + i y)) Γ(c - (σ + i y)) Γ(d - (σ + i y)) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub {a b c d : ℂ} {σ : ℝ}
    (ha : -a.re < σ) (hb : -b.re < σ) (hc : σ < c.re) (hd : σ < d.re) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ,
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - (σ + y * I)) * Gamma (d - (σ + y * I)) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  have h := integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma
    (a := a + σ) (b := b + σ) (c := c - σ) (d := d - σ)
    (by simp [add_re]; linarith) (by simp [add_re]; linarith)
    (by simp [sub_re]; linarith) (by simp [sub_re]; linarith)
  have e1 : a + σ + (c - σ) = a + c := by ring
  have e2 : a + σ + (d - σ) = a + d := by ring
  have e3 : b + σ + (c - σ) = b + c := by ring
  have e4 : b + σ + (d - σ) = b + d := by ring
  have e5 : a + σ + (b + σ) + (c - σ) + (d - σ) = a + b + c + d := by ring
  rw [e1, e2, e3, e4, e5] at h
  rw [← h]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  have s1 : a + ((σ : ℂ) + y * I) = a + σ + y * I := by ring
  have s2 : b + ((σ : ℂ) + y * I) = b + σ + y * I := by ring
  have s3 : c - ((σ : ℂ) + y * I) = c - σ - y * I := by ring
  have s4 : d - ((σ : ℂ) + y * I) = d - σ - y * I := by ring
  rw [s1, s2, s3, s4]

end Complex
