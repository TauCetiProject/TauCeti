/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import TauCeti.Analysis.Calculus.RealCharts
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical

/-!
# The Mellin–Barnes integral of `(1 + u)^{-a}`

For `0 < Re s < Re a` the Mellin transform of `t ↦ (1 + t)^{-a}` is Euler's Beta integral of the
second kind (DLMF 5.12.3),

`∫₀^∞ t^{s - 1} (1 + t)^{-a} dt = Γ(s) Γ(a - s) / Γ(a)`,

obtained from the Beta integral over `[0, 1]` by the substitution `t = u / (1 - u)`. This adapts
the real-variable proof of `TauCeti.integral_rpow_mul_one_add_rpow` to complex parameters. On
every vertical line `Re s = σ` avoiding the poles of both factors the product `Γ(s) Γ(a - s)` is
integrable, since `Γ(σ + i y)` decays faster than every power of `|y|` while `Γ(a - σ - i y)` is
bounded. For `0 < σ < Re a`, Mellin inversion then gives the Mellin–Barnes integral of the
binomial,

`Γ(a) (1 + u)^{-a} = (1 / 2π) ∫ Γ(σ + i y) Γ(a - σ - i y) u^{-σ - i y} dy`   for `u > 0`.

This is the integral that, inserted into Euler's integral for the Gauss hypergeometric function
and into a Beta integral, gives the Mellin–Barnes representations of the Gauss function and
Barnes's first lemma.

## Main results

* `Complex.hasMellin_one_add_cpow_neg`: the Mellin transform of `(1 + t)^{-a}` converges at every
  `s` with `0 < Re s < Re a` and equals `Γ(s) Γ(a - s) / Γ(a)` there.
* `Complex.verticalIntegrable_Gamma_mul_Gamma_sub`: `s ↦ Γ(s) Γ(a - s)` is integrable on every
  vertical line `Re s = σ` with neither `σ` nor `Re a - σ` a nonpositive integer.
* `Complex.mellinInv_Gamma_mul_Gamma_sub`: Mellin inversion of `Γ(s) Γ(a - s)` on a vertical line
  `Re s = σ` with `0 < σ < Re a` is `Γ(a) (1 + u)^{-a}`.
* `Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_sub`: the same formula as the unnormalised
  vertical integral `∫ u^{-(σ + i y)} Γ(σ + i y) Γ(a - σ - i y) dy = 2π Γ(a) (1 + u)^{-a}`.

## References

* NIST Digital Library of Mathematical Functions, equation 5.12.3 and §15.6 (the Mellin–Barnes
  integrals 15.6.6–15.6.7).
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §§12.41 and 14.5.
-/

public section

open Real Set MeasureTheory Filter
open Complex hiding exp continuous_exp log

namespace Complex

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

end Complex
