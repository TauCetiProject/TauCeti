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
# The Mellin–Barnes integral of `(1 + u)^{-a}` and Barnes's first lemma

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
Barnes's first lemma (DLMF 5.13.3): for `a`, `b`, `c`, `d` with positive real parts,

`(1 / 2π) ∫ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy
  = Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`.

To prove it, write `Γ(b + d) (1 + u)^{-(b + d)}` as its Mellin–Barnes integral along
`Re s = Re b` inside the Beta integral
`∫₀^∞ u^{b + c - 1} (1 + u)^{-(a + c)} (1 + u)^{-(b + d)} du
  = Γ(b + c) Γ(a + d) / Γ(a + b + c + d)`,
and exchange the two integrals: the inner integral in `u` is then the Beta integral
`∫₀^∞ u^{c - i y - 1} (1 + u)^{-(a + c)} du = Γ(c - i y) Γ(a + i y) / Γ(a + c)`. Barnes's first
lemma evaluates the termwise integrals in the Mellin–Barnes representation of the Gauss function
in the variable `1 - z` (DLMF 15.6.7).

## Main results

* `Complex.hasMellin_one_add_cpow_neg`: the Mellin transform of `(1 + t)^{-a}` converges at every
  `s` with `0 < Re s < Re a` and equals `Γ(s) Γ(a - s) / Γ(a)` there.
* `Complex.integrableOn_cpow_mul_one_add_cpow_neg`, `Complex.integral_cpow_mul_one_add_cpow_neg`:
  the same Beta integral as an integrable function and a set integral on `(0, ∞)`.
* `Complex.verticalIntegrable_Gamma_mul_Gamma_sub`: `s ↦ Γ(s) Γ(a - s)` is integrable on every
  vertical line `Re s = σ` with neither `σ` nor `Re a - σ` a nonpositive integer.
* `Complex.mellinInv_Gamma_mul_Gamma_sub`: Mellin inversion of `Γ(s) Γ(a - s)` on a vertical line
  `Re s = σ` with `0 < σ < Re a` is `Γ(a) (1 + u)^{-a}`.
* `Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_sub`: the same formula as the unnormalised
  vertical integral `∫ u^{-(σ + i y)} Γ(σ + i y) Γ(a - σ - i y) dy = 2π Γ(a) (1 + u)^{-a}`.
* `Complex.integral_cpow_neg_mul_Gamma_add_mul_Gamma_sub`: the same integral along the line
  `Re s = Re b` parametrised from a complex point `b`,
  `∫ u^{-(b + i y)} Γ(b + i y) Γ(d - i y) dy = 2π Γ(b + d) (1 + u)^{-(b + d)}`.
* `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`: the integrand of Barnes's first lemma
  is integrable on the imaginary axis.
* `Complex.integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`: **Barnes's first lemma** (DLMF 5.13.3).

## References

* NIST Digital Library of Mathematical Functions, equations 5.12.3 and 5.13.3 and §15.6 (the
  Mellin–Barnes integrals 15.6.6–15.6.7).
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

/-- For `0 < Re s < Re a`, the integrand `u^{s - 1} (1 + u)^{-a}` of Euler's Beta integral of the
second kind is integrable on `(0, ∞)`. -/
theorem integrableOn_cpow_mul_one_add_cpow_neg {s a : ℂ} (hs : 0 < s.re) (hsa : s.re < a.re) :
    IntegrableOn (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * (1 + (u : ℂ)) ^ (-a)) (Ioi 0) := by
  simpa [MellinConvergent] using (hasMellin_one_add_cpow_neg hs hsa).1

/-- **Euler's Beta integral of the second kind** (DLMF 5.12.3), as a set integral: for
`0 < Re s < Re a`, `∫₀^∞ u^{s - 1} (1 + u)^{-a} du = Γ(s) Γ(a - s) / Γ(a)`. -/
theorem integral_cpow_mul_one_add_cpow_neg {s a : ℂ} (hs : 0 < s.re) (hsa : s.re < a.re) :
    ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * (1 + (u : ℂ)) ^ (-a) =
      Gamma s * Gamma (a - s) / Gamma a := by
  simpa [mellin] using (hasMellin_one_add_cpow_neg hs hsa).2

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

/-! ### Barnes's first lemma -/

/-- A complex number with positive real part does not have a nonpositive integer as real part. -/
private lemma re_ne_neg_natCast {b : ℂ} (hb : 0 < b.re) (n : ℕ) : b.re ≠ -n := by
  linarith [n.cast_nonneg' (α := ℝ)]

/-- The line `Re s = Re b`, parametrised from `Re b` and shifted by `Im b`, is the line
parametrised from `b`. -/
private lemma re_add_add_im_mul_I (b : ℂ) (y : ℝ) :
    (b.re : ℂ) + ((y + b.im : ℝ) : ℂ) * I = b + y * I := by
  apply Complex.ext <;> simp [add_comm]

/-- On the imaginary axis, `y ↦ Γ(b + i y) Γ(d - i y)` is integrable when neither `Re b` nor `Re d`
is a nonpositive integer. -/
theorem integrable_Gamma_add_mul_Gamma_sub {b d : ℂ} (hb : ∀ n : ℕ, b.re ≠ -n)
    (hd : ∀ n : ℕ, d.re ≠ -n) :
    Integrable fun y : ℝ ↦ Gamma (b + y * I) * Gamma (d - y * I) := by
  have h := (verticalIntegrable_Gamma_mul_Gamma_sub (a := b + d) (σ := b.re) hb
    (by simpa using hd)).comp_add_right b.im
  refine h.congr (Eventually.of_forall fun y ↦ ?_)
  simp only [re_add_add_im_mul_I, add_sub_add_left_eq_sub]

/-- **The Mellin–Barnes integral of `(1 + u)^{-(b + d)}`** along the line `Re s = Re b`,
parametrised from `b`: for `0 < Re b`, `0 < Re d` and `u > 0`,
`∫ u^{-(b + i y)} Γ(b + i y) Γ(d - i y) dy = 2π Γ(b + d) (1 + u)^{-(b + d)}`. -/
theorem integral_cpow_neg_mul_Gamma_add_mul_Gamma_sub {b d : ℂ} (hb : 0 < b.re) (hd : 0 < d.re)
    {u : ℝ} (hu : 0 < u) :
    ∫ y : ℝ, (u : ℂ) ^ (-(b + y * I)) * (Gamma (b + y * I) * Gamma (d - y * I)) =
      2 * π * (Gamma (b + d) * (1 + (u : ℂ)) ^ (-(b + d))) := by
  set φ : ℂ → ℂ := fun s ↦ (u : ℂ) ^ (-s) * (Gamma s * Gamma (b + d - s))
  calc
    _ = ∫ y : ℝ, φ (b.re + ((y + b.im : ℝ) : ℂ) * I) := by
      refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
      simp only [φ, re_add_add_im_mul_I, add_sub_add_left_eq_sub]
    _ = ∫ y : ℝ, φ (b.re + y * I) := integral_add_right_eq_self (fun y : ℝ ↦ φ (b.re + y * I)) b.im
    _ = _ := integral_cpow_neg_mul_Gamma_mul_Gamma_sub hb (by simp; linarith) hu

/-- The integrand `Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y)` of Barnes's first lemma is
integrable on the imaginary axis when `a`, `b`, `c` and `d` have positive real parts. -/
theorem integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    Integrable fun y : ℝ ↦
      Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
  refine ((integrable_Gamma_add_mul_Gamma_sub (re_ne_neg_natCast ha) (re_ne_neg_natCast hd)).mul_bdd
    (c := Real.Gamma b.re * Real.Gamma c.re) (integrable_Gamma_add_mul_Gamma_sub
      (re_ne_neg_natCast hb) (re_ne_neg_natCast hc)).aestronglyMeasurable
    (Eventually.of_forall fun y ↦ ?_)).congr (Eventually.of_forall fun y ↦ by ring)
  have h1 : ‖Gamma (b + y * I)‖ ≤ Real.Gamma b.re := by
    simpa using norm_Gamma_le_Gamma_re (s := b + y * I) (by simpa using hb)
  have h2 : ‖Gamma (c - y * I)‖ ≤ Real.Gamma c.re := by
    simpa using norm_Gamma_le_Gamma_re (s := c - y * I) (by simpa using hc)
  rw [norm_mul]
  exact mul_le_mul h1 h2 (norm_nonneg _) (Real.Gamma_pos_of_pos hb).le

/-- The kernel `u^{c - 1} (1 + u)^{-(a + c)} u^{-i y} Γ(b + i y) Γ(d - i y)` whose two iterated
integrals give the two sides of Barnes's first lemma is integrable on `(0, ∞) × ℝ`: for `u > 0` its
norm is the product of the norms of a Beta integrand in `u` and of `Γ(b + i y) Γ(d - i y)`. -/
private lemma integrable_barnesKernel {a b c d : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) (hd : 0 < d.re) :
    Integrable (fun z : ℝ × ℝ ↦ (z.1 : ℂ) ^ (c - 1) * (1 + (z.1 : ℂ)) ^ (-(a + c)) *
      ((z.1 : ℂ) ^ (-(z.2 * I)) * (Gamma (b + z.2 * I) * Gamma (d - z.2 * I))))
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hh := integrableOn_cpow_mul_one_add_cpow_neg (s := c) (a := a + c) hc (by simp; linarith)
  have hg := integrable_Gamma_add_mul_Gamma_sub (re_ne_neg_natCast hb) (re_ne_neg_natCast hd)
  have hpos : ∀ᵐ z ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ)), 0 < z.1 := by
    rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with z hz
    exact hz.1
  refine (hh.mul_prod hg).norm.mono' (hh.aestronglyMeasurable.comp_fst.mul
    ((Measurable.aestronglyMeasurable (by fun_prop)).mul hg.aestronglyMeasurable.comp_snd)) ?_
  filter_upwards [hpos] with z hz
  simp [norm_cpow_eq_rpow_re_of_pos hz]

/-- The integral in `y` of the kernel of Barnes's first lemma is the Mellin–Barnes integral of
`(1 + u)^{-(b + d)}`, which turns the kernel into a Beta integrand in `u`. -/
private lemma integral_barnesKernel_im {a b c d : ℂ} (hb : 0 < b.re) (hd : 0 < d.re) {u : ℝ}
    (hu : 0 < u) :
    ∫ y : ℝ, (u : ℂ) ^ (c - 1) * (1 + (u : ℂ)) ^ (-(a + c)) *
      ((u : ℂ) ^ (-(y * I)) * (Gamma (b + y * I) * Gamma (d - y * I))) =
      2 * π * Gamma (b + d) * ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + b + c + d))) := by
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  have h1u : 1 + (u : ℂ) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_add]
    exact ofReal_ne_zero.mpr (by linarith)
  have hshift (y : ℝ) : (u : ℂ) ^ (-(y * I)) = (u : ℂ) ^ b * (u : ℂ) ^ (-(b + y * I)) := by
    rw [← cpow_add _ _ hu0]
    congr 1
    ring
  simp_rw [hshift, mul_assoc ((u : ℂ) ^ b)]
  rw [integral_const_mul, integral_const_mul,
    integral_cpow_neg_mul_Gamma_add_mul_Gamma_sub hb hd hu, show b + c - 1 = c - 1 + b by ring,
    show -(a + b + c + d) = -(a + c) + -(b + d) by ring,
    cpow_add _ _ hu0, cpow_add _ _ h1u]
  ring

/-- The integral in `u` of the kernel of Barnes's first lemma is a Beta integral of the second
kind, which turns the kernel into the integrand of Barnes's first lemma. -/
private lemma integral_barnesKernel_Ioi {a b c d : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) (y : ℝ) :
    ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (c - 1) * (1 + (u : ℂ)) ^ (-(a + c)) *
      ((u : ℂ) ^ (-(y * I)) * (Gamma (b + y * I) * Gamma (d - y * I))) =
      Gamma (c - y * I) * Gamma (a + y * I) / Gamma (a + c) *
        (Gamma (b + y * I) * Gamma (d - y * I)) := by
  have hm := integral_cpow_mul_one_add_cpow_neg (s := c - y * I) (a := a + c) (by simpa using hc)
    (by simpa using ha)
  rw [show a + c - (c - y * I) = a + y * I by ring] at hm
  rw [← hm, ← integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) ↦ ?_
  rw [show c - y * I - 1 = c - 1 + -(y * I) by ring, cpow_add _ _ (ofReal_ne_zero.mpr hu.ne')]
  ring

/-- **Barnes's first lemma** (DLMF 5.13.3). For `a`, `b`, `c`, `d` with positive real parts,
`(1 / 2π) ∫ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy` equals
`Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    ∫ y : ℝ, Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) =
      2 * π * (Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) /
        Gamma (a + b + c + d)) := by
  have hac : Gamma (a + c) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hm := integral_cpow_mul_one_add_cpow_neg (s := b + c) (a := a + b + c + d)
    (by simp; linarith) (by simp; linarith)
  rw [show a + b + c + d - (b + c) = a + d by ring] at hm
  -- integrate the kernel first in `u`, then in `y`, and swap the order by Fubini
  calc
    _ = Gamma (a + c) * ∫ y : ℝ, ∫ u in Ioi (0 : ℝ),
          (u : ℂ) ^ (c - 1) * (1 + (u : ℂ)) ^ (-(a + c)) *
            ((u : ℂ) ^ (-(y * I)) * (Gamma (b + y * I) * Gamma (d - y * I))) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
      simp only [integral_barnesKernel_Ioi ha hc]
      field_simp
    _ = Gamma (a + c) * ∫ u in Ioi (0 : ℝ),
          2 * π * Gamma (b + d) * ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + b + c + d))) := by
      rw [← integral_integral_swap (integrable_barnesKernel ha hb hc hd)]
      congr 1
      exact setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ integral_barnesKernel_im hb hd hu
    _ = _ := by
      rw [integral_const_mul, hm]
      ring

end Complex
