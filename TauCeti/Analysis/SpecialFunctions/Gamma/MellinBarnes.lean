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

This also yields **Barnes's first lemma** ([DLMF 5.13.3](https://dlmf.nist.gov/5.13.E3)): for
`a, b, c, d` with positive real parts,

`(1 / 2π) ∫ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`.

## Main results

* `Complex.hasMellin_one_add_cpow_neg`: the Mellin transform of `(1 + t)^{-a}` converges at every
  `s` with `0 < Re s < Re a` and equals `Γ(s) Γ(a - s) / Γ(a)` there.
* `Complex.verticalIntegrable_Gamma_mul_Gamma_sub` and `Complex.integrable_Gamma_add_mul_Gamma_sub`:
  `s ↦ Γ(s) Γ(a - s)` is integrable on every pole-avoiding vertical line.
* `Complex.mellinInv_Gamma_mul_Gamma_sub`, `Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_sub`, and
  `Complex.integral_cpow_neg_add_mul_Gamma_mul_Gamma`: Mellin inversion of `Γ(s) Γ(a - s)` on a
  vertical line with `0 < Re s < Re a` is `Γ(a) (1 + u)^{-a}`.
* `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`: `y ↦ Γ(a + i y) Γ(b + i y) Γ(c - i y)
  Γ(d - i y)` is integrable whenever none of `Re a, Re b, Re c, Re d` is a nonpositive integer.
* `Complex.integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma` and
  `Complex.integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub`: **Barnes's first lemma**
  (DLMF 5.13.3) at the imaginary axis and along a separating vertical line `Re s = σ`.

## References

* NIST Digital Library of Mathematical Functions, equations 5.12.3 and 5.13.3.
* E. W. Barnes, *A new development of the theory of the hypergeometric functions*, Proc. London
  Math. Soc. (2) **6** (1908), 141–177.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §§12.41 and 14.52.
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

/-- The product `y ↦ Γ(b + i y) Γ(d - i y)` is integrable whenever neither `Re b` nor `Re d` is a
nonpositive integer. -/
theorem integrable_Gamma_add_mul_Gamma_sub {b d : ℂ} (hb : ∀ n : ℕ, b.re ≠ -n)
    (hd : ∀ n : ℕ, d.re ≠ -n) :
    Integrable fun y : ℝ ↦ Gamma (b + y * I) * Gamma (d - y * I) := by
  have h := (verticalIntegrable_Gamma_mul_Gamma_sub (a := b + d) (σ := b.re) hb
    (by simpa using hd)).comp_add_right b.im
  refine h.congr (Eventually.of_forall fun y ↦ ?_)
  have hb' : (b.re : ℂ) + ((y + b.im : ℝ) : ℂ) * I = b + y * I := by
    apply Complex.ext <;> simp [add_comm]
  have hd' : b + d - (b + y * I) = d - y * I := by ring
  simp only [hb', hd']

/-- Complex-shifted Mellin–Barnes integral of `(1 + u)^{-(b + d)}`: for `0 < Re b`, `0 < Re d`, and
`0 < u`, `∫ u^{-(b + i y)} Γ(b + i y) Γ(d - i y) dy = 2π Γ(b + d) (1 + u)^{-(b + d)}`. -/
theorem integral_cpow_neg_add_mul_Gamma_mul_Gamma {b d : ℂ} (hb : 0 < b.re) (hd : 0 < d.re)
    {u : ℝ} (hu : 0 < u) :
    ∫ y : ℝ, (u : ℂ) ^ (-(b + y * I)) * (Gamma (b + y * I) * Gamma (d - y * I)) =
      2 * π * (Gamma (b + d) * (1 + (u : ℂ)) ^ (-(b + d))) := by
  let f : ℝ → ℂ := fun w ↦ (u : ℂ) ^ (-((b.re : ℂ) + w * I)) *
    (Gamma ((b.re : ℂ) + w * I) * Gamma (b + d - ((b.re : ℂ) + w * I)))
  have hshift : (fun y : ℝ ↦ (u : ℂ) ^ (-(b + y * I)) * (Gamma (b + y * I) * Gamma (d - y * I))) =
      fun y : ℝ ↦ f (y + b.im) := by
    ext y
    have hb' : (b.re : ℂ) + ((y + b.im : ℝ) : ℂ) * I = b + y * I := by
      apply Complex.ext <;> simp [add_comm]
    have hd' : b + d - (b + y * I) = d - y * I := by ring
    simp only [f, hb', hd']
  rw [hshift, integral_add_right_eq_self f b.im]
  exact integral_cpow_neg_mul_Gamma_mul_Gamma_sub hb (by simp [hd]) hu

/-- The four-Gamma product `y ↦ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y)` is integrable on `ℝ`
whenever none of `Re a`, `Re b`, `Re c`, `Re d` is a nonpositive integer. -/
theorem integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ}
    (ha : ∀ n : ℕ, a.re ≠ -n) (hb : ∀ n : ℕ, b.re ≠ -n)
    (hc : ∀ n : ℕ, c.re ≠ -n) (hd : ∀ n : ℕ, d.re ≠ -n) :
    Integrable fun y : ℝ ↦
      Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
  obtain ⟨Cb, hCb⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow hb 0
  obtain ⟨Cd, hCd⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow hd 0
  have hb_eq (y : ℝ) : b + y * I = (b.re : ℂ) + ((b.im + y : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hd_eq (y : ℝ) : d - y * I = (d.re : ℂ) + ((d.im - y : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hcont_b : Continuous fun y : ℝ ↦ Gamma (b + y * I) := by
    refine continuous_iff_continuousAt.mpr fun y ↦ ?_
    refine ((differentiableAt_Gamma _ fun m hm ↦ hb m ?_).continuousAt).comp (by fun_prop)
    simpa using congrArg re hm
  have hcont_d : Continuous fun y : ℝ ↦ Gamma (d - y * I) := by
    refine continuous_iff_continuousAt.mpr fun y ↦ ?_
    refine ((differentiableAt_Gamma _ fun m hm ↦ hd m ?_).continuousAt).comp (by fun_prop)
    simpa using congrArg re hm
  have hint := ((integrable_Gamma_add_mul_Gamma_sub ha hc).mul_bdd (c := Cb)
    hcont_b.aestronglyMeasurable
    (Eventually.of_forall fun y ↦ by simpa [hb_eq] using hCb (b.im + y))).mul_bdd (c := Cd)
    hcont_d.aestronglyMeasurable
    (Eventually.of_forall fun y ↦ by simpa [hd_eq] using hCd (d.im - y))
  exact hint.congr (Eventually.of_forall fun y ↦ by dsimp; ring)

/-- **Barnes's first lemma** ([DLMF 5.13.3](https://dlmf.nist.gov/5.13.E3)). For `a, b, c, d : ℂ`
with positive real parts,
`(2π)⁻¹ ∫ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) *
        Gamma (d - y * I) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  let F : ℝ → ℝ → ℂ := fun u y ↦
    ((u : ℂ) ^ (c - y * I - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
      (Gamma (b + y * I) * Gamma (d - y * I))
  -- Joint integrability of `F` on `Ioi 0 × ℝ`, bounded by a product of one-variable functions.
  have hf_int : Integrable (fun u : ℝ ↦ (u : ℂ) ^ (c - 1) * (1 + (u : ℂ)) ^ (-(a + c)))
      (volume.restrict (Ioi 0)) := by
    have h := (hasMellin_one_add_cpow_neg (s := c) (a := a + c) hc (by simp [ha])).1
    exact h.congr_fun (fun u _ ↦ by simp [smul_eq_mul]) measurableSet_Ioi
  have hg_int : Integrable fun y : ℝ ↦ Gamma (b + y * I) * Gamma (d - y * I) :=
    integrable_Gamma_add_mul_Gamma_sub
      (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
      (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
  have hF_meas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ, ← Measure.volume_eq_prod]
    refine (continuousOn_of_forall_continuousAt fun p hp ↦ ?_).aestronglyMeasurable
      (measurableSet_Ioi.prod MeasurableSet.univ)
    obtain ⟨hu, -⟩ := hp
    have hu0 : (0 : ℝ) < p.1 := hu
    have hu_slit : (p.1 : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hu0
    have h1u_slit : 1 + (p.1 : ℂ) ∈ slitPlane := by
      rw [← ofReal_one, ← ofReal_add]
      exact ofReal_mem_slitPlane.mpr (by linarith)
    have hc1 : ContinuousAt (fun q : ℝ × ℝ ↦ (q.1 : ℂ) ^ (c - q.2 * I - 1)) p :=
      ContinuousAt.cpow (by fun_prop) (by fun_prop) hu_slit
    have hc2 : ContinuousAt (fun q : ℝ × ℝ ↦ (1 + (q.1 : ℂ)) ^ (-(a + c))) p :=
      ContinuousAt.cpow (by fun_prop) (by fun_prop) h1u_slit
    have hc3 : ContinuousAt (fun q : ℝ × ℝ ↦ Gamma (b + q.2 * I)) p := by
      refine ((differentiableAt_Gamma _ fun m hm ↦ ?_).continuousAt).comp (by fun_prop)
      have := congrArg re hm
      simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, neg_re, natCast_re] at this
      linarith [m.cast_nonneg' (α := ℝ)]
    have hc4 : ContinuousAt (fun q : ℝ × ℝ ↦ Gamma (d - q.2 * I)) p := by
      refine ((differentiableAt_Gamma _ fun m hm ↦ ?_).continuousAt).comp (by fun_prop)
      have := congrArg re hm
      simp only [sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        neg_re, natCast_re] at this
      linarith [m.cast_nonneg' (α := ℝ)]
    exact ((hc1.mul hc2).mul (hc3.mul hc4))
  have hF_int : Integrable (Function.uncurry F) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    refine (hf_int.norm.mul_prod hg_int.norm).mono' hF_meas ?_
    rw [Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp
    obtain ⟨hu, -⟩ := hp
    have hu0 : (0 : ℝ) < p.1 := hu
    simp only [Function.uncurry, F, norm_mul, norm_cpow_eq_rpow_re_of_pos hu0]
    have hre : (c - (p.2 : ℂ) * I - 1).re = (c - 1).re := by simp
    rw [hre]
  -- Swap the order of integration on `Ioi 0 × ℝ`.
  have hswap := integral_integral_swap hF_int
  -- Evaluate the `y`-first integral via the Mellin–Barnes formula for `(1 + u)^{-(b + d)}`.
  have hlhs : ∫ u in Ioi (0 : ℝ), ∫ y : ℝ, F u y =
      2 * π * Gamma (b + d) *
        (Gamma (b + c) * Gamma (a + d) / Gamma (a + b + c + d)) := by
    have hcongr : ∀ u ∈ Ioi (0 : ℝ), ∫ y : ℝ, F u y =
        (2 * π * Gamma (b + d)) *
          ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + b + c + d))) := by
      intro u (hu : 0 < u)
      have hu_ne : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
      have h1u_ne : 1 + (u : ℂ) ≠ 0 := by
        rw [← ofReal_one, ← ofReal_add]
        exact ofReal_ne_zero.mpr (by positivity)
      have hF_eq : (fun y : ℝ ↦ F u y) = fun y : ℝ ↦
          ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
            ((u : ℂ) ^ (-(b + y * I)) * (Gamma (b + y * I) * Gamma (d - y * I))) := by
        ext y
        simp only [F]
        have hpow : (u : ℂ) ^ (c - y * I - 1) =
            (u : ℂ) ^ (b + c - 1) * (u : ℂ) ^ (-(b + y * I)) := by
          rw [← cpow_add _ _ hu_ne]
          congr 1
          ring
        rw [hpow]
        ring
      rw [hF_eq, integral_const_mul, integral_cpow_neg_add_mul_Gamma_mul_Gamma hb hd hu]
      have hpow1 : (1 + (u : ℂ)) ^ (-(a + c)) * (1 + (u : ℂ)) ^ (-(b + d)) =
          (1 + (u : ℂ)) ^ (-(a + b + c + d)) := by
        rw [← cpow_add _ _ h1u_ne]
        congr 1
        ring
      calc ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
            (2 * π * (Gamma (b + d) * (1 + (u : ℂ)) ^ (-(b + d))))
          = (2 * π * Gamma (b + d)) * ((u : ℂ) ^ (b + c - 1) *
              ((1 + (u : ℂ)) ^ (-(a + c)) * (1 + (u : ℂ)) ^ (-(b + d)))) := by ring
        _ = _ := by rw [hpow1]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul]
    have hmellin := (hasMellin_one_add_cpow_neg (s := b + c) (a := a + b + c + d)
      (by simp; linarith) (by simp; linarith)).2
    have hsub : a + b + c + d - (b + c) = a + d := by ring
    rw [mellin] at hmellin
    simp only [smul_eq_mul, hsub] at hmellin
    rw [hmellin]
  -- Evaluate the `u`-first integral via Euler's Beta integral of the second kind.
  have hrhs : (∫ y : ℝ, ∫ u in Ioi (0 : ℝ), F u y) =
      (Gamma (a + c))⁻¹ * ∫ y : ℝ,
        Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
    have hinner : ∀ y : ℝ, ∫ u in Ioi (0 : ℝ), F u y =
        (Gamma (a + c))⁻¹ *
          (Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I)) := by
      intro y
      simp only [F, integral_mul_const]
      have hmellin := (hasMellin_one_add_cpow_neg (s := c - y * I) (a := a + c)
        (by simp [hc]) (by simp [ha])).2
      have hsub : a + c - (c - y * I) = a + y * I := by ring
      rw [mellin] at hmellin
      simp only [smul_eq_mul, hsub] at hmellin
      rw [hmellin, div_eq_mul_inv]
      ring
    simp_rw [hinner, integral_const_mul]
  rw [hlhs, hrhs] at hswap
  have hΓac : Gamma (a + c) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have h2pi : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hsol := congrArg (fun w : ℂ ↦ (2 * π : ℂ)⁻¹ * (Gamma (a + c) * w)) hswap.symm
  rw [← mul_assoc (Gamma (a + c)), mul_inv_cancel₀ hΓac, one_mul] at hsol
  rw [hsol]
  field_simp [h2pi]

/-- **Barnes's first lemma** along a separating vertical line `Re s = σ`: when
`max (-Re a, -Re b) < σ < min (Re c, Re d)`,
`(2π)⁻¹ ∫ Γ(a + (σ + i y)) Γ(b + (σ + i y)) Γ(c - (σ + i y)) Γ(d - (σ + i y)) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub {a b c d : ℂ} {σ : ℝ}
    (ha : -a.re < σ) (hb : -b.re < σ) (hc : σ < c.re) (hd : σ < d.re) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - (σ + y * I)) * Gamma (d - (σ + y * I)) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  have h := integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma
    (a := a + σ) (b := b + σ) (c := c - σ) (d := d - σ)
    (by simp; linarith) (by simp; linarith) (by simp; linarith) (by simp; linarith)
  have ha' (y : ℝ) : a + ((σ : ℂ) + y * I) = a + σ + y * I := by ring
  have hb' (y : ℝ) : b + ((σ : ℂ) + y * I) = b + σ + y * I := by ring
  have hc' (y : ℝ) : c - ((σ : ℂ) + y * I) = c - σ - y * I := by ring
  have hd' (y : ℝ) : d - ((σ : ℂ) + y * I) = d - σ - y * I := by ring
  have hac : a + (σ : ℂ) + (c - σ) = a + c := by ring
  have had : a + (σ : ℂ) + (d - σ) = a + d := by ring
  have hbc : b + (σ : ℂ) + (c - σ) = b + c := by ring
  have hbd : b + (σ : ℂ) + (d - σ) = b + d := by ring
  have habcd : a + (σ : ℂ) + (b + σ) + (c - σ) + (d - σ) = a + b + c + d := by ring
  simp only [ha', hb', hc', hd']
  rw [h, hac, had, hbc, hbd, habcd]

end Complex
