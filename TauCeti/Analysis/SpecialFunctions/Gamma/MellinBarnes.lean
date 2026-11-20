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
import TauCeti.MeasureTheory.Integral.Prod

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

Inserting Euler's Beta integral of the second kind into the vertical integral of a four-Gamma
product and swapping the two integrations by Fubini's theorem proves **Barnes's first lemma**
(DLMF 5.13.3): for `a, b, c, d` in the open right half-plane,

`(1 / 2π) ∫ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`,

together with its general form on any vertical line `Re s = σ` separating the left and right pole
sequences (`max (-Re a, -Re b) < σ < min (Re c, Re d)`).

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
* `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`: integrability of
  `y ↦ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y)` away from the poles of the four factors.
* `Complex.integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`: **Barnes's first lemma** (DLMF 5.13.3)
  on `i ℝ` for `a, b, c, d` in the open right half-plane.
* `Complex.integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub`: Barnes's first lemma on a
  general separating vertical line `Re s = σ`.

## References

* NIST Digital Library of Mathematical Functions, equations 5.12.3 and 5.13.3, and §15.6 (the
  Mellin–Barnes integrals 15.6.6–15.6.7).
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §§12.41, 14.5, and 14.52.
* G. E. Andrews, R. Askey, and R. Roy, *Special Functions*, §2.4 (Theorem 2.4.2).
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
    VerticalIntegrable (fun s ↦ Gamma s * Gamma (a - s)) σ :=
  (verticalIntegrable_Gamma hσ).mul_Gamma_comp haσ (by fun_prop) fun y ↦ by simp

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

/-- The product `y ↦ Γ(b + i y) Γ(d - i y)` is integrable on `ℝ` whenever neither `Re b` nor
`Re d` is a nonpositive integer. -/
theorem integrable_Gamma_add_mul_Gamma_sub {b d : ℂ} (hb : ∀ n : ℕ, b.re ≠ -n)
    (hd : ∀ n : ℕ, d.re ≠ -n) :
    Integrable fun y : ℝ ↦ Gamma (b + y * I) * Gamma (d - y * I) := by
  have h := (verticalIntegrable_Gamma_mul_Gamma_sub (a := b + d) hb
    (by simpa using hd)).comp_add_left b.im
  refine h.congr (Eventually.of_forall fun y ↦ ?_)
  have hb' : (b.re : ℂ) + ↑(b.im + y) * I = b + y * I := by
    apply Complex.ext <;> simp
  have hd' : b + d - ((b.re : ℂ) + ↑(b.im + y) * I) = d - y * I := by
    rw [hb']
    ring
  dsimp
  rw [hd', hb']

/-- Shifted form of `integral_cpow_neg_mul_Gamma_mul_Gamma_sub`: for `Re b > 0`, `Re d > 0`, and
`u > 0`, `∫ u^{-(b + i y)} Γ(b + i y) Γ(d - i y) dy = 2π Γ(b + d) (1 + u)^{-(b + d)}`. -/
theorem integral_cpow_neg_mul_Gamma_add_mul_Gamma_sub {b d : ℂ} (hb : 0 < b.re) (hd : 0 < d.re)
    {u : ℝ} (hu : 0 < u) :
    ∫ y : ℝ, (u : ℂ) ^ (-(b + y * I)) * (Gamma (b + y * I) * Gamma (d - y * I)) =
      2 * π * (Gamma (b + d) * (1 + (u : ℂ)) ^ (-(b + d))) := by
  have hcongr (y : ℝ) :
      (u : ℂ) ^ (-(b + y * I)) * (Gamma (b + y * I) * Gamma (d - y * I)) =
        (u : ℂ) ^ (-((b.re : ℂ) + ↑(b.im + y) * I)) *
          (Gamma ((b.re : ℂ) + ↑(b.im + y) * I) *
            Gamma (b + d - ((b.re : ℂ) + ↑(b.im + y) * I))) := by
    have hb' : (b.re : ℂ) + ↑(b.im + y) * I = b + y * I := by
      apply Complex.ext <;> simp
    have hd' : b + d - ((b.re : ℂ) + ↑(b.im + y) * I) = d - y * I := by
      rw [hb']
      ring
    rw [hd', hb']
  simp_rw [hcongr]
  rw [integral_add_left_eq_self
    (fun t : ℝ ↦ (u : ℂ) ^ (-((b.re : ℂ) + t * I)) *
      (Gamma ((b.re : ℂ) + t * I) * Gamma (b + d - ((b.re : ℂ) + t * I)))) b.im]
  exact integral_cpow_neg_mul_Gamma_mul_Gamma_sub hb (by simp; linarith) hu

/-- The four-Gamma integrand of Barnes's first lemma is integrable on `ℝ` whenever none of
`Re a`, `Re b`, `Re c`, `Re d` is a nonpositive integer. -/
theorem integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ}
    (ha : ∀ n : ℕ, a.re ≠ -n) (hb : ∀ n : ℕ, b.re ≠ -n) (hc : ∀ n : ℕ, c.re ≠ -n)
    (hd : ∀ n : ℕ, d.re ≠ -n) :
    Integrable fun y : ℝ ↦
      Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
  obtain ⟨Cb, hCb⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow hb 0
  obtain ⟨Cd, hCd⟩ := exists_norm_Gamma_le_mul_inv_one_add_sq_pow hd 0
  have h_ac := integrable_Gamma_add_mul_Gamma_sub ha hc
  have h_bd_cont : Continuous fun y : ℝ ↦ Gamma (b + y * I) * Gamma (d - y * I) :=
    (continuous_Gamma_add_mul_I hb).mul (continuous_Gamma_sub_mul_I hd)
  have h_bd_bdd : ∀ y : ℝ, ‖Gamma (b + y * I) * Gamma (d - y * I)‖ ≤ Cb * Cd := by
    intro y
    have hb_eq : b + y * I = (b.re : ℂ) + ↑(b.im + y) * I := by
      apply Complex.ext <;> simp
    have hd_eq : d - y * I = (d.re : ℂ) + ↑(d.im - y) * I := by
      apply Complex.ext <;> simp [sub_eq_add_neg]
    have hb0 : ‖Gamma (b + y * I)‖ ≤ Cb := by simpa [hb_eq] using hCb (b.im + y)
    have hd0 : ‖Gamma (d - y * I)‖ ≤ Cd := by simpa [hd_eq] using hCd (d.im - y)
    rw [norm_mul]
    exact mul_le_mul hb0 hd0 (norm_nonneg _) ((norm_nonneg _).trans hb0)
  refine (h_ac.mul_bdd h_bd_cont.aestronglyMeasurable (Eventually.of_forall h_bd_bdd)).congr
    (Eventually.of_forall fun y ↦ by ring)

/-- Joint integrability on `(0, ∞) × ℝ` of the Fubini kernel used to prove Barnes's first lemma. -/
private theorem integrable_barnesKernel {a b c d : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) (hd : 0 < d.re) :
    Integrable
      (fun p : ℝ × ℝ ↦ ((p.1 : ℂ) ^ (c - p.2 * I - 1) * (1 + (p.1 : ℂ)) ^ (-(a + c))) *
        (Gamma (b + p.2 * I) * Gamma (d - p.2 * I)))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hf₁ : Integrable
      (fun u : ℝ ↦ ‖(u : ℂ) ^ (c - 1) * (1 + (u : ℂ)) ^ (-(a + c))‖)
      (volume.restrict (Ioi (0 : ℝ))) := by
    exact (integrableOn_cpow_mul_one_add_cpow_neg (s := c) (a := a + c) hc
      (by simp; linarith)).norm
  have hf₂ : Integrable (fun y : ℝ ↦ ‖Gamma (b + y * I) * Gamma (d - y * I)‖) :=
    (integrable_Gamma_add_mul_Gamma_sub
      (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
      (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])).norm
  refine (hf₁.mul_prod hf₂).mono' ?_ ?_
  · have hmeas_eq : (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ) =
        volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
      simpa [Measure.volume_eq_prod] using
        Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) (Ioi 0) univ
    rw [hmeas_eq]
    refine ContinuousOn.aestronglyMeasurable (continuousOn_of_forall_continuousAt fun p hp ↦ ?_)
      (measurableSet_Ioi.prod MeasurableSet.univ)
    have hu : 0 < p.1 := hp.1
    have hc1 : ContinuousAt (fun p : ℝ × ℝ ↦ (p.1 : ℂ) ^ (c - p.2 * I - 1)) p :=
      ContinuousAt.cpow (continuous_ofReal.continuousAt.comp continuousAt_fst) (by fun_prop)
        (ofReal_mem_slitPlane.mpr hu)
    have hc2 : ContinuousAt (fun p : ℝ × ℝ ↦ (1 + (p.1 : ℂ)) ^ (-(a + c))) p := by
      refine ContinuousAt.cpow (by fun_prop) continuousAt_const ?_
      rw [← ofReal_one, ← ofReal_add]
      exact ofReal_mem_slitPlane.mpr (by linarith)
    have hc3 : ContinuousAt (fun p : ℝ × ℝ ↦ Gamma (b + p.2 * I)) p :=
      (continuous_Gamma_add_mul_I
        (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])).continuousAt.comp continuousAt_snd
    have hc4 : ContinuousAt (fun p : ℝ × ℝ ↦ Gamma (d - p.2 * I)) p :=
      (continuous_Gamma_sub_mul_I
        (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])).continuousAt.comp continuousAt_snd
    exact (hc1.mul hc2).mul (hc3.mul hc4)
  · filter_upwards [TauCeti.ae_of_ae_fst (ae_restrict_mem measurableSet_Ioi)] with p (hu : 0 < p.1)
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hu,
      norm_cpow_eq_rpow_re_of_pos hu]
    have hre : (c - (p.2 : ℂ) * I - 1).re = (c - 1).re := by simp
    rw [hre]

/-- **Barnes's first lemma** ([DLMF 5.13.3](https://dlmf.nist.gov/5.13.E3)). For `a, b, c, d` in
the open right half-plane,
`(1 / 2π) ∫ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) *
        Gamma (d - y * I) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let F : ℝ → ℝ → ℂ := fun u y ↦
    ((u : ℂ) ^ (c - y * I - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
      (Gamma (b + y * I) * Gamma (d - y * I))
  have hF : Integrable (Function.uncurry F) (μ.prod volume) := integrable_barnesKernel ha hb hc hd
  -- Integrating in `u` first yields `(Γ(a + c))⁻¹` times the four-Gamma integral.
  have h_u_first : ∫ y : ℝ, ∫ u, F u y ∂μ =
      (Gamma (a + c))⁻¹ * ∫ y : ℝ,
        Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
    have hinner (y : ℝ) : ∫ u, F u y ∂μ =
        (Gamma (a + c))⁻¹ *
          (Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I)) := by
      have hm := (hasMellin_one_add_cpow_neg (s := c - y * I) (a := a + c)
        (by simpa using hc) (by simp; linarith)).2
      have hsub : a + c - (c - (y : ℂ) * I) = a + y * I := by ring
      simp only [mellin, smul_eq_mul, hsub] at hm
      simp only [F, μ, integral_mul_const, hm]
      ring
    simp_rw [hinner, integral_const_mul]
  -- Integrating in `y` first evaluates to `2π Γ(b + d) Γ(b + c) Γ(a + d) / Γ(a + b + c + d)`.
  have h_y_first : ∫ u, (∫ y : ℝ, F u y) ∂μ =
      2 * π * Gamma (b + d) * (Gamma (b + c) * Gamma (a + d) / Gamma (a + b + c + d)) := by
    have hinner : ∀ᵐ u ∂μ, ∫ y : ℝ, F u y =
        2 * π * Gamma (b + d) *
          ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + b + c + d))) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
      have hsplit (y : ℝ) : F u y =
          ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
            ((u : ℂ) ^ (-(b + y * I)) * (Gamma (b + y * I) * Gamma (d - y * I))) := by
        have hexp : c - (y : ℂ) * I - 1 = (b + c - 1) + (-(b + y * I)) := by ring
        simp only [F, hexp, cpow_add _ _ (ofReal_ne_zero.mpr hu.ne')]
        ring
      have h1pow : (1 + (u : ℂ)) ^ (-(a + c)) * (1 + (u : ℂ)) ^ (-(b + d)) =
          (1 + (u : ℂ)) ^ (-(a + b + c + d)) := by
        rw [← cpow_add _ _ (by exact_mod_cast (by positivity : (1 : ℝ) + u ≠ 0))]
        congr 1
        ring
      simp_rw [hsplit]
      rw [integral_const_mul, integral_cpow_neg_mul_Gamma_add_mul_Gamma_sub hb hd hu]
      calc ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
              (2 * π * (Gamma (b + d) * (1 + (u : ℂ)) ^ (-(b + d))))
          = 2 * π * Gamma (b + d) *
              ((u : ℂ) ^ (b + c - 1) * ((1 + (u : ℂ)) ^ (-(a + c)) *
                (1 + (u : ℂ)) ^ (-(b + d)))) := by ring
        _ = 2 * π * Gamma (b + d) *
              ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + b + c + d))) := by rw [h1pow]
    rw [integral_congr_ae hinner, integral_const_mul]
    have hm := (hasMellin_one_add_cpow_neg (s := b + c) (a := a + b + c + d)
      (by simp; linarith) (by simp; linarith)).2
    have hsub : a + b + c + d - (b + c) = a + d := by ring
    simp only [mellin, smul_eq_mul, hsub] at hm
    exact congrArg (2 * π * Gamma (b + d) * ·) hm
  have hswap : ∫ u, (∫ y : ℝ, F u y) ∂μ = ∫ y : ℝ, ∫ u, F u y ∂μ := integral_integral_swap hF
  rw [h_y_first, h_u_first] at hswap
  have hΓac : Gamma (a + c) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have h2pi : (2 * π : ℂ) ≠ 0 := by norm_num [Real.pi_ne_zero]
  calc (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) *
          Gamma (d - y * I)
      = (2 * π : ℂ)⁻¹ * Gamma (a + c) * ((Gamma (a + c))⁻¹ *
          ∫ y : ℝ, Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) *
            Gamma (d - y * I)) := by
          rw [mul_assoc, mul_inv_cancel_left₀ hΓac]
    _ = (2 * π : ℂ)⁻¹ * Gamma (a + c) *
          (2 * π * Gamma (b + d) * (Gamma (b + c) * Gamma (a + d) / Gamma (a + b + c + d))) := by
          rw [← hswap]
    _ = Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) /
          Gamma (a + b + c + d) := by
          field_simp [h2pi]

/-- **Barnes's first lemma** on a general vertical line `Re s = σ` separating the poles of
`Γ(a + s) Γ(b + s)` from those of `Γ(c - s) Γ(d - s)`: for `max (-Re a, -Re b) < σ <
min (Re c, Re d)`,
`(1 / 2π) ∫ Γ(a + σ + i y) Γ(b + σ + i y) Γ(c - σ - i y) Γ(d - σ - i y) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub {a b c d : ℂ} {σ : ℝ}
    (ha : -a.re < σ) (hb : -b.re < σ) (hc : σ < c.re) (hd : σ < d.re) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ,
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - (σ + y * I)) * Gamma (d - (σ + y * I)) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  have h := integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma
    (a := a + σ) (b := b + σ) (c := c - σ) (d := d - σ)
    (by simp; linarith) (by simp; linarith) (by simp; linarith) (by simp; linarith)
  have hcongr (y : ℝ) :
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - (σ + y * I)) * Gamma (d - (σ + y * I)) =
        Gamma (a + σ + y * I) * Gamma (b + σ + y * I) *
          Gamma (c - σ - y * I) * Gamma (d - σ - y * I) := by
    simp only [← add_assoc, sub_add_eq_sub_sub]
  have hsum : a + (σ : ℂ) + (b + σ) + (c - σ) + (d - σ) = a + b + c + d := by ring
  simp_rw [hcongr]
  simpa only [add_add_sub_cancel, hsum] using h

end Complex
