/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical

/-!
# Barnes's first lemma

Barnes's first lemma (DLMF 5.13.3) evaluates the Mellin–Barnes integral of a product of four
Gamma functions: when the vertical line `Re s = σ` separates the poles of `Γ(a + s) Γ(b + s)` on
the left from those of `Γ(c - s) Γ(d - s)` on the right, that is, when
`max (-Re a, -Re b) < σ < min (Re c, Re d)`,

`(1 / 2π) ∫_{-∞}^∞ Γ(a + σ + i y) Γ(b + σ + i y) Γ(c - σ - i y) Γ(d - σ - i y) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`.

In particular, when `a, b, c, d` all have positive real part we may take `σ = 0`. Conversely, the
separating-line form follows immediately from the imaginary-axis case applied to
`(a + σ, b + σ, c - σ, d - σ)`.

Following the classical real-variable proof via Euler's Beta integral of the second kind
(`Complex.hasMellin_one_add_cpow_neg`) and its Mellin–Barnes inversion
(`Complex.integral_cpow_neg_mul_Gamma_add_mul_Gamma_sub`), we consider the two-variable kernel

`F(u, y) = u^{c - i y - 1} (1 + u)^{-(a + c)} Γ(b + i y) Γ(d - i y)`   on `(0, ∞) × ℝ`.

For `u > 0` the complex powers have norms `u^{Re c - 1}` and `(1 + u)^{-Re(a + c)}` independent of
`y`, so `‖F(u, y)‖` factors as the product of an integrable Beta kernel on `(0, ∞)` and the
integrable vertical product `‖Γ(b + i y) Γ(d - i y)‖` on `ℝ`. Fubini's theorem therefore equates
the two iterated integrals: integrating in `u` first yields `Γ(a + c)⁻¹` times the Barnes integral,
while integrating in `y` first inserts the Mellin–Barnes representation of `(1 + u)^{-(b + d)}` and
reduces the outer `u`-integral to a single Beta integral of the second kind.

## Main results

* `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`: integrability of
  `y ↦ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y)` on `ℝ` whenever none of
  `Re a, Re b, Re c, Re d` is a nonpositive integer.
* `Complex.verticalIntegrable_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub`: vertical
  integrability of `s ↦ Γ(a + s) Γ(b + s) Γ(c - s) Γ(d - s)` on every pole-free vertical line
  `Re s = σ`.
* `Complex.integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`: Barnes's first lemma on the imaginary
  axis for `Re a, Re b, Re c, Re d > 0` (DLMF 5.13.3).
* `Complex.integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub`: the unnormalised
  separating-line integral `∫ Γ(a + σ + i y) Γ(b + σ + i y) Γ(c - σ - i y) Γ(d - σ - i y) dy =
  2π Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)` for
  `max (-Re a, -Re b) < σ < min (Re c, Re d)`.
* `Complex.mellinInv_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub_one`: the `(1 / 2π)`
  normalised form expressed as `mellinInv σ (fun s ↦ Γ(a + s) Γ(b + s) Γ(c - s) Γ(d - s)) 1`.

## References

* NIST Digital Library of Mathematical Functions, equation 5.13.3 (<https://dlmf.nist.gov/5.13.E3>)
  and §15.6 (<https://dlmf.nist.gov/15.6>).
* E. W. Barnes, *A new development of the theory of the hypergeometric functions*, Proc. London
  Math. Soc. (2) **6** (1908), 141–177.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §14.52.
* G. E. Andrews, R. Askey, and R. Roy, *Special Functions*, Theorem 2.4.2.
-/

public section

open Real Set MeasureTheory Filter Function
open Complex hiding exp continuous_exp log

namespace Complex

/-- On the imaginary axis, the Barnes product
`y ↦ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y)` is integrable whenever none of
`Re a, Re b, Re c, Re d` is a nonpositive integer. -/
theorem integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ}
    (ha : ∀ n : ℕ, a.re ≠ -n) (hb : ∀ n : ℕ, b.re ≠ -n)
    (hc : ∀ n : ℕ, c.re ≠ -n) (hd : ∀ n : ℕ, d.re ≠ -n) :
    Integrable fun y : ℝ ↦
      Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
  obtain ⟨Cb, hCb⟩ := exists_norm_Gamma_add_mul_I_le hb
  obtain ⟨Cc, hCc⟩ := exists_norm_Gamma_sub_mul_I_le hc
  obtain ⟨Cd, hCd⟩ := exists_norm_Gamma_sub_mul_I_le hd
  exact (((integrable_Gamma_add_mul_I ha).mul_bdd
      (continuous_Gamma_add_mul_I hb).aestronglyMeasurable (Eventually.of_forall hCb)).mul_bdd
      (continuous_Gamma_sub_mul_I hc).aestronglyMeasurable (Eventually.of_forall hCc)).mul_bdd
      (continuous_Gamma_sub_mul_I hd).aestronglyMeasurable (Eventually.of_forall hCd)

/-- On every vertical line `Re s = σ` avoiding the poles of all four factors, the Barnes kernel
`s ↦ Γ(a + s) Γ(b + s) Γ(c - s) Γ(d - s)` is integrable. -/
theorem verticalIntegrable_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub {a b c d : ℂ}
    {σ : ℝ} (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hc : ∀ n : ℕ, c.re - σ ≠ -n) (hd : ∀ n : ℕ, d.re - σ ≠ -n) :
    VerticalIntegrable
      (fun s ↦ Gamma (a + s) * Gamma (b + s) * Gamma (c - s) * Gamma (d - s)) σ := by
  have hint := integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma
    (a := a + σ) (b := b + σ) (c := c - σ) (d := d - σ)
    (by simpa using ha) (by simpa using hb) (by simpa using hc) (by simpa using hd)
  refine hint.congr (Eventually.of_forall fun y ↦ ?_)
  have ha_eq : a + (σ + y * I) = a + σ + y * I := by ring
  have hb_eq : b + (σ + y * I) = b + σ + y * I := by ring
  have hc_eq : c - (σ + y * I) = c - σ - y * I := by ring
  have hd_eq : d - (σ + y * I) = d - σ - y * I := by ring
  simp only [ha_eq, hb_eq, hc_eq, hd_eq]

/-- The two-variable Fubini kernel `u^{c - i y - 1} (1 + u)^{-(a + c)} Γ(b + i y) Γ(d - i y)` whose
iterated integrals over `(0, ∞)` and `ℝ` equate the Barnes integral to a product of Beta
integrals. -/
private noncomputable def barnesFubiniKernel (a b c d : ℂ) (u y : ℝ) : ℂ :=
  (u : ℂ) ^ (c - y * I - 1) * (1 + (u : ℂ)) ^ (-(a + c)) *
    (Gamma (b + y * I) * Gamma (d - y * I))

/-- When `Re a, Re b, Re c, Re d > 0`, `barnesFubiniKernel a b c d` is integrable on the product
measure `(volume.restrict (Ioi 0)).prod volume`, because its norm factors as a product of an
integrable Beta kernel in `u` and an integrable two-Gamma vertical product in `y`. -/
private lemma integrable_barnesFubiniKernel {a b c d : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) (hd : 0 < d.re) :
    Integrable (uncurry (barnesFubiniKernel a b c d))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hbpole : ∀ n : ℕ, b.re ≠ -n := fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  have hdpole : ∀ n : ℕ, d.re ≠ -n := fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  -- Factored majorant `gu u * hy y` on `Ioi 0 × ℝ`
  let gu : ℝ → ℝ := fun u ↦
    ‖(u : ℂ) ^ ((c.re : ℂ) - 1) * (1 + (u : ℂ)) ^ (-((a.re + c.re : ℝ) : ℂ))‖
  let hy : ℝ → ℝ := fun y ↦ ‖Gamma (b + y * I) * Gamma (d - y * I)‖
  have hgu : Integrable gu (volume.restrict (Ioi (0 : ℝ))) := by
    simpa only [MellinConvergent, IntegrableOn, smul_eq_mul, gu] using
      (hasMellin_one_add_cpow_neg (s := (c.re : ℂ)) (a := ((a.re + c.re : ℝ) : ℂ))
        (by simpa using hc) (by simp; linarith)).1.norm
  have hhy : Integrable hy volume := (integrable_Gamma_add_mul_Gamma_sub hbpole hdpole).norm
  have hmeas_eq : (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ) =
      (volume : Measure (ℝ × ℝ)).restrict (Ioi (0 : ℝ) ×ˢ univ) := by
    symm
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hcont : ContinuousOn (uncurry (barnesFubiniKernel a b c d)) (Ioi (0 : ℝ) ×ˢ univ) := by
    have hc1 : ContinuousOn (fun z : ℝ × ℝ ↦ (z.1 : ℂ) ^ (c - z.2 * I - 1))
        (Ioi (0 : ℝ) ×ˢ univ) :=
      ContinuousOn.cpow (by fun_prop) (by fun_prop) fun z hz ↦ ofReal_mem_slitPlane.mpr hz.1
    have hc2 : ContinuousOn (fun z : ℝ × ℝ ↦ (1 + (z.1 : ℂ)) ^ (-(a + c)))
        (Ioi (0 : ℝ) ×ˢ univ) := by
      refine ContinuousOn.cpow_const (by fun_prop) fun z hz ↦ ?_
      rw [← ofReal_one, ← ofReal_add]
      exact ofReal_mem_slitPlane.mpr (by linarith [show 0 < z.1 from hz.1])
    have hc3 : Continuous (fun z : ℝ × ℝ ↦ Gamma (b + z.2 * I) * Gamma (d - z.2 * I)) :=
      ((continuous_Gamma_add_mul_I hbpole).mul (continuous_Gamma_sub_mul_I hdpole)).comp
        continuous_snd
    exact (hc1.mul hc2).mul hc3.continuousOn
  refine (hgu.mul_prod hhy).mono' ?_ ?_
  · rw [hmeas_eq]
    exact hcont.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ)
  · rw [hmeas_eq]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with z hz
    have hu : 0 < z.1 := hz.1
    have h1u : 0 < 1 + z.1 := by linarith
    have h1u_eq : (1 : ℂ) + (z.1 : ℂ) = ((1 + z.1 : ℝ) : ℂ) := by push_cast; ring
    simp only [uncurry, barnesFubiniKernel, gu, hy, norm_mul, h1u_eq,
      norm_cpow_eq_rpow_re_of_pos hu, norm_cpow_eq_rpow_re_of_pos h1u]
    simp only [sub_re, mul_I_re, ofReal_im, neg_zero, sub_zero, one_re, ofReal_re, neg_re, add_re]
    exact le_rfl

/-- Integrating `barnesFubiniKernel a b c d u y` in `u ∈ (0, ∞)` evaluates the Mellin transform of
`(1 + u)^{-(a + c)}` at `c - i y`. -/
private lemma integral_Ioi_barnesFubiniKernel {a b c d : ℂ} (ha : 0 < a.re) (hc : 0 < c.re)
    (y : ℝ) :
    ∫ u in Ioi (0 : ℝ), barnesFubiniKernel a b c d u y =
      (Gamma (a + c))⁻¹ *
        (Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I)) := by
  simp only [barnesFubiniKernel, integral_mul_const]
  have hm := (hasMellin_one_add_cpow_neg (s := c - y * I) (a := a + c)
    (by simpa using hc) (by simp; linarith)).2
  simp only [mellin, smul_eq_mul] at hm
  have hsub : a + c - (c - y * I) = a + y * I := by ring
  rw [hm, hsub, div_eq_mul_inv]
  ring

/-- Integrating `barnesFubiniKernel a b c d u y` in `y ∈ ℝ` for `u > 0` applies the Mellin–Barnes
formula `Complex.integral_cpow_neg_mul_Gamma_add_mul_Gamma_sub` at `(b, d)`. -/
private lemma integral_real_barnesFubiniKernel {a b c d : ℂ} (hb : 0 < b.re) (hd : 0 < d.re)
    {u : ℝ} (hu : 0 < u) :
    ∫ y : ℝ, barnesFubiniKernel a b c d u y =
      (2 * π * Gamma (b + d)) *
        ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + b + c + d))) := by
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
  have h1u0 : (1 : ℂ) + (u : ℂ) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_add]
    exact ofReal_ne_zero.mpr (by linarith)
  have hsplit (y : ℝ) :
      barnesFubiniKernel a b c d u y =
        ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
          ((u : ℂ) ^ (-(b + y * I)) * (Gamma (b + y * I) * Gamma (d - y * I))) := by
    have hexp : c - y * I - 1 = (b + c - 1) + -(b + y * I) := by ring
    simp only [barnesFubiniKernel, hexp, cpow_add _ _ hu0]
    ring
  simp_rw [hsplit, integral_const_mul, integral_cpow_neg_mul_Gamma_add_mul_Gamma_sub hb hd hu]
  calc ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
        (2 * π * (Gamma (b + d) * (1 + (u : ℂ)) ^ (-(b + d)))) =
      (2 * π * Gamma (b + d)) *
        ((u : ℂ) ^ (b + c - 1) * ((1 + (u : ℂ)) ^ (-(a + c)) * (1 + (u : ℂ)) ^ (-(b + d)))) := by
        ring
    _ = _ := by
      rw [← cpow_add _ _ h1u0]
      congr 3
      ring

/-- **Barnes's first lemma** (DLMF 5.13.3). For complex parameters `a, b, c, d` with positive real
parts,
`(1 / 2π) ∫_{-∞}^∞ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) *
        Gamma (d - y * I) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  have hswap := integral_integral_swap (integrable_barnesFubiniKernel ha hb hc hd)
  -- Left-hand side of Fubini: integrate `y` first, then `u ∈ Ioi 0`
  have hlhs : (∫ u in Ioi (0 : ℝ), ∫ y : ℝ, barnesFubiniKernel a b c d u y) =
      (2 * π * Gamma (b + d)) *
        (Gamma (b + c) * Gamma (a + d) / Gamma (a + b + c + d)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi
      fun u (hu : 0 < u) ↦ integral_real_barnesFubiniKernel hb hd hu, integral_const_mul]
    have hm := (hasMellin_one_add_cpow_neg (s := b + c) (a := a + b + c + d)
      (by simp; linarith) (by simp; linarith)).2
    simp only [mellin, smul_eq_mul] at hm
    have hsub : a + b + c + d - (b + c) = a + d := by ring
    rw [hm, hsub]
  -- Right-hand side of Fubini: integrate `u` first, then `y ∈ ℝ`
  have hrhs : (∫ y : ℝ, ∫ u in Ioi (0 : ℝ), barnesFubiniKernel a b c d u y) =
      (Gamma (a + c))⁻¹ * ∫ y : ℝ,
        Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
    simp_rw [integral_Ioi_barnesFubiniKernel ha hc, integral_const_mul]
  rw [hlhs, hrhs] at hswap
  have hΓac : Gamma (a + c) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have h2π : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  calc (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) *
          Gamma (d - y * I) =
        (2 * π : ℂ)⁻¹ * Gamma (a + c) *
          ((Gamma (a + c))⁻¹ * ∫ y : ℝ,
            Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I)) := by
        rw [mul_assoc ((2 * π : ℂ)⁻¹), ← mul_assoc (Gamma (a + c)),
          mul_inv_cancel₀ hΓac, one_mul]
    _ = (2 * π : ℂ)⁻¹ * Gamma (a + c) *
          ((2 * π * Gamma (b + d)) *
            (Gamma (b + c) * Gamma (a + d) / Gamma (a + b + c + d))) := by
        rw [← hswap]
    _ = _ := by
        field_simp [h2π]

/-- **Barnes's first lemma** on a separating vertical line `Re s = σ` (DLMF 5.13.3), as an
unnormalised vertical integral: whenever `-Re a < σ`, `-Re b < σ`, `σ < Re c`, and `σ < Re d`, so
that the vertical line `Re s = σ` separates the poles of `Γ(a + s) Γ(b + s)` from those of
`Γ(c - s) Γ(d - s)`,
`∫_{-∞}^∞ Γ(a + σ + i y) Γ(b + σ + i y) Γ(c - σ - i y) Γ(d - σ - i y) dy =
  2π Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub {a b c d : ℂ} {σ : ℝ}
    (ha : -a.re < σ) (hb : -b.re < σ) (hc : σ < c.re) (hd : σ < d.re) :
    ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - (σ + y * I)) * Gamma (d - (σ + y * I)) =
      2 * π * (Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) /
        Gamma (a + b + c + d)) := by
  have h := integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma
    (a := a + σ) (b := b + σ) (c := c - σ) (d := d - σ)
    (by simp; linarith) (by simp; linarith) (by simp; linarith) (by simp; linarith)
  have hcongr : (∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - (σ + y * I)) * Gamma (d - (σ + y * I))) =
      ∫ y : ℝ, Gamma (a + σ + y * I) * Gamma (b + σ + y * I) *
        Gamma (c - σ - y * I) * Gamma (d - σ - y * I) := by
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    have ha_eq : a + (σ + y * I) = a + σ + y * I := by ring
    have hb_eq : b + (σ + y * I) = b + σ + y * I := by ring
    have hc_eq : c - (σ + y * I) = c - σ - y * I := by ring
    have hd_eq : d - (σ + y * I) = d - σ - y * I := by ring
    simp only [ha_eq, hb_eq, hc_eq, hd_eq]
  have hac : a + σ + (c - σ) = a + c := by ring
  have had : a + σ + (d - σ) = a + d := by ring
  have hbc : b + σ + (c - σ) = b + c := by ring
  have hbd : b + σ + (d - σ) = b + d := by ring
  have habcd : a + σ + (b + σ) + (c - σ) + (d - σ) = a + b + c + d := by ring
  rw [hac, had, hbc, hbd, habcd] at h
  have h2π : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [hcongr, ← h, ← mul_assoc, mul_inv_cancel₀ h2π, one_mul]

/-- **Barnes's first lemma** in terms of `mellinInv` at `1`: on every separating vertical line
`Re s = σ` with `-Re a, -Re b < σ < Re c, Re d`, the inverse Mellin transform of
`s ↦ Γ(a + s) Γ(b + s) Γ(c - s) Γ(d - s)` at `1` equals
`Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem mellinInv_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub_one {a b c d : ℂ} {σ : ℝ}
    (ha : -a.re < σ) (hb : -b.re < σ) (hc : σ < c.re) (hd : σ < d.re) :
    mellinInv σ (fun s ↦ Gamma (a + s) * Gamma (b + s) * Gamma (c - s) * Gamma (d - s)) 1 =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  have h2π : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [mellinInv, real_smul]
  simp only [ofReal_one, one_cpow, one_smul, one_div, ofReal_inv, ofReal_mul, ofReal_ofNat]
  rw [integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub ha hb hc hd,
    ← mul_assoc, inv_mul_cancel₀ h2π, one_mul]

-- Concrete checks: the symmetric half-integer case `(1/2, 1/2, 1/2, 1/2)` on the imaginary axis,
-- and the `(1, 1, 1, 0)` case on the separating line `Re s = -1/2` where `Re d = 0`.
example :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ,
        Gamma (1 / 2 + y * I) ^ 2 * Gamma (1 / 2 - y * I) ^ 2 = 1 := by
  have h := integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma
    (a := 1 / 2) (b := 1 / 2) (c := 1 / 2) (d := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hcongr : (∫ y : ℝ, Gamma (1 / 2 + y * I) ^ 2 * Gamma (1 / 2 - y * I) ^ 2) =
      ∫ y : ℝ, Gamma (1 / 2 + y * I) * Gamma (1 / 2 + y * I) *
        Gamma (1 / 2 - y * I) * Gamma (1 / 2 - y * I) :=
    integral_congr_ae (Eventually.of_forall fun y ↦ by ring)
  rw [hcongr, h]
  norm_num [Gamma_one, Gamma_nat_eq_factorial]

example :
    (∫ y : ℝ,
        Gamma (1 + ((-1 / 2 : ℝ) + y * I)) * Gamma (1 + ((-1 / 2 : ℝ) + y * I)) *
          Gamma (1 - ((-1 / 2 : ℝ) + y * I)) * Gamma (-((-1 / 2 : ℝ) + y * I))) = π := by
  have h := integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub
    (a := 1) (b := 1) (c := 1) (d := 0) (σ := -1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only [zero_sub] at h
  rw [h]
  norm_num [Gamma_one, Gamma_nat_eq_factorial, Nat.factorial]
  ring

end Complex
