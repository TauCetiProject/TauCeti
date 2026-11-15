/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical

/-!
# Barnes's first lemma

**Barnes's first lemma** (DLMF 5.13.3) evaluates the vertical-line integral of a product of four
Gamma functions, two increasing and two decreasing along the imaginary axis: for complex parameters
`a, b, c, d` with positive real parts,

`(2π)⁻¹ ∫_{-∞}^∞ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy =`
`  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`.

More generally, if a vertical line `Re s = σ` separates the poles `-a - ℕ` and `-b - ℕ` of
`Γ(a + s) Γ(b + s)` on the left from the poles `c + ℕ` and `d + ℕ` of `Γ(c - s) Γ(d - s)` on the
right (`max(-Re a, -Re b) < σ < min(Re c, Re d)`), shifting `(a, b, c, d)` to
`(a + σ, b + σ, c - σ, d - σ)` evaluates the integral along `Re s = σ` without requiring `c` or
`d` themselves to lie in the right half-plane. In particular, taking `d = n ∈ ℕ` on a separating
line with `σ < 0` evaluates the coefficients arising when `(1 - z)^s` is expanded in powers of `z`
inside the Mellin–Barnes representation of the Gauss hypergeometric function (DLMF 15.6.7).

We follow the Mellin–Barnes–Fubini proof: consider the kernel

`F(u, y) = u^{c - i y - 1} (1 + u)^{-(a + c)} Γ(b + i y) Γ(d - i y)`

on `(0, ∞) × ℝ`. Since `‖u^{c - i y - 1}‖ = u^{Re c - 1}` is independent of `y`, `‖F(u, y)‖`
factors as a product of an integrable Beta-type weight on `(0, ∞)` and the integrable vertical
product `‖Γ(b + i y) Γ(d - i y)‖` on `ℝ`, giving joint integrability on `(0, ∞) × ℝ`. Integrating
first in `u` applies Euler's Beta integral of the second kind (`Complex.hasMellin_one_add_cpow_neg`)
at `s = c - i y`, producing `Γ(a + c)⁻¹` times the Barnes integrand; integrating first in `y`
applies the Mellin–Barnes representation of `(1 + u)^{-(b + d)}`
(`Complex.integral_cpow_neg_mul_Gamma_add_mul_Gamma_sub`), leaving a second Beta integral on
`(0, ∞)` that evaluates to `2π Γ(b + d) Γ(b + c) Γ(a + d) / Γ(a + b + c + d)`.

## Main results

* `Complex.exists_norm_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_le_mul_inv_one_add_sq_pow`: on any
  vertical line avoiding the poles of all four factors, the four-Gamma Barnes integrand decays
  faster than every power `(1 + y²)⁻ᵐ`.
* `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma` and
  `Complex.verticalIntegrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`: integrability of the four-Gamma
  Barnes integrand on every pole-free vertical line.
* `Complex.integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`: **Barnes's first lemma** (DLMF 5.13.3)
  for `Re a, Re b, Re c, Re d > 0`.
* `Complex.integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_vertical`: Barnes's first lemma along a
  separating vertical line `Re s = σ` with `-Re a, -Re b < σ < Re c, Re d`.

## References

* E. W. Barnes, *A new development of the theory of the hypergeometric functions*, Proc. London
  Math. Soc. (2) **6** (1908), 141–177.
* NIST Digital Library of Mathematical Functions, equations 5.13.3 and 15.6.7.
* G. E. Andrews, R. Askey, and R. Roy, *Special Functions*, Theorem 2.4.2.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §14.52.
-/

public section

open Real Set MeasureTheory Filter Function
open scoped Real
open Complex hiding exp continuous_exp log

namespace Complex

/-- Along any vertical line avoiding the poles of all four factors, the four-Gamma Barnes integrand
`y ↦ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y)` decays faster than every power of `|y|`: for
every `m`, its norm is bounded by a constant multiple of `(1 + y²)⁻ᵐ`. -/
theorem exists_norm_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_le_mul_inv_one_add_sq_pow {a b c d : ℂ}
    (ha : ∀ n : ℕ, a.re ≠ -n) (hb : ∀ n : ℕ, b.re ≠ -n)
    (hc : ∀ n : ℕ, c.re ≠ -n) (hd : ∀ n : ℕ, d.re ≠ -n) (m : ℕ) :
    ∃ C : ℝ, ∀ y : ℝ,
      ‖Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I)‖ ≤
        C * ((1 + y ^ 2) ^ m)⁻¹ := by
  obtain ⟨Ca, hCa⟩ := exists_norm_Gamma_add_mul_I_le_mul_inv_one_add_sq_pow ha m
  obtain ⟨Cb, hCb⟩ := exists_norm_Gamma_add_mul_I_le_mul_inv_one_add_sq_pow hb 0
  obtain ⟨Cc, hCc⟩ := exists_norm_Gamma_add_mul_I_le_mul_inv_one_add_sq_pow hc 0
  obtain ⟨Cd, hCd⟩ := exists_norm_Gamma_add_mul_I_le_mul_inv_one_add_sq_pow hd 0
  have hCa0 : 0 ≤ Ca := by simpa using (norm_nonneg _).trans (hCa 0)
  have hCb0 : 0 ≤ Cb := by simpa using (norm_nonneg _).trans (hCb 0)
  have hCc0 : 0 ≤ Cc := by simpa using (norm_nonneg _).trans (hCc 0)
  refine ⟨Ca * Cb * Cc * Cd, fun y ↦ ?_⟩
  have hb' : ‖Gamma (b + y * I)‖ ≤ Cb := by simpa using hCb y
  have hc' : ‖Gamma (c - y * I)‖ ≤ Cc := by simpa [sub_eq_add_neg] using hCc (-y)
  have hd' : ‖Gamma (d - y * I)‖ ≤ Cd := by simpa [sub_eq_add_neg] using hCd (-y)
  have h12 : ‖Gamma (a + y * I)‖ * ‖Gamma (b + y * I)‖ ≤ Ca * ((1 + y ^ 2) ^ m)⁻¹ * Cb :=
    mul_le_mul (hCa y) hb' (norm_nonneg _) (by positivity)
  have h123 :
      ‖Gamma (a + y * I)‖ * ‖Gamma (b + y * I)‖ * ‖Gamma (c - y * I)‖ ≤
        Ca * ((1 + y ^ 2) ^ m)⁻¹ * Cb * Cc :=
    mul_le_mul h12 hc' (norm_nonneg _) (by positivity)
  have h1234 :
      ‖Gamma (a + y * I)‖ * ‖Gamma (b + y * I)‖ * ‖Gamma (c - y * I)‖ * ‖Gamma (d - y * I)‖ ≤
        Ca * ((1 + y ^ 2) ^ m)⁻¹ * Cb * Cc * Cd :=
    mul_le_mul h123 hd' (norm_nonneg _) (by positivity)
  have hrhs : Ca * ((1 + y ^ 2) ^ m)⁻¹ * Cb * Cc * Cd =
      Ca * Cb * Cc * Cd * ((1 + y ^ 2) ^ m)⁻¹ := by ring
  simpa only [norm_mul, hrhs] using h1234

/-- Along every vertical line avoiding the poles of all four factors, the four-Gamma Barnes
integrand `y ↦ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y)` is integrable. -/
theorem integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ}
    (ha : ∀ n : ℕ, a.re ≠ -n) (hb : ∀ n : ℕ, b.re ≠ -n)
    (hc : ∀ n : ℕ, c.re ≠ -n) (hd : ∀ n : ℕ, d.re ≠ -n) :
    Integrable fun y : ℝ ↦
      Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
  obtain ⟨C, hC⟩ :=
    exists_norm_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_le_mul_inv_one_add_sq_pow ha hb hc hd 1
  have hcont_c : Continuous fun y : ℝ ↦ Gamma (c - y * I) := by
    simpa [comp_def, sub_eq_add_neg] using (continuous_Gamma_add_mul_I hc).comp continuous_neg
  have hcont_d : Continuous fun y : ℝ ↦ Gamma (d - y * I) := by
    simpa [comp_def, sub_eq_add_neg] using (continuous_Gamma_add_mul_I hd).comp continuous_neg
  have hcont : Continuous fun y : ℝ ↦
      Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) :=
    (((continuous_Gamma_add_mul_I ha).mul (continuous_Gamma_add_mul_I hb)).mul hcont_c).mul hcont_d
  exact (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun y ↦ by simpa using hC y)

/-- On every vertical line `Re s = σ` avoiding the poles of all four factors,
`s ↦ Γ(a + s) Γ(b + s) Γ(c - s) Γ(d - s)` is `VerticalIntegrable`. -/
theorem verticalIntegrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hc : ∀ n : ℕ, c.re - σ ≠ -n) (hd : ∀ n : ℕ, d.re - σ ≠ -n) :
    VerticalIntegrable
      (fun s ↦ Gamma (a + s) * Gamma (b + s) * Gamma (c - s) * Gamma (d - s)) σ := by
  have h := integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma (a := a + σ) (b := b + σ)
    (c := c - σ) (d := d - σ) (by simpa using ha) (by simpa using hb)
    (by simpa using hc) (by simpa using hd)
  exact h.congr (Eventually.of_forall fun y ↦ by simp only [add_assoc, sub_add_eq_sub_sub])

/-- The two-variable Fubini kernel `u^{c - i y - 1} (1 + u)^{-(a + c)} Γ(b + i y) Γ(d - i y)` on
`(0, ∞) × ℝ` used in the proof of Barnes's first lemma. -/
private noncomputable def barnesKernel (a b c d : ℂ) (u y : ℝ) : ℂ :=
  ((u : ℂ) ^ (c - y * I - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
    (Gamma (b + y * I) * Gamma (d - y * I))

/-- Joint integrability of `barnesKernel a b c d` on `(0, ∞) × ℝ` for
`Re a, Re b, Re c, Re d > 0`. -/
private theorem integrable_barnesKernel {a b c d : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) (hd : 0 < d.re) :
    Integrable (uncurry (barnesKernel a b c d)) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hb' : ∀ n : ℕ, b.re ≠ -n := fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  have hd' : ∀ n : ℕ, d.re ≠ -n := fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  have hg : Integrable (fun u : ℝ ↦ ‖(u : ℂ) ^ (c - 1) * (1 + (u : ℂ)) ^ (-(a + c))‖)
      (volume.restrict (Ioi (0 : ℝ))) := by
    simpa only [smul_eq_mul] using
      (hasMellin_one_add_cpow_neg (s := c) (a := a + c) hc (by simp [ha])).1.norm
  have hh : Integrable (fun y : ℝ ↦ ‖Gamma (b + y * I) * Gamma (d - y * I)‖) volume :=
    (integrable_Gamma_add_mul_Gamma_sub hb' hd').norm
  refine (hg.mul_prod hh).mono' ?_ ?_
  · rw [Measure.restrict_prod_eq_prod_univ]
    refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioi.prod MeasurableSet.univ)
    intro z hz
    have hz1 : 0 < z.1 := hz.1
    have hpow1 : ContinuousWithinAt (fun p : ℝ × ℝ ↦ (p.1 : ℂ) ^ (c - (p.2 : ℂ) * I - 1))
        (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) z :=
      ContinuousWithinAt.cpow (by fun_prop) (by fun_prop) (ofReal_mem_slitPlane.mpr hz1)
    have hpow2 : ContinuousWithinAt (fun p : ℝ × ℝ ↦ (1 + (p.1 : ℂ)) ^ (-(a + c)))
        (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) z := by
      refine ContinuousWithinAt.cpow (by fun_prop) (by fun_prop) ?_
      rw [← ofReal_one, ← ofReal_add]
      exact ofReal_mem_slitPlane.mpr (by linarith)
    have hGb : ContinuousWithinAt (fun p : ℝ × ℝ ↦ Gamma (b + (p.2 : ℂ) * I))
        (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) z :=
      ((continuous_Gamma_add_mul_I hb').comp continuous_snd).continuousWithinAt
    have hGd : ContinuousWithinAt (fun p : ℝ × ℝ ↦ Gamma (d - (p.2 : ℂ) * I))
        (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) z := by
      have hcont_d : Continuous fun y : ℝ ↦ Gamma (d - y * I) := by
        simpa [comp_def, sub_eq_add_neg] using (continuous_Gamma_add_mul_I hd').comp continuous_neg
      exact (hcont_d.comp continuous_snd).continuousWithinAt
    exact (hpow1.mul hpow2).mul (hGb.mul hGd)
  · rw [Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with z hz
    have hz1 : 0 < z.1 := hz.1
    have hnorm_u : ‖(z.1 : ℂ) ^ (c - (z.2 : ℂ) * I - 1)‖ = ‖(z.1 : ℂ) ^ (c - 1)‖ := by
      rw [norm_cpow_eq_rpow_re_of_pos hz1, norm_cpow_eq_rpow_re_of_pos hz1]
      congr 1
      simp
    simp only [uncurry, barnesKernel, norm_mul, hnorm_u, le_refl]

/-- Integrating `barnesKernel a b c d` first over `u ∈ (0, ∞)` and then over `y ∈ ℝ` yields
`Γ(a + c)⁻¹` times the four-Gamma Barnes integral. -/
private theorem integral_integral_barnesKernel_fst {a c : ℂ} (b d : ℂ) (ha : 0 < a.re)
    (hc : 0 < c.re) :
    (∫ y : ℝ, ∫ u in Ioi (0 : ℝ), barnesKernel a b c d u y) =
      (Gamma (a + c))⁻¹ * ∫ y : ℝ, Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) *
        Gamma (d - y * I) := by
  have hinner (y : ℝ) : (∫ u in Ioi (0 : ℝ), barnesKernel a b c d u y) =
      (Gamma (a + c))⁻¹ * (Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) *
        Gamma (d - y * I)) := by
    simp only [barnesKernel, integral_mul_const]
    have hm := (hasMellin_one_add_cpow_neg (s := c - y * I) (a := a + c)
      (by simpa using hc) (by simp [ha])).2
    have hsub : a + c - (c - (y : ℂ) * I) = a + y * I := by ring
    simp only [mellin, smul_eq_mul, hsub] at hm
    rw [hm]
    ring
  simp_rw [hinner, integral_const_mul]

/-- Integrating `barnesKernel a b c d` first over `y ∈ ℝ` and then over `u ∈ (0, ∞)` yields
`2π Γ(b + d) Γ(b + c) Γ(a + d) / Γ(a + b + c + d)`. -/
private theorem integral_integral_barnesKernel_snd {a b c d : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) (hd : 0 < d.re) :
    (∫ u in Ioi (0 : ℝ), ∫ y : ℝ, barnesKernel a b c d u y) =
      2 * π * Gamma (b + d) * (Gamma (b + c) * Gamma (a + d) / Gamma (a + b + c + d)) := by
  have hinner : EqOn (fun u : ℝ ↦ ∫ y : ℝ, barnesKernel a b c d u y)
      (fun u : ℝ ↦ (2 * π * Gamma (b + d)) *
        ((u : ℂ) ^ ((b + c) - 1) * (1 + (u : ℂ)) ^ (-(a + b + c + d)))) (Ioi 0) := by
    intro u (hu : 0 < u)
    have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
    have h1u0 : 1 + (u : ℂ) ≠ 0 := by
      rw [← ofReal_one, ← ofReal_add]
      exact ofReal_ne_zero.mpr (by linarith)
    have hrew (y : ℝ) : barnesKernel a b c d u y =
        ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
          ((u : ℂ) ^ (-(b + y * I)) * (Gamma (b + y * I) * Gamma (d - y * I))) := by
      have hexp : c - (y : ℂ) * I - 1 = (b + c - 1) + (-(b + y * I)) := by ring
      simp only [barnesKernel]
      rw [hexp, cpow_add _ _ hu0]
      ring
    simp_rw [hrew, integral_const_mul]
    rw [integral_cpow_neg_mul_Gamma_add_mul_Gamma_sub hb hd hu]
    calc ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
          (2 * π * (Gamma (b + d) * (1 + (u : ℂ)) ^ (-(b + d))))
        = (2 * π * Gamma (b + d)) * ((u : ℂ) ^ ((b + c) - 1) *
            ((1 + (u : ℂ)) ^ (-(a + c)) * (1 + (u : ℂ)) ^ (-(b + d)))) := by ring
      _ = (2 * π * Gamma (b + d)) *
            ((u : ℂ) ^ ((b + c) - 1) * (1 + (u : ℂ)) ^ (-(a + b + c + d))) := by
          rw [← cpow_add _ _ h1u0]
          congr 3
          ring
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, integral_const_mul]
  have hm := (hasMellin_one_add_cpow_neg (s := b + c) (a := a + b + c + d)
    (by simp; linarith) (by simp; linarith)).2
  have hsub : a + b + c + d - (b + c) = a + d := by ring
  simp only [mellin, smul_eq_mul, hsub] at hm
  rw [hm]

/-- **Barnes's first lemma** (DLMF 5.13.3). For complex parameters `a, b, c, d` with positive real
parts,
`(2π)⁻¹ ∫_{-∞}^∞ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy =`
`  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) *
        Gamma (d - y * I) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  have hswap := (integral_integral_swap (integrable_barnesKernel ha hb hc hd)).symm
  rw [integral_integral_barnesKernel_fst b d ha hc,
    integral_integral_barnesKernel_snd ha hb hc hd] at hswap
  have hΓac : Gamma (a + c) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have h2pi : (2 * π : ℂ) ≠ 0 := by
    rw [ne_eq, mul_eq_zero, not_or]
    exact ⟨two_ne_zero, ofReal_ne_zero.mpr pi_ne_zero⟩
  calc (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) *
          Gamma (d - y * I)
      = (2 * π : ℂ)⁻¹ * (Gamma (a + c) * ((Gamma (a + c))⁻¹ *
          ∫ y : ℝ, Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) *
            Gamma (d - y * I))) := by
        rw [← mul_assoc (Gamma (a + c)), mul_inv_cancel₀ hΓac, one_mul]
    _ = (2 * π : ℂ)⁻¹ * (Gamma (a + c) *
          (2 * π * Gamma (b + d) * (Gamma (b + c) * Gamma (a + d) / Gamma (a + b + c + d)))) := by
        rw [hswap]
    _ = Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
        field_simp [h2pi]

/-- **Barnes's first lemma on a separating vertical line** (DLMF 5.13.3). If the vertical line
`Re s = σ` separates the poles of `Γ(a + s) Γ(b + s)` from those of `Γ(c - s) Γ(d - s)`, meaning
`-Re a < σ`, `-Re b < σ`, `σ < Re c`, and `σ < Re d`, then
`(2π)⁻¹ ∫_{-∞}^∞ Γ(a + σ + i y) Γ(b + σ + i y) Γ(c - σ - i y) Γ(d - σ - i y) dy =`
`  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_vertical {a b c d : ℂ} {σ : ℝ}
    (haσ : -a.re < σ) (hbσ : -b.re < σ) (hσc : σ < c.re) (hσd : σ < d.re) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - (σ + y * I)) * Gamma (d - (σ + y * I)) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  have hsum : a + (σ : ℂ) + (b + σ) + (c - σ) + (d - σ) = a + b + c + d := by ring
  calc (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - (σ + y * I)) * Gamma (d - (σ + y * I))
      = (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + σ + y * I) * Gamma (b + σ + y * I) *
          Gamma (c - σ - y * I) * Gamma (d - σ - y * I) := by
        simp only [add_assoc, sub_add_eq_sub_sub]
    _ = Gamma (a + σ + (c - σ)) * Gamma (a + σ + (d - σ)) * Gamma (b + σ + (c - σ)) *
          Gamma (b + σ + (d - σ)) / Gamma (a + σ + (b + σ) + (c - σ) + (d - σ)) :=
        integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma (by simp; linarith) (by simp; linarith)
          (by simp; linarith) (by simp; linarith)
    _ = Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) /
          Gamma (a + b + c + d) := by
        rw [add_add_sub_cancel, add_add_sub_cancel, add_add_sub_cancel, add_add_sub_cancel, hsum]

-- Asymmetric integer parameters `(1, 1, 2, 2)` check the `(2π)⁻¹` factor and `Γ(a + b + c + d)`.
example :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (1 + y * I) * Gamma (1 + y * I) * Gamma (2 - y * I) *
        Gamma (2 - y * I) = 2 / 15 := by
  rw [integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)]
  norm_num [Gamma_nat_eq_factorial]

-- Separating line `Re s = -1/2` at `(a, b, c, d) = (1, 1, 1, 0)`, where `Re d = 0` is not positive.
example :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (1 + ((-1 / 2 : ℝ) + y * I)) *
        Gamma (1 + ((-1 / 2 : ℝ) + y * I)) * Gamma (1 - ((-1 / 2 : ℝ) + y * I)) *
        Gamma (0 - ((-1 / 2 : ℝ) + y * I)) = 1 / 2 := by
  rw [integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_vertical (σ := -1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num [Gamma_nat_eq_factorial]

end Complex
