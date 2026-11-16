/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical

/-!
# Barnes's first lemma

For complex parameters `a`, `b`, `c`, `d` with positive real parts, Barnes's first lemma
([DLMF 5.13.3](https://dlmf.nist.gov/5.13.E3)) evaluates the vertical line integral of a product
of four Gamma functions:

`(1 / 2π) ∫ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy`
`  = Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`.

The proof avoids contour shifting by applying Fubini's theorem to the double integral of
`u^{c - i y - 1} (1 + u)^{-(a + c)} Γ(b + i y) Γ(d - i y)` over `(0, ∞) × ℝ`:

* Integrating in `y` first via the Mellin–Barnes integral of `(1 + u)^{-(b + d)}`
  (`Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_sub`) reduces the `u`-integral to Euler's Beta
  integral of the second kind (`Complex.hasMellin_one_add_cpow_neg`), yielding
  `2π Γ(b + d) Γ(b + c) Γ(a + d) / Γ(a + b + c + d)`.
* Integrating in `u` first via `Complex.hasMellin_one_add_cpow_neg` produces
  `(Γ(a + c))⁻¹ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y)`.

Replacing `(a, b, c, d)` by `(a + σ, b + σ, c - σ, d - σ)` immediately yields the shifted-line
version on any vertical line `Re s = σ` with `-min(Re a, Re b) < σ < min(Re c, Re d)`.

## Main results

* `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`: integrability of the four-Gamma
  integrand on every line where none of `Re a`, `Re b`, `Re c`, `Re d` is a nonpositive integer.
* `Complex.integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`: Barnes's first lemma on the imaginary
  axis for `Re a, Re b, Re c, Re d > 0`.
* `Complex.integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub`: Barnes's first lemma on
  a shifted vertical line `Re s = σ` separating the poles of `Γ(a + s) Γ(b + s)` from those of
  `Γ(c - s) Γ(d - s)`.

## References

* NIST Digital Library of Mathematical Functions, equation 5.13.3.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §14.52.
-/

public section

open Real Set MeasureTheory Filter
open Complex hiding exp continuous_exp log

namespace Complex

/-- The product `Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y)` is integrable on `ℝ` whenever none
of `Re a`, `Re b`, `Re c`, `Re d` is a nonpositive integer. -/
theorem integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ}
    (ha : ∀ n : ℕ, a.re ≠ -n) (hb : ∀ n : ℕ, b.re ≠ -n)
    (hc : ∀ n : ℕ, c.re ≠ -n) (hd : ∀ n : ℕ, d.re ≠ -n) :
    Integrable fun y : ℝ ↦
      Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
  obtain ⟨Cb, hCb⟩ := exists_norm_Gamma_add_mul_I_le hb
  obtain ⟨Cc, hCc⟩ := exists_norm_Gamma_sub_mul_I_le hc
  obtain ⟨Cd, hCd⟩ := exists_norm_Gamma_sub_mul_I_le hd
  exact (((integrable_Gamma_add_mul_I ha).mul_bdd
    (continuous_Gamma_add_mul_I hb).aestronglyMeasurable (.of_forall hCb)).mul_bdd
    (continuous_Gamma_sub_mul_I hc).aestronglyMeasurable (.of_forall hCc)).mul_bdd
    (continuous_Gamma_sub_mul_I hd).aestronglyMeasurable (.of_forall hCd)

/-- Shifted-imaginary-part form of the Mellin–Barnes integral of `(1 + u)^{-(b + d)}`:
`∫ u^{-(b + i y)} Γ(b + i y) Γ(d - i y) dy = 2π Γ(b + d) (1 + u)^{-(b + d)}` for `u > 0`
and `Re b, Re d > 0`. -/
private lemma integral_cpow_neg_add_mul_Gamma_mul_Gamma {b d : ℂ} (hb : 0 < b.re) (hd : 0 < d.re)
    {u : ℝ} (hu : 0 < u) :
    ∫ y : ℝ, (u : ℂ) ^ (-(b + y * I)) * (Gamma (b + y * I) * Gamma (d - y * I)) =
      2 * π * (Gamma (b + d) * (1 + (u : ℂ)) ^ (-(b + d))) := by
  have h := integral_cpow_neg_mul_Gamma_mul_Gamma_sub (a := b + d) (σ := b.re)
    hb (by simpa using hd) hu
  rw [← MeasureTheory.integral_add_right_eq_self _ b.im] at h
  refine (integral_congr_ae (.of_forall fun y ↦ ?_)).trans h
  have h1 : b + (y : ℂ) * I = (b.re : ℂ) + ((y + b.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [add_comm]
  have h2 : d - (y : ℂ) * I = b + d - ((b.re : ℂ) + ((y + b.im : ℝ) : ℂ) * I) := by
    apply Complex.ext <;> simp; ring
  rw [h1, h2]

/-- Joint integrability on `(0, ∞) × ℝ` of the Fubini kernel used to prove Barnes's first lemma. -/
private lemma integrable_barnesKernel {a b c d : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hc : 0 < c.re) (hd : 0 < d.re) :
    Integrable
      (Function.uncurry fun (u y : ℝ) ↦
        (u : ℂ) ^ (c - y * I - 1) * (1 + (u : ℂ)) ^ (-(a + c)) *
          (Gamma (b + y * I) * Gamma (d - y * I)))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hb_ne : ∀ n : ℕ, b.re ≠ -n := fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  have hd_ne : ∀ n : ℕ, d.re ≠ -n := fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  have hprod_eq : (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ) =
      ((volume : Measure ℝ).prod volume).restrict (Ioi (0 : ℝ) ×ˢ Set.univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hcont : ContinuousOn
      (Function.uncurry fun (u y : ℝ) ↦
        (u : ℂ) ^ (c - y * I - 1) * (1 + (u : ℂ)) ^ (-(a + c)) *
          (Gamma (b + y * I) * Gamma (d - y * I)))
      (Ioi (0 : ℝ) ×ˢ Set.univ) := by
    refine continuousOn_of_forall_continuousAt fun p hp ↦ ?_
    have hu : 0 < p.1 := hp.1
    have h1 : ContinuousAt (fun q : ℝ × ℝ ↦ (q.1 : ℂ) ^ (c - (q.2 : ℂ) * I - 1)) p :=
      ContinuousAt.cpow (by fun_prop) (by fun_prop) (ofReal_mem_slitPlane.mpr hu)
    have h2 : ContinuousAt (fun q : ℝ × ℝ ↦ (1 + (q.1 : ℂ)) ^ (-(a + c))) p :=
      ContinuousAt.cpow (by fun_prop) (by fun_prop) <| by
        rw [← ofReal_one, ← ofReal_add]
        exact ofReal_mem_slitPlane.mpr (by linarith)
    have h3 : ContinuousAt
        (fun q : ℝ × ℝ ↦ Gamma (b + (q.2 : ℂ) * I) * Gamma (d - (q.2 : ℂ) * I)) p :=
      (((continuous_Gamma_add_mul_I hb_ne).comp continuous_snd).mul
        ((continuous_Gamma_sub_mul_I hd_ne).comp continuous_snd)).continuousAt
    exact (h1.mul h2).mul h3
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun (u y : ℝ) ↦
        (u : ℂ) ^ (c - y * I - 1) * (1 + (u : ℂ)) ^ (-(a + c)) *
          (Gamma (b + y * I) * Gamma (d - y * I)))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    rw [hprod_eq]
    exact hcont.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ)
  have hu_int : Integrable (fun u : ℝ ↦ ‖(u : ℂ) ^ (c - 1) * (1 + (u : ℂ)) ^ (-(a + c))‖)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have h := (hasMellin_one_add_cpow_neg (s := c) (a := a + c) hc (by simpa using ha)).1
    simpa [MellinConvergent, smul_eq_mul] using h.norm
  have hy_int : Integrable fun y : ℝ ↦ ‖Gamma (b + y * I) * Gamma (d - y * I)‖ := by
    obtain ⟨Cd, hCd⟩ := exists_norm_Gamma_sub_mul_I_le hd_ne
    exact ((integrable_Gamma_add_mul_I hb_ne).mul_bdd
      (continuous_Gamma_sub_mul_I hd_ne).aestronglyMeasurable (.of_forall hCd)).norm
  refine (hu_int.mul_prod hy_int).mono' hmeas ?_
  rw [hprod_eq]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp
  have hu : 0 < p.1 := hp.1
  simp only [Function.uncurry, norm_mul]
  have hpow : ‖(p.1 : ℂ) ^ (c - (p.2 : ℂ) * I - 1)‖ = ‖(p.1 : ℂ) ^ (c - 1)‖ := by
    rw [norm_cpow_eq_rpow_re_of_pos hu, norm_cpow_eq_rpow_re_of_pos hu]
    simp
  rw [hpow, mul_assoc]

/-- **Barnes's first lemma** ([DLMF 5.13.3](https://dlmf.nist.gov/5.13.E3)): for `a, b, c, d ∈ ℂ`
with positive real parts,
`(1 / 2π) ∫ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy`
`= Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) *
        Gamma (d - y * I) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  let F : ℝ → ℝ → ℂ := fun u y ↦
    (u : ℂ) ^ (c - y * I - 1) * (1 + (u : ℂ)) ^ (-(a + c)) *
      (Gamma (b + y * I) * Gamma (d - y * I))
  have hF_int : Integrable (Function.uncurry F) ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
    integrable_barnesKernel ha hb hc hd
  -- Evaluate the iterated integral in `y` first, then `u`.
  have h_uy : ∫ u in Ioi (0 : ℝ), ∫ y : ℝ, F u y =
      2 * π * Gamma (b + d) * (Gamma (b + c) * Gamma (a + d) / Gamma (a + b + c + d)) := by
    have hinner : ∀ u ∈ Ioi (0 : ℝ), ∫ y : ℝ, F u y =
        2 * π * Gamma (b + d) * ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + b + c + d))) := by
      intro u (hu : 0 < u)
      have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
      have h1u0 : (1 + (u : ℂ)) ≠ 0 := by
        rw [← ofReal_one, ← ofReal_add]
        exact ofReal_ne_zero.mpr (by linarith)
      have hrew : ∀ y : ℝ, F u y =
          ((u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
            ((u : ℂ) ^ (-(b + y * I)) * (Gamma (b + y * I) * Gamma (d - y * I))) := by
        intro y
        simp only [F]
        have hcpow : (u : ℂ) ^ (b + c - 1) * (u : ℂ) ^ (-(b + y * I)) =
            (u : ℂ) ^ (c - y * I - 1) := by
          rw [← cpow_add _ _ hu0]
          congr 1
          ring
        calc (u : ℂ) ^ (c - y * I - 1) * (1 + (u : ℂ)) ^ (-(a + c)) *
              (Gamma (b + y * I) * Gamma (d - y * I))
            = (u : ℂ) ^ (b + c - 1) * (u : ℂ) ^ (-(b + y * I)) * (1 + (u : ℂ)) ^ (-(a + c)) *
                (Gamma (b + y * I) * Gamma (d - y * I)) := by rw [hcpow]
          _ = _ := by ring
      simp_rw [hrew, integral_const_mul, integral_cpow_neg_add_mul_Gamma_mul_Gamma hb hd hu]
      have hcpow1 : (1 + (u : ℂ)) ^ (-(a + c)) * (1 + (u : ℂ)) ^ (-(b + d)) =
          (1 + (u : ℂ)) ^ (-(a + b + c + d)) := by
        rw [← cpow_add _ _ h1u0]
        congr 1
        ring
      calc (u : ℂ) ^ (b + c - 1) * (1 + (u : ℂ)) ^ (-(a + c)) *
            (2 * π * (Gamma (b + d) * (1 + (u : ℂ)) ^ (-(b + d))))
          = 2 * π * Gamma (b + d) * ((u : ℂ) ^ (b + c - 1) *
              ((1 + (u : ℂ)) ^ (-(a + c)) * (1 + (u : ℂ)) ^ (-(b + d)))) := by ring
        _ = _ := by rw [hcpow1]
    rw [setIntegral_congr_fun measurableSet_Ioi hinner, integral_const_mul]
    have hm := (hasMellin_one_add_cpow_neg (s := b + c) (a := a + b + c + d)
      (by simp; linarith) (by simp; linarith)).2
    have had : a + b + c + d - (b + c) = a + d := by ring
    rw [mellin] at hm
    simp only [smul_eq_mul] at hm
    rw [hm, had]
  -- Evaluate the iterated integral in `u` first, then `y`.
  have h_yu : ∫ y : ℝ, ∫ u in Ioi (0 : ℝ), F u y =
      (Gamma (a + c))⁻¹ * ∫ y : ℝ,
        Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
    have hinner (y : ℝ) : ∫ u in Ioi (0 : ℝ), F u y =
        (Gamma (a + c))⁻¹ *
          (Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I)) := by
      simp only [F, integral_mul_const]
      have hm := (hasMellin_one_add_cpow_neg (s := c - y * I) (a := a + c)
        (by simpa using hc) (by simp; linarith)).2
      have hay : a + c - (c - y * I) = a + y * I := by ring
      rw [mellin] at hm
      simp only [smul_eq_mul] at hm
      rw [hm, hay]
      ring
    simp_rw [hinner, integral_const_mul]
  -- Equate the two iterated integrals by Fubini's theorem.
  have heq : (Gamma (a + c))⁻¹ * ∫ y : ℝ,
        Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) =
      2 * π * Gamma (b + d) * (Gamma (b + c) * Gamma (a + d) / Gamma (a + b + c + d)) := by
    rw [← h_yu, ← h_uy]
    exact (integral_integral_swap hF_int).symm
  have hΓac : Gamma (a + c) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have h2π : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hmul := congrArg (fun w : ℂ ↦ (2 * π : ℂ)⁻¹ * Gamma (a + c) * w) heq
  calc (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) *
          Gamma (d - y * I)
      = (2 * π : ℂ)⁻¹ * Gamma (a + c) * ((Gamma (a + c))⁻¹ * ∫ y : ℝ,
          Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I)) := by
        rw [mul_assoc, ← mul_assoc (Gamma (a + c)), mul_inv_cancel₀ hΓac, one_mul]
    _ = (2 * π : ℂ)⁻¹ * Gamma (a + c) *
          (2 * π * Gamma (b + d) * (Gamma (b + c) * Gamma (a + d) / Gamma (a + b + c + d))) := hmul
    _ = Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
        field_simp [h2π]

/-- **Barnes's first lemma** on a shifted vertical line `Re s = σ`: whenever
`-min(Re a, Re b) < σ < min(Re c, Re d)`,
`(1 / 2π) ∫ Γ(a + σ + i y) Γ(b + σ + i y) Γ(c - σ - i y) Γ(d - σ - i y) dy`
`= Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub {a b c d : ℂ} {σ : ℝ}
    (haσ : -a.re < σ) (hbσ : -b.re < σ) (hσc : σ < c.re) (hσd : σ < d.re) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - (σ + y * I)) * Gamma (d - (σ + y * I)) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  have h := integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma
    (a := a + σ) (b := b + σ) (c := c - σ) (d := d - σ)
    (by simp; linarith) (by simp; linarith) (by simp; linarith) (by simp; linarith)
  have hcongr : ∀ y : ℝ,
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - (σ + y * I)) * Gamma (d - (σ + y * I)) =
        Gamma ((a + σ) + y * I) * Gamma ((b + σ) + y * I) *
          Gamma ((c - σ) - y * I) * Gamma ((d - σ) - y * I) := fun y ↦ by
    rw [add_assoc a, add_assoc b, sub_add_eq_sub_sub c, sub_add_eq_sub_sub d]
  have hac : a + σ + (c - σ) = a + c := by ring
  have had : a + σ + (d - σ) = a + d := by ring
  have hbc : b + σ + (c - σ) = b + c := by ring
  have hbd : b + σ + (d - σ) = b + d := by ring
  have habcd : a + σ + (b + σ) + (c - σ) + (d - σ) = a + b + c + d := by ring
  simp_rw [hcongr]
  rw [h, hac, had, hbc, hbd, habcd]

end Complex
