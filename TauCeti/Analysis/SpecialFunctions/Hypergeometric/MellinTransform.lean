/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes

/-!
# The Mellin transform of Euler's integral at negative argument

For `0 < Re s < min (Re a) (Re b)` and `Re b < Re c`, the Mellin transform of
`x ↦ E(a, b, c, -x)`, Euler's normalized integral (DLMF 15.6.1) at negative argument, is

`∫₀^∞ x^{s - 1} E(a, b, c, -x) dx = Γ(s) Γ(a - s) Γ(b - s) / (Γ(a) Γ(b) Γ(c - s))`.

This is DLMF 15.14.1 in the region `0 < Re b < Re c` where Euler's integral represents the
regularized Gauss function `𝐅(a, b; c; -x)`. The proof inserts Euler's integral, exchanges the
two integrals by Fubini, evaluates the inner `x`-integral as a scaled Beta integral of the second
kind (`Complex.hasMellin_one_add_cpow_neg`),

`∫₀^∞ x^{s - 1} (1 + x t)^{-a} dx = t^{-s} Γ(s) Γ(a - s) / Γ(a)`,

and evaluates the remaining `t`-integral `∫₀¹ t^{b - s - 1} (1 - t)^{c - b - 1} dt` as the Beta
integral `B(b - s, c - b)`. The same computation with the real parts of the parameters bounds the
norm of the integrand, which gives the integrability on `(0, ∞) × (0, 1]` that Fubini needs.

## Main results

* `Complex.hasMellin_eulerIntegral_neg`: for `0 < Re s < Re a`, `Re s < Re b` and `Re b < Re c`,
  the Mellin transform of `x ↦ eulerIntegral a b c (-x)` converges at `s` and equals
  `Γ(s) Γ(a - s) Γ(b - s) / (Γ(a) Γ(b) Γ(c - s))`.

## References

* NIST Digital Library of Mathematical Functions, equations 15.6.1 and 15.14.1,
  <https://dlmf.nist.gov/15.14>.
-/

public section

open Real Set MeasureTheory
open Complex hiding exp continuous_exp log

namespace Complex

/-- The scaled Beta integral of the second kind: for `t > 0` and `0 < Re s < Re a`, the Mellin
transform of `x ↦ (1 + x t)^{-a}` at `s` is `t^{-s} Γ(s) Γ(a - s) / Γ(a)`. -/
private lemma hasMellin_one_add_mul_cpow_neg {s a : ℂ} (hs : 0 < s.re) (hsa : s.re < a.re)
    {t : ℝ} (ht : 0 < t) :
    HasMellin (fun x : ℝ ↦ (1 + (x : ℂ) * t) ^ (-a)) s
      ((t : ℂ) ^ (-s) * (Gamma s * Gamma (a - s) / Gamma a)) := by
  simpa only [ofReal_mul, smul_eq_mul] using (hasMellin_one_add_cpow_neg hs hsa).comp_mul_right ht

/-- The norm of the scaled Mellin integrand of `(1 + x t)^{-a}` integrates to
`t^{-Re s} ‖Γ(Re s) Γ(Re a - Re s) / Γ(Re a)‖`, by the same Beta integral at the real parts. -/
private lemma integral_norm_cpow_mul_one_add_mul_cpow_neg {s a : ℂ} (hs : 0 < s.re)
    (hsa : s.re < a.re) {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ in Ioi 0, ‖(x : ℂ) ^ (s - 1) * (1 + (x : ℂ) * t) ^ (-a)‖ =
      t ^ (-s.re) * ‖Gamma s.re * Gamma (a.re - s.re) / Gamma a.re‖ := by
  -- the real integrand `x^{Re s - 1} (1 + x t)^{-Re a}`
  set r : ℝ → ℝ := fun x ↦ x ^ (s.re - 1) * (1 + x * t) ^ (-a.re)
  have hnorm : ∀ x ∈ Ioi (0 : ℝ),
      ‖(x : ℂ) ^ (s - 1) * (1 + (x : ℂ) * t) ^ (-a)‖ = r x := fun x hx ↦ by
    have hbase : (1 + (x : ℂ) * t) = ((1 + x * t : ℝ) : ℂ) := by push_cast; ring
    rw [norm_mul, hbase, norm_cpow_eq_rpow_re_of_pos hx,
      norm_cpow_eq_rpow_re_of_pos (by have := mul_pos (show (0 : ℝ) < x from hx) ht; linarith)]
    simp [r]
  have hreal : ∀ x ∈ Ioi (0 : ℝ),
      (x : ℂ) ^ ((s.re : ℂ) - 1) • (1 + (x : ℂ) * t) ^ (-(a.re : ℂ)) = ((r x : ℝ) : ℂ) :=
    fun x hx ↦ by
      have hx0 : (0 : ℝ) ≤ x := le_of_lt hx
      have h1 : (0 : ℝ) ≤ 1 + x * t := by positivity
      simp only [r, smul_eq_mul, ofReal_mul, ofReal_cpow hx0, ofReal_cpow h1]
      push_cast
      ring_nf
  obtain ⟨-, hval⟩ := hasMellin_one_add_mul_cpow_neg (s := s.re) (a := a.re) (by simpa)
    (by simpa) ht
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi hreal, integral_complex_ofReal] at hval
  have hr0 : 0 ≤ ∫ x : ℝ in Ioi 0, r x :=
    setIntegral_nonneg measurableSet_Ioi fun x hx ↦ by
      have := mul_pos (show (0 : ℝ) < x from hx) ht
      exact mul_nonneg (rpow_nonneg (le_of_lt hx) _) (rpow_nonneg (by linarith) _)
  rw [setIntegral_congr_fun measurableSet_Ioi hnorm, ← abs_of_nonneg hr0, ← Real.norm_eq_abs,
    ← norm_real, hval, norm_mul, norm_cpow_eq_rpow_re_of_pos ht]
  simp

/-- Lowering the exponent of `t` in the Beta weight of Euler's integral by `s`. -/
private lemma cpow_mul_one_sub_cpow_mul_cpow_neg (b c s : ℂ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (t : ℂ) ^ (-s) =
      (t : ℂ) ^ (b - s - 1) * (1 - (t : ℂ)) ^ (c - b - 1) := by
  rw [show b - s - 1 = b - 1 + -s by ring, cpow_add _ _ (ofReal_ne_zero.mpr ht.ne')]
  ring

/-- The integrand of the Mellin transform of Euler's integral at negative argument is integrable
on `(0, ∞) × (0, 1]`: its norm integrates in `x` to a constant multiple of the Beta weight
`‖t^{b - s - 1} (1 - t)^{c - b - 1}‖`. -/
private lemma integrable_cpow_mul_eulerIntegrand {a b c s : ℂ} (hs : 0 < s.re) (hsa : s.re < a.re)
    (hsb : s.re < b.re) (hbc : b.re < c.re) :
    Integrable (Function.uncurry fun x t : ℝ ↦ (x : ℂ) ^ (s - 1) *
        ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 + (x : ℂ) * t) ^ (-a)))
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 1))) := by
  have hbs : 0 < (b - s).re := by simpa using sub_pos.mpr hsb
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  rw [integrable_prod_iff' (Measurable.aestronglyMeasurable (by fun_prop))]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    refine ((hasMellin_one_add_mul_cpow_neg hs hsa ht.1).1.const_mul
      ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1))).congr (ae_of_all _ fun x ↦ ?_)
    simp only [Function.uncurry_apply_pair, smul_eq_mul]
    ring
  · have hbeta := ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (betaIntegral_convergent hbs hcb)).norm
    refine (hbeta.mul_const ‖Gamma s.re * Gamma (a.re - s.re) / Gamma a.re‖).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hnorm (x : ℝ) : ‖(x : ℂ) ^ (s - 1) *
        ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 + (x : ℂ) * t) ^ (-a))‖ =
        ‖(t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)‖ *
          ‖(x : ℂ) ^ (s - 1) * (1 + (x : ℂ) * t) ^ (-a)‖ := by
      simp only [norm_mul]
      ring
    simp_rw [Function.uncurry_apply_pair, hnorm]
    rw [integral_const_mul, integral_norm_cpow_mul_one_add_mul_cpow_neg hs hsa ht.1,
      ← mul_assoc, ← cpow_mul_one_sub_cpow_mul_cpow_neg b c s ht.1, norm_mul, norm_mul,
      norm_cpow_eq_rpow_re_of_pos ht.1 (-s), neg_re]

/-- **The Mellin transform of Euler's integral at negative argument** (DLMF 15.14.1 in the region
of DLMF 15.6.1). For `0 < Re s < Re a`, `Re s < Re b` and `Re b < Re c`, the Mellin transform of
`x ↦ eulerIntegral a b c (-x)` converges at `s` and equals
`Γ(s) Γ(a - s) Γ(b - s) / (Γ(a) Γ(b) Γ(c - s))`. -/
theorem hasMellin_eulerIntegral_neg {a b c s : ℂ} (hs : 0 < s.re) (hsa : s.re < a.re)
    (hsb : s.re < b.re) (hbc : b.re < c.re) :
    HasMellin (fun x : ℝ ↦ eulerIntegral a b c (-x)) s
      (Gamma s * Gamma (a - s) * Gamma (b - s) / (Gamma a * Gamma b * Gamma (c - s))) := by
  have hbs : 0 < (b - s).re := by simpa using sub_pos.mpr hsb
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  -- the Beta weight of Euler's integral, and the integrand on `(0, ∞) × (0, 1]`
  set w : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)
  set F : ℝ → ℝ → ℂ := fun x t ↦ (x : ℂ) ^ (s - 1) * (w t * (1 + (x : ℂ) * t) ^ (-a))
  set N := (Gamma b * Gamma (c - b))⁻¹ with hN
  set μ : Measure ℝ := volume.restrict (Ioi 0)
  set ν : Measure ℝ := volume.restrict (Ioc 0 1)
  have hF : Integrable (Function.uncurry F) (μ.prod ν) :=
    integrable_cpow_mul_eulerIntegrand hs hsa hsb hbc
  have heuler (x : ℝ) :
      (x : ℂ) ^ (s - 1) • eulerIntegral a b c (-x) = N * ∫ t, F x t ∂ν := by
    rw [eulerIntegral_def, intervalIntegral.integral_of_le zero_le_one, smul_eq_mul,
      mul_left_comm, ← integral_const_mul]
    congr 2
    ext t
    simp only [F, w, neg_mul, sub_neg_eq_add]
  -- the inner integral in `x` is a scaled Beta integral of the second kind
  have hinner : ∀ᵐ t ∂ν, ∫ x, F x t ∂μ =
      (t : ℂ) ^ (b - s - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (Gamma s * Gamma (a - s) / Gamma a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have h := (hasMellin_one_add_mul_cpow_neg hs hsa ht.1).2
    rw [mellin] at h
    have hF' : ∀ x, F x t = w t * ((x : ℂ) ^ (s - 1) • (1 + (x : ℂ) * t) ^ (-a)) := fun x ↦ by
      simp only [F, smul_eq_mul]
      ring
    simp_rw [hF']
    rw [integral_const_mul, h, ← mul_assoc, cpow_mul_one_sub_cpow_mul_cpow_neg b c s ht.1]
  refine ⟨(hF.integral_prod_left.const_mul N).congr (ae_of_all _ fun x ↦ (heuler x).symm), ?_⟩
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ heuler x, integral_const_mul,
    integral_integral_swap hF, integral_congr_ae hinner, integral_mul_const,
    ← intervalIntegral.integral_of_le zero_le_one, ← betaIntegral,
    betaIntegral_eq_Gamma_mul_div _ _ hbs hcb, show b - s + (c - b) = c - s by ring]
  have hGb := Gamma_ne_zero_of_re_pos (hs.trans hsb)
  have hGcb := Gamma_ne_zero_of_re_pos hcb
  have hGa := Gamma_ne_zero_of_re_pos (hs.trans hsa)
  have hGcs := Gamma_ne_zero_of_re_pos (show 0 < (c - s).re by
    simpa using sub_pos.mpr (hsb.trans hbc))
  simp only [hN]
  field_simp

end Complex
