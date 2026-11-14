/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Euler's second beta integral with complex parameters

For parameters `a`, `b` with positive real parts and a positive real shift `x`, the
kernel `t ^ (a - 1) * (x + t) ^ (-(a + b))` is absolutely integrable on the positive
half-line. Its integral is `Gamma a * Gamma b / Gamma (a + b) * x ^ (-b)`.
All complex powers use the principal branch; their bases here are positive real numbers.

The unit-shift case is already supplied by `Complex.hasMellin_one_add_cpow_neg`.
Scaling gives the arbitrary positive shift. These formulas supply the model integrals
for expansions of Stieltjes transforms.

## References

* NIST Digital Library of Mathematical Functions, §2.6(i), equation (2.6.4),
  <https://dlmf.nist.gov/2.6.E4>.
-/

public section

open Complex MeasureTheory Set

namespace Complex

private lemma betaKernel_scale (a b : ℂ) {x t : ℝ} (hx : 0 < x) :
    ((x * t : ℝ) : ℂ) ^ (a - 1) * ((x + x * t : ℝ) : ℂ) ^ (-(a + b)) =
      (x : ℂ) ^ (-b - 1) * ((t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (-(a + b))) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hfactor : x + x * t = x * (1 + t) := by ring
  rw [hfactor, ofReal_mul, ofReal_mul, TauCeti.ofReal_mul_cpow hx.le,
    TauCeti.ofReal_mul_cpow hx.le, ofReal_add, ofReal_one]
  calc
    _ = ((x : ℂ) ^ (a - 1) * (x : ℂ) ^ (-(a + b))) *
        ((t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (-(a + b))) := by ring
    _ = _ := by
      rw [← cpow_add _ _ hx0]
      congr 2
      ring

/-- The shifted complex beta kernel is absolutely integrable on the positive half-line.
Both endpoint conditions are encoded by the positive real parts of the parameters. -/
theorem integrableOn_cpow_mul_add_cpow {a b : ℂ} {x : ℝ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * ((x + t : ℝ) : ℂ) ^ (-(a + b)))
      (Ioi 0) := by
  have hm := hasMellin_one_add_cpow_neg (s := a) (a := a + b) ha (by simp; linarith)
  have hi : IntegrableOn (fun t : ℝ =>
      (x : ℂ) ^ (-b - 1) * ((t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (-(a + b))))
      (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul, mul_left_comm] using
      hm.1.const_smul ((x : ℂ) ^ (-b - 1))
  have hs := IntegrableOn.congr_fun hi
    (fun t _ => (betaKernel_scale a b hx).symm) measurableSet_Ioi
  simpa only [mul_zero] using
    (integrableOn_Ioi_comp_mul_left_iff _ 0 hx).mp hs

/-- The Beta-type model integral with positive real shift and complex exponents
(DLMF 2.6.4), using principal complex powers. -/
theorem integral_cpow_mul_add_cpow {a b : ℂ} {x : ℝ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) * ((x + t : ℝ) : ℂ) ^ (-(a + b))) =
      Gamma a * Gamma b / Gamma (a + b) * (x : ℂ) ^ (-b) := by
  have hscale := integral_comp_mul_left_Ioi'
    (fun t : ℝ => (t : ℂ) ^ (a - 1) * ((x + t : ℝ) : ℂ) ^ (-(a + b))) 0 hx
  rw [mul_zero] at hscale
  rw [← hscale, setIntegral_congr_fun measurableSet_Ioi
    (fun (t : ℝ) _ => betaKernel_scale a b hx (t := t)),
    integral_const_mul, real_smul]
  have hm := (hasMellin_one_add_cpow_neg (s := a) (a := a + b) ha (by simp; linarith)).2
  simp only [mellin, smul_eq_mul, add_sub_cancel_left] at hm
  rw [hm]
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  calc
    _ = (Gamma a * Gamma b / Gamma (a + b)) *
        ((x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (-b - 1)) := by rw [cpow_one]; ring
    _ = _ := by rw [← cpow_add _ _ hx0]; congr 2; ring

-- The elementary and half-integer cases check the normalization and the shift factor.
example {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), ((x + t : ℝ) : ℂ) ^ (-2 : ℂ)) = (x : ℂ)⁻¹ := by
  convert integral_cpow_mul_add_cpow (a := 1) (b := 1) (by norm_num) (by norm_num) hx using 1 <;>
    norm_num [cpow_neg_one, Gamma_nat_eq_factorial]

example :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (-(1 / 2) : ℂ) * (1 + (t : ℂ))⁻¹) = (Real.pi : ℂ) := by
  have h := integral_cpow_mul_add_cpow (a := 1 / 2) (b := 1 / 2) (x := 1)
    (by norm_num) (by norm_num) zero_lt_one
  norm_num [cpow_neg_one, Gamma_one_half_eq, ← sq] at h
  convert h using 1
  rw [← cpow_nat_mul]
  norm_num

end Complex
