/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Elementary one-sided Laplace transforms

This file evaluates the one-sided Laplace transform `TauCeti.HasLaplace` on elementary functions
(constants, step functions, exponentials, monomials, and exponentially damped monomials) and
records non-convergence of constant functions on the closed left half-plane `Re s ≤ 0`.

## Main results

* `TauCeti.hasLaplace_const` and `TauCeti.hasLaplace_one`: constants have Laplace transform
  `s⁻¹ • v` (resp. `s⁻¹`) for `0 < s.re`.
* `TauCeti.not_hasLaplace_const_of_re_nonpos` and `TauCeti.not_hasLaplace_one_of_re_nonpos`:
  nonzero constants have no convergent one-sided Laplace transform for `s.re ≤ 0`.
* `TauCeti.hasLaplace_indicator_Ici_one`: the Heaviside step function on `[a, ∞)` (`0 ≤ a`) has
  Laplace transform `exp (-s * a) / s` for `0 < s.re`.
* `TauCeti.hasLaplace_cexp_mul`: `t ↦ exp (w * t)` has Laplace transform `(s - w)⁻¹` for
  `w.re < s.re`.
* `TauCeti.hasLaplace_pow`, `TauCeti.hasLaplace_cexp_mul_pow`, and `TauCeti.hasLaplace_exp_mul_pow`:
  monomials and damped monomials have Laplace transform `k! / (s - w) ^ (k + 1)`.

## References

* Jiří Lebl, *Notes on Diffy Qs: Differential Equations for Engineers*, version 6.11 (2026),
  Table 6.2, for elementary Laplace transforms.
-/

public section

open MeasureTheory Set

namespace TauCeti

/-- For `0 < s.re`, the constant function `v` in a complex Banach space has Laplace transform
`s⁻¹ • v`. -/
theorem hasLaplace_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (v : E) {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (fun _ : ℝ ↦ v) s (s⁻¹ • v) := by
  have hsneg : (-s).re < 0 := by simpa using hs
  refine HasLaplace.intro ((integrableOn_exp_mul_complex_Ioi hsneg 0).smul_const v) ?_
  rw [integral_smul_const, integral_exp_mul_complex_Ioi hsneg 0, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero, neg_div_neg_eq, one_div]

/-- For `0 < s.re`, the constant function `1 : ℝ → ℂ` has Laplace transform `s⁻¹ = 1 / s`. -/
theorem hasLaplace_one {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (fun _ : ℝ ↦ (1 : ℂ)) s s⁻¹ := by
  simpa using hasLaplace_const (1 : ℂ) hs

/-- For `s.re ≤ 0` and any nonzero vector `v`, the constant function `v` has no convergent
one-sided Laplace transform, even though the totalized Bochner integral at `s = 0` equals `0`. -/
theorem not_hasLaplace_const_of_re_nonpos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {v : E} (hv : v ≠ 0) {s : ℂ} (hs : s.re ≤ 0) (z : E) :
    ¬ HasLaplace (fun _ : ℝ ↦ v) s z := by
  intro h
  have hexp : IntegrableOn (fun t : ℝ ↦ Complex.exp (-s * t)) (Ioi 0) :=
    (integrable_smul_const hv).mp h.integrableOn
  have hnorm : IntegrableOn (fun t : ℝ ↦ Real.exp (-s.re * t)) (Ioi 0) :=
    hexp.norm.congr (.of_forall fun t ↦ by simp [Complex.norm_exp, neg_mul])
  have hlt : -s.re < 0 := integrableOn_exp_mul_Ioi_iff.mp hnorm
  linarith

/-- For `s.re ≤ 0`, the constant function `1 : ℝ → ℂ` has no convergent one-sided Laplace
transform, even though the totalized Bochner integral at `s = 0` equals `0`. -/
theorem not_hasLaplace_one_of_re_nonpos {s : ℂ} (hs : s.re ≤ 0) (z : ℂ) :
    ¬ HasLaplace (fun _ : ℝ ↦ (1 : ℂ)) s z :=
  not_hasLaplace_const_of_re_nonpos one_ne_zero hs z

/-- For `0 ≤ a` and `0 < s.re`, the indicator of `[a, ∞)` has Laplace transform
`exp (-s * a) / s`. -/
theorem hasLaplace_indicator_Ici_one {a : ℝ} (ha : 0 ≤ a) {s : ℂ} (hs : 0 < s.re) :
    HasLaplace ((Ici a).indicator fun _ ↦ (1 : ℂ)) s (Complex.exp (-s * a) / s) := by
  simpa [div_eq_mul_inv] using (hasLaplace_one hs).indicator_Ici_comp_sub_right ha

/-- For `w.re < s.re`, `t ↦ exp (w * t)` has Laplace transform `(s - w)⁻¹`. -/
theorem hasLaplace_cexp_mul {w s : ℂ} (hws : w.re < s.re) :
    HasLaplace (fun t : ℝ ↦ Complex.exp (w * t)) s (s - w)⁻¹ := by
  have hs : 0 < (s - w).re := by
    rw [Complex.sub_re]
    linarith
  simpa using (hasLaplace_one hs).cexp_mul_smul

/-- For `0 < s.re` and `k : ℕ`, `t ↦ (t : ℂ) ^ k` has Laplace transform `k! / s ^ (k + 1)`. -/
theorem hasLaplace_pow (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasLaplace (fun t : ℝ ↦ (t : ℂ) ^ k) s ((k.factorial : ℂ) / s ^ (k + 1)) := by
  have hk : 0 < (((k + 1 : ℕ) : ℂ)).re := by rw [Complex.natCast_re]; positivity
  have hfun : (fun t : ℝ ↦ Complex.exp (-s * t) • (t : ℂ) ^ k) =
      fun t : ℝ ↦ (t : ℂ) ^ (((k + 1 : ℕ) : ℂ) - 1) * Complex.exp (-(s * t)) := by
    ext t
    simp [mul_comm]
  refine HasLaplace.intro ?_ ?_
  · rw [hfun]
    exact Complex.integrableOn_cpow_mul_exp_neg_mul_Ioi hk hs
  · rw [hfun, Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos hk hs, Complex.cpow_neg,
      Complex.cpow_natCast]
    simp [Complex.Gamma_nat_eq_factorial, div_eq_mul_inv]

/-- For `w.re < s.re` and `k : ℕ`, `t ↦ exp (w * t) * (t : ℂ) ^ k` has Laplace transform
`k! / (s - w) ^ (k + 1)`. -/
theorem hasLaplace_cexp_mul_pow (k : ℕ) {w s : ℂ} (hws : w.re < s.re) :
    HasLaplace (fun t : ℝ ↦ Complex.exp (w * t) * (t : ℂ) ^ k) s
      ((k.factorial : ℂ) / (s - w) ^ (k + 1)) := by
  have hs : 0 < (s - w).re := by
    rw [Complex.sub_re]
    linarith
  simpa only [smul_eq_mul] using (hasLaplace_pow k hs).cexp_mul_smul

/-- For `a < s.re` and `k : ℕ`, the real damped monomial `t ↦ exp (a * t) * t ^ k` (cast to `ℂ`)
has Laplace transform `k! / (s - a) ^ (k + 1)`. -/
theorem hasLaplace_exp_mul_pow (k : ℕ) {a : ℝ} {s : ℂ} (has : a < s.re) :
    HasLaplace (fun t : ℝ ↦ ((Real.exp (a * t) * t ^ k : ℝ) : ℂ)) s
      ((k.factorial : ℂ) / (s - a) ^ (k + 1)) := by
  refine (hasLaplace_cexp_mul_pow k (w := (a : ℂ)) (by simpa using has)).congr_ae ?_
  exact .of_forall fun t ↦ by simp [Complex.ofReal_exp]

end TauCeti
