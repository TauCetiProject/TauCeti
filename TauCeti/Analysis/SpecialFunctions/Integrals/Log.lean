/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import TauCeti.MeasureTheory.Integral.RpowLaplace

/-!
# Logarithmic power integrals on `(0, 1]`

For `-1 < p` and `k : ℕ`, the substitution `t = exp (-u)` identifies the logarithmic moment
`∫ t in 0..1, t ^ p * (-log t) ^ k` with Euler's Gamma integral
`∫ u in Ioi 0, u ^ k * exp (-((p + 1) * u)) = k! / (p + 1) ^ (k + 1)`.

We first record the exponential substitutions `y = exp x` on `(-∞, a]` and `y = exp (-x)` on
`(a, ∞)` for Banach-space-valued integrands, complementing Mathlib's `integral_comp_exp_Ioi`.
From `a = 0` we deduce interval integrability and the closed form of `t ^ p * (-log t) ^ k` and
`t ^ p * (log t) ^ k` on `0..1`, together with their natural-power specializations.

## Main declarations

* `TauCeti.integral_comp_exp_Iic`, `TauCeti.integrableOn_comp_exp_Iic`: substitution `y = exp x`
  between `(-∞, a]` and `(0, exp a]`.
* `TauCeti.integral_comp_exp_neg_Ioi`, `TauCeti.integrableOn_comp_exp_neg_Ioi`: substitution
  `y = exp (-x)` between `(a, ∞)` and `(0, exp (-a)]`.
* `TauCeti.intervalIntegrable_rpow_mul_neg_log_pow`,
  `TauCeti.intervalIntegrable_rpow_mul_log_pow`: interval integrability on `0..1` for `-1 < p`.
* `TauCeti.integral_rpow_mul_neg_log_pow`, `TauCeti.integral_rpow_mul_log_pow`: closed-form
  evaluations `k! / (p + 1) ^ (k + 1)` and `(-1) ^ k * k! / (p + 1) ^ (k + 1)`.
* `TauCeti.intervalIntegrable_pow_mul_neg_log_pow`, `TauCeti.integral_pow_mul_neg_log_pow`:
  natural-exponent specializations `t ^ j * (-log t) ^ k`.
-/

public section

open MeasureTheory Real Set

namespace TauCeti

section ExpSubstitution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Substitution `y = exp x` in integrals over `(-∞, a]`. -/
theorem integral_comp_exp_Iic (g : ℝ → E) (a : ℝ) :
    ∫ x in Iic a, exp x • g (exp x) = ∫ y in Ioc 0 (exp a), g y := by
  symm
  rw [← image_exp_Iic]
  simpa [abs_of_pos (exp_pos _)] using integral_image_eq_integral_abs_deriv_smul
    (measurableSet_Iic (a := a)) (fun x _ ↦ (hasDerivAt_exp x).hasDerivWithinAt)
    (fun _ _ _ _ hxy ↦ exp_injective hxy) g

/-- Substitution `y = exp x` in integrals over `(-∞, a]` preserves integrability. -/
theorem integrableOn_comp_exp_Iic (g : ℝ → E) (a : ℝ) :
    IntegrableOn (fun x ↦ exp x • g (exp x)) (Iic a) ↔ IntegrableOn g (Ioc 0 (exp a)) := by
  symm
  rw [← image_exp_Iic]
  simpa [abs_of_pos (exp_pos _)] using integrableOn_image_iff_integrableOn_abs_deriv_smul
    (measurableSet_Iic (a := a)) (fun x _ ↦ (hasDerivAt_exp x).hasDerivWithinAt)
    (fun _ _ _ _ hxy ↦ exp_injective hxy) g

/-- Substitution `y = exp (-x)` in integrals over `(a, ∞)`. -/
theorem integral_comp_exp_neg_Ioi (g : ℝ → E) (a : ℝ) :
    ∫ x in Ioi a, exp (-x) • g (exp (-x)) = ∫ y in Ioc 0 (exp (-a)), g y := by
  rw [← integral_comp_exp_Iic, ← integral_comp_neg_Ioi]

/-- Substitution `y = exp (-x)` in integrals over `(a, ∞)` preserves integrability. -/
theorem integrableOn_comp_exp_neg_Ioi (g : ℝ → E) (a : ℝ) :
    IntegrableOn (fun x ↦ exp (-x) • g (exp (-x))) (Ioi a) ↔
      IntegrableOn g (Ioc 0 (exp (-a))) := by
  have himg : (fun x ↦ exp (-x)) '' Ici a = Ioc 0 (exp (-a)) := by
    rw [← Function.comp_def exp Neg.neg, image_comp, image_neg_Ici, image_exp_Iic]
  have hderiv : ∀ x ∈ Ici a,
      HasDerivWithinAt (fun x ↦ exp (-x)) (exp (-x) * -1) (Ici a) x :=
    fun x _ ↦ ((hasDerivAt_id x).neg.exp).hasDerivWithinAt
  rw [← integrableOn_Ici_iff_integrableOn_Ioi, ← himg,
    integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ici hderiv
      (fun _ _ _ _ hxy ↦ neg_injective (exp_injective hxy)) g]
  refine integrableOn_congr_fun (fun x _ ↦ ?_) measurableSet_Ici
  rw [mul_neg_one, abs_neg, abs_of_pos (exp_pos _)]

end ExpSubstitution

/-- Under `t = exp (-u)`, the Jacobian-weighted integrand `exp (-u) * (t ^ p * (-log t) ^ k)`
becomes Euler's Gamma integrand `u ^ ((k + 1) - 1) * exp (-((p + 1) * u))`. -/
private lemma exp_neg_mul_rpow_mul_neg_log_pow (k : ℕ) (p u : ℝ) :
    exp (-u) * (exp (-u) ^ p * (-log (exp (-u))) ^ k) =
      u ^ ((k + 1 : ℝ) - 1) * exp (-((p + 1) * u)) := by
  rw [log_exp, neg_neg, ← exp_mul, ← mul_assoc, ← exp_add, add_sub_cancel_right, rpow_natCast]
  ring_nf

/-- For `-1 < p` and `k : ℕ`, the logarithmic moment integrand `t ↦ t ^ p * (-log t) ^ k` is
interval integrable on `0..1`. -/
theorem intervalIntegrable_rpow_mul_neg_log_pow (k : ℕ) {p : ℝ} (hp : -1 < p) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ p * (-log t) ^ k) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
    show (1 : ℝ) = exp (-0) by simp, ← integrableOn_comp_exp_neg_Ioi]
  refine (integrableOn_rpow_mul_exp_neg_mul_Ioi (a := k + 1) (r := p + 1) (by positivity)
    (by linarith)).congr_fun (fun u _ ↦ ?_) measurableSet_Ioi
  simpa only [smul_eq_mul] using (exp_neg_mul_rpow_mul_neg_log_pow k p u).symm

/-- For `-1 < p` and `k : ℕ`, `t ↦ t ^ p * (log t) ^ k` is interval integrable on `0..1`. -/
theorem intervalIntegrable_rpow_mul_log_pow (k : ℕ) {p : ℝ} (hp : -1 < p) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ p * log t ^ k) volume 0 1 := by
  refine ((intervalIntegrable_rpow_mul_neg_log_pow k hp).const_mul ((-1 : ℝ) ^ k)).congr
    fun t _ ↦ ?_
  rw [mul_left_comm, ← mul_pow, neg_one_mul, neg_neg]

/-- **Mellin integral of a logarithmic power**: for `-1 < p` and `k : ℕ`,
`∫ t in 0..1, t ^ p * (-log t) ^ k = k! / (p + 1) ^ (k + 1)`. -/
theorem integral_rpow_mul_neg_log_pow (k : ℕ) {p : ℝ} (hp : -1 < p) :
    ∫ t : ℝ in 0..1, t ^ p * (-log t) ^ k = (k.factorial : ℝ) / (p + 1) ^ (k + 1) := by
  have hp1 : 0 < p + 1 := by linarith
  have hsub := integral_comp_exp_neg_Ioi (fun t ↦ t ^ p * (-log t) ^ k) 0
  simp only [neg_zero, exp_zero, smul_eq_mul] at hsub
  rw [intervalIntegral.integral_of_le zero_le_one, ← hsub]
  have hcongr : ∫ u in Ioi (0 : ℝ), exp (-u) * (exp (-u) ^ p * (-log (exp (-u))) ^ k) =
      ∫ u in Ioi (0 : ℝ), u ^ ((k + 1 : ℝ) - 1) * exp (-((p + 1) * u)) :=
    setIntegral_congr_fun measurableSet_Ioi fun u _ ↦ exp_neg_mul_rpow_mul_neg_log_pow k p u
  rw [hcongr, integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hp1, Gamma_nat_eq_factorial,
    show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; rfl, rpow_natCast, one_div_pow,
    one_div_mul_eq_div]

/-- Signed counterpart of `TauCeti.integral_rpow_mul_neg_log_pow`: for `-1 < p` and `k : ℕ`,
`∫ t in 0..1, t ^ p * (log t) ^ k = (-1) ^ k * k! / (p + 1) ^ (k + 1)`. -/
theorem integral_rpow_mul_log_pow (k : ℕ) {p : ℝ} (hp : -1 < p) :
    ∫ t : ℝ in 0..1, t ^ p * log t ^ k = (-1) ^ k * (k.factorial : ℝ) / (p + 1) ^ (k + 1) := by
  have hcongr : (∫ t : ℝ in 0..1, t ^ p * log t ^ k) =
      ∫ t : ℝ in 0..1, (-1 : ℝ) ^ k * (t ^ p * (-log t) ^ k) := by
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    rw [mul_left_comm, ← mul_pow, neg_one_mul, neg_neg]
  rw [hcongr, intervalIntegral.integral_const_mul, integral_rpow_mul_neg_log_pow k hp,
    mul_div_assoc]

/-- Natural-exponent specialization of `TauCeti.intervalIntegrable_rpow_mul_neg_log_pow`. -/
theorem intervalIntegrable_pow_mul_neg_log_pow (j k : ℕ) :
    IntervalIntegrable (fun t : ℝ ↦ t ^ j * (-log t) ^ k) volume 0 1 := by
  refine (intervalIntegrable_rpow_mul_neg_log_pow k (p := (j : ℝ))
    (by linarith [Nat.cast_nonneg (α := ℝ) j])) |>.congr fun t _ ↦ ?_
  rw [rpow_natCast]

/-- Natural-exponent specialization of `TauCeti.integral_rpow_mul_neg_log_pow`:
`∫ t in 0..1, t ^ j * (-log t) ^ k = k! / (j + 1) ^ (k + 1)`. -/
theorem integral_pow_mul_neg_log_pow (j k : ℕ) :
    ∫ t : ℝ in 0..1, t ^ j * (-log t) ^ k = (k.factorial : ℝ) / (j + 1 : ℝ) ^ (k + 1) := by
  have h := integral_rpow_mul_neg_log_pow k (p := (j : ℝ))
    (by linarith [Nat.cast_nonneg (α := ℝ) j])
  rw [← h]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  rw [rpow_natCast]

end TauCeti
