/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Differentiation involving the logarithm

For `x ≠ 0`, a function `v ∘ log` is differentiable at `x` exactly when `v` is differentiable at
`log x`, by evenness of `v ∘ log` for `x < 0`.
The derivative of `x / log x ^ n` is also computed wherever `log x ≠ 0`.

## Main results

* `TauCeti.differentiableAt_comp_log_iff`: differentiability of `v ∘ log` at `x ≠ 0` is
  differentiability of `v` at `log x`.
* `TauCeti.mul_deriv_comp_log`: under `x = e^y` the operator `x d/dx` is `d/dy`.
* `TauCeti.Real.hasDerivAt_div_log_pow`: the derivative of `x / log x ^ n` for every natural
  exponent, assuming `log x ≠ 0`.

The reciprocal-log-power derivative is adapted from the Ramanujan estimates in the
[PrimeNumberTheoremAnd project][PNTLogPower].

[PNTLogPower]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/dc6e36e/PrimeNumberTheoremAnd/IEANTN/Ramanujan/Ramanujan.lean
-/

public section

open Real Filter Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : ℝ → E} {x : ℝ}

/-- For `x ≠ 0`, `v ∘ log` is differentiable at `x` exactly when `v` is differentiable at `log x`.
For `x < 0` this uses that `v ∘ log` is even. -/
@[simp]
theorem differentiableAt_comp_log_iff (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun x ↦ v (log x)) x ↔ DifferentiableAt ℝ v (log x) := by
  refine ⟨fun h ↦ ?_, fun hv ↦ hv.comp x (differentiableAt_log hx)⟩
  have hg : DifferentiableAt ℝ (fun x ↦ v (log x)) (exp (log x)) := by
    rw [exp_log_eq_abs hx]
    rcases hx.lt_or_gt with hneg | hpos
    · rw [abs_of_neg hneg]
      have h' : DifferentiableAt ℝ (fun x ↦ v (log x)) (-(-x)) := by simpa using h
      exact (h'.comp (-x) differentiableAt_id.neg).congr_of_eventuallyEq
        (Eventually.of_forall fun t ↦ by simp [log_neg_eq_log])
    · rwa [abs_of_pos hpos]
  exact (hg.comp (log x) differentiableAt_exp).congr_of_eventuallyEq
    (Eventually.of_forall fun y ↦ by simp [log_exp])

section

variable {v : ℝ → ℝ} {x : ℝ}

/-- Under the change of variables `x = e^y` the operator `x d/dx` is `d/dy`:
`x (v ∘ log)'(x) = v'(log x)` for `x ≠ 0`. If `v` is not differentiable at `log x`, then `v ∘ log`
is not differentiable at `x` either, and both sides are `0`. -/
theorem mul_deriv_comp_log (hx : x ≠ 0) :
    x * deriv (fun x ↦ v (log x)) x = deriv v (log x) := by
  by_cases hv : DifferentiableAt ℝ v (log x)
  · have h : HasDerivAt (fun x ↦ v (log x)) (deriv v (log x) * x⁻¹) x :=
      hv.hasDerivAt.comp x (hasDerivAt_log hx)
    rw [h.deriv]
    field_simp
  · rw [deriv_zero_of_not_differentiableAt hv,
      deriv_zero_of_not_differentiableAt (mt (differentiableAt_comp_log_iff hx).1 hv), mul_zero]

end

end TauCeti

namespace TauCeti.Real

/-- The derivative of `t ↦ t / log t ^ n` wherever `log t ≠ 0`, for every natural exponent. -/
theorem hasDerivAt_div_log_pow (n : ℕ) {t : ℝ} (ht : Real.log t ≠ 0) :
    HasDerivAt (fun u : ℝ ↦ u / Real.log u ^ n)
      ((Real.log t ^ n)⁻¹ - (n : ℝ) * (Real.log t ^ (n + 1))⁻¹) t := by
  have ht₀ : t ≠ 0 := by
    intro h
    exact ht (by simp [h])
  cases n with
  | zero =>
      simpa only [pow_zero, inv_one, Nat.cast_zero, zero_mul, sub_zero, div_one] using
        hasDerivAt_id' t
  | succ n =>
      have hd := (hasDerivAt_id' t).div ((Real.hasDerivAt_log ht₀).pow (n + 1))
        (pow_ne_zero _ ht)
      apply hd.congr_deriv
      simp only [Pi.pow_apply, Nat.add_one_sub_one, one_mul]
      field_simp [pow_succ, ht, ht₀]
      ring

end TauCeti.Real
