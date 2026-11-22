/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Differentiation involving the logarithm

For `x ≠ 0`, a function `v ∘ log` is differentiable at `x` exactly when `v` is differentiable at
`log x`, by evenness of `v ∘ log` for `x < 0`.
Where `0 < f ≤ 1`, the gradient of `f = exp (log f)` is at most that of `log f`.
The derivative of `x / log x ^ n` is also computed wherever `log x ≠ 0`, together with its
real-exponent analogue `x / log x ^ k` wherever `log x > 0`, and that of `r ↦ log (c / r)`
wherever `c ≠ 0` and `r ≠ 0`.

## Main results

* `TauCeti.differentiableAt_comp_log_iff`: differentiability of `v ∘ log` at `x ≠ 0` is
  differentiability of `v` at `log x`.
* `TauCeti.mul_deriv_comp_log`: under `x = e^y` the operator `x d/dx` is `d/dy`.
* `TauCeti.norm_fderiv_le_norm_fderiv_log`: where `0 < f z ≤ 1`, `‖∇ f‖ ≤ ‖∇ log f‖`.
* `TauCeti.Real.hasDerivAt_div_log_pow`: the derivative of `x / log x ^ n` for every natural
  exponent, assuming `log x ≠ 0`.
* `Real.hasDerivAt_div_log_rpow`: the derivative of `x / log x ^ k` for every real
  exponent, assuming `log x > 0`.
* `Real.hasDerivAt_log_const_div`: the derivative of `log (c / r)` is `-r⁻¹`.

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

/-- Where `0 < f z ≤ 1`, the gradient of `f` is at most the gradient of `log f`, since
`∇ f = f ∇ log f`. -/
theorem norm_fderiv_le_norm_fderiv_log {f : E → ℝ} {z : E} (hf : DifferentiableAt ℝ f z)
    (h₀ : 0 < f z) (h₁ : f z ≤ 1) : ‖fderiv ℝ f z‖ ≤ ‖fderiv ℝ (fun w ↦ log (f w)) z‖ := by
  rw [(hf.hasFDerivAt.log h₀.ne').fderiv, norm_smul, norm_inv, Real.norm_of_nonneg h₀.le,
    le_inv_mul_iff₀ h₀]
  exact mul_le_of_le_one_left (norm_nonneg _) h₁

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

namespace Real

/-- The derivative of `t ↦ t / log t ^ k` wherever `log t > 0`, for every real exponent `k`. -/
theorem hasDerivAt_div_log_rpow (k : ℝ) {t : ℝ} (ht : 0 < log t) :
    HasDerivAt (fun u : ℝ ↦ u / log u ^ k)
      ((log t ^ k)⁻¹ - k * (log t ^ (k + 1))⁻¹) t := by
  have ht₀ : t ≠ 0 := by
    intro h
    simp [h] at ht
  have hpow :
      HasDerivAt (fun u : ℝ ↦ log u ^ k) (k * log t ^ (k - 1) * t⁻¹) t := by
    simpa [Function.comp_def] using
      (hasDerivAt_rpow_const (x := log t) (p := k) (Or.inl ht.ne')).comp t (hasDerivAt_log ht₀)
  have hd := (hasDerivAt_id' t).div hpow (rpow_pos_of_pos ht k).ne'
  refine hd.congr_deriv ?_
  have hrpow_pos : 0 < log t ^ k := rpow_pos_of_pos ht k
  have hadd : log t ^ (k + 1) = log t ^ k * log t := by
    rw [rpow_add ht, rpow_one]
  have hsub : log t ^ (k - 1) * log t = log t ^ k := by
    rw [← rpow_add_one ht.ne', sub_add_cancel]
  rw [hadd]
  have hlne : log t ≠ 0 := ht.ne'
  field_simp [ht₀, hrpow_pos.ne', hlne]
  linear_combination -k * hsub

/-- The derivative of `r ↦ log (c / r)` is `-r⁻¹`, for `c ≠ 0` and `r ≠ 0`. -/
theorem hasDerivAt_log_const_div {c r : ℝ} (hc : c ≠ 0) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => log (c / s)) (-r⁻¹) r := by
  have hdiv : HasDerivAt (fun s : ℝ => c / s) (-(c / r ^ 2)) r := by
    simpa only [div_eq_mul_inv, neg_mul_eq_mul_neg, ← inv_pow] using
      (hasDerivAt_inv hr).const_mul c
  refine (hdiv.log (div_ne_zero hc hr)).congr_deriv ?_
  field_simp

end Real
