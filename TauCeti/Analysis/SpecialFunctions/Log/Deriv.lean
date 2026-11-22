/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import TauCeti.Analysis.Calculus.Deriv.ZPow
import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal

/-!
# Differentiation involving the logarithm

For `x ≠ 0`, a function `v ∘ log` is differentiable at `x` exactly when `v` is differentiable at
`log x`, by evenness of `v ∘ log` for `x < 0`.
Where `0 < f ≤ 1`, the gradient of `f = exp (log f)` is at most that of `log f`.
The derivative of `x / log x ^ n` is also computed wherever `log x ≠ 0`, that of `r ↦ log (c / r)`
wherever `c ≠ 0` and `r ≠ 0`, the higher derivatives `iteratedDeriv k Real.log` for `k ≥ 1`, and
the real-parameter smoothness and higher derivatives of `t ↦ Complex.log (t + z)` wherever
`t + z ∈ Complex.slitPlane`.

## Main results

* `TauCeti.differentiableAt_comp_log_iff`: differentiability of `v ∘ log` at `x ≠ 0` is
  differentiability of `v` at `log x`.
* `TauCeti.mul_deriv_comp_log`: under `x = e^y` the operator `x d/dx` is `d/dy`.
* `TauCeti.norm_fderiv_le_norm_fderiv_log`: where `0 < f z ≤ 1`, `‖∇ f‖ ≤ ‖∇ log f‖`.
* `TauCeti.Real.hasDerivAt_div_log_pow`: the derivative of `x / log x ^ n` for every natural
  exponent, assuming `log x ≠ 0`.
* `Real.hasDerivAt_log_const_div`: the derivative of `log (c / r)` is `-r⁻¹`.
* `Real.iteratedDeriv_log`: for `k ≥ 1`, `iteratedDeriv k log x = (-1)^(k-1) (k-1)! / x^k`.
* `Complex.contDiffAt_log_ofReal_add`, `Complex.hasDerivAt_log_ofReal_add`,
  `Complex.iteratedDeriv_log_ofReal_add`: smoothness, first derivative, and higher derivatives of
  `t ↦ Complex.log (t + z)` along `ℝ` whenever `(u : ℂ) + z ∈ Complex.slitPlane`.

The reciprocal-log-power derivative is adapted from the Ramanujan estimates in the
[PrimeNumberTheoremAnd project][PNTLogPower].

[PNTLogPower]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/dc6e36e/PrimeNumberTheoremAnd/IEANTN/Ramanujan/Ramanujan.lean
-/

public section

open Real Filter Topology
open scoped ContDiff Nat

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

/-- The derivative of `r ↦ log (c / r)` is `-r⁻¹`, for `c ≠ 0` and `r ≠ 0`. -/
theorem hasDerivAt_log_const_div {c r : ℝ} (hc : c ≠ 0) (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ => log (c / s)) (-r⁻¹) r := by
  have hdiv : HasDerivAt (fun s : ℝ => c / s) (-(c / r ^ 2)) r := by
    simpa only [div_eq_mul_inv, neg_mul_eq_mul_neg, ← inv_pow] using
      (hasDerivAt_inv hr).const_mul c
  refine (hdiv.log (div_ne_zero hc hr)).congr_deriv ?_
  field_simp

/-- For `k ≥ 1`, the `k`-th derivative of `Real.log` at `x` is
`(-1) ^ (k - 1) * (k - 1)! / x ^ k` (at `x = 0` both sides vanish). -/
theorem iteratedDeriv_log {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    iteratedDeriv k log x = (-1 : ℝ) ^ (k - 1) * ((k - 1)! : ℝ) / x ^ k := by
  have hk_eq : k = (k - 1) + 1 := (Nat.sub_add_cancel hk).symm
  conv_lhs => rw [hk_eq, iteratedDeriv_succ', deriv_log']
  simpa [one_div, Nat.sub_add_cancel hk] using
    TauCeti.iteratedDeriv_const_div (k - 1) (1 : ℝ) x

end Real

namespace Complex

/-- For `(u : ℂ) + z ∈ Complex.slitPlane`, the shifted principal logarithm `t ↦ log (t + z)` is
smooth of arbitrary order at `u : ℝ`. -/
theorem contDiffAt_log_ofReal_add {u : ℝ} {z : ℂ} (h : (u : ℂ) + z ∈ slitPlane)
    (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun t : ℝ ↦ log ((t : ℂ) + z)) u := by
  have hlin : ContDiffAt ℝ n (fun t : ℝ ↦ (t : ℂ) + z) u :=
    ofRealCLM.contDiff.contDiffAt.add contDiffAt_const
  exact ((contDiffAt_log h).restrict_scalars ℝ).comp u hlin

/-- For `(u : ℂ) + z ∈ Complex.slitPlane`, the derivative of `t ↦ log (t + z)` at `u : ℝ` is
`(u + z)⁻¹`. -/
theorem hasDerivAt_log_ofReal_add {u : ℝ} {z : ℂ} (h : (u : ℂ) + z ∈ slitPlane) :
    HasDerivAt (fun t : ℝ ↦ log ((t : ℂ) + z)) (((u : ℂ) + z)⁻¹) u := by
  have hlin : HasDerivAt (fun t : ℝ ↦ (t : ℂ) + z) 1 u := by
    simpa using (hasDerivAt_id (u : ℂ)).comp_ofReal.add_const z
  refine ((hasDerivAt_log h).comp u hlin).congr_deriv ?_
  simp

/-- For `k ≥ 1` and `(u : ℂ) + z ∈ Complex.slitPlane`, the `k`-th derivative of `t ↦ log (t + z)`
at `u : ℝ` is `(-1) ^ (k - 1) * (k - 1)! / (u + z) ^ k`. -/
theorem iteratedDeriv_log_ofReal_add {k : ℕ} (hk : 1 ≤ k) {u : ℝ} {z : ℂ}
    (h : (u : ℂ) + z ∈ slitPlane) :
    iteratedDeriv k (fun t : ℝ ↦ log ((t : ℂ) + z)) u =
      (-1 : ℂ) ^ (k - 1) * ((k - 1)! : ℂ) / ((u : ℂ) + z) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  clear hk
  induction m generalizing u with
  | zero =>
    rw [zero_add, iteratedDeriv_one, (hasDerivAt_log_ofReal_add h).deriv]
    simp [one_div]
  | succ m ih =>
    have hs : {t : ℝ | (t : ℂ) + z ∈ slitPlane} ∈ 𝓝 u :=
      (isOpen_slitPlane.preimage (continuous_ofReal.add continuous_const)).mem_nhds h
    have hev : iteratedDeriv (m + 1) (fun t : ℝ ↦ log ((t : ℂ) + z)) =ᶠ[𝓝 u]
        fun t : ℝ ↦ (-1 : ℂ) ^ m * (m ! : ℂ) / ((t : ℂ) + z) ^ (m + 1) :=
      Filter.eventually_of_mem hs fun _ ht ↦ ih ht
    have hlin : HasDerivAt (fun t : ℝ ↦ (t : ℂ) + z) 1 u := by
      simpa using (hasDerivAt_id (u : ℂ)).comp_ofReal.add_const z
    have hpow := hlin.const_div_pow (slitPlane_ne_zero h) ((-1 : ℂ) ^ m * (m ! : ℂ)) (m + 1)
    rw [iteratedDeriv_succ, hev.deriv_eq, hpow.deriv]
    simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    ring

end Complex
