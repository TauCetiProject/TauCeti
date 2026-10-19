/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# The modified Bessel function of the first kind

This file defines the modified Bessel function of the first kind of real order `ν` at a real
argument `x`. For `x > 0`, it satisfies
`I_ν(x) = (x / 2) ^ ν ₀F₁(; ν + 1; x ^ 2 / 4) = ∑ⱼ (x / 2) ^ (2 j + ν) / (j! Γ(j + ν + 1))`,
and develops its basic real-variable theory.

The definition follows the shape of Mathlib's `Complex.besselJ`: `Real.besselI ν x` is the real
part of `(x / 2) ^ ν * ₀F₁(; ν + 1; (x / 2) ^ 2)`, computed with the complex power and Mathlib's
regularized hypergeometric function `Complex.regularizedHGFun`. The regularization (dividing by
`Γ(j + ν + 1)` rather than by a Pochhammer symbol) makes the series meaningful for every real `ν`.
For `x > 0`, or for an integer order, the complex power is real and `Real.besselI ν x` is the
classical value. At `x = 0`, the definition is totalized to `1` for `ν = 0` and `0` otherwise;
these values agree with the classical continuous extension for nonnegative or integer orders.
For `x < 0` and non-integer `ν` the value is the real part of the principal branch, matching the
totalization of `Real.rpow`.

The modified Bessel functions appear in the densities of the noncentral chi-squared, von Mises and
von Mises–Fisher laws.

## Main declarations

* `Real.besselI` — the modified Bessel function of the first kind `I_ν(x)`.
* `Real.besselI_eq_rpow_mul` — `I_ν(x) = (x / 2) ^ ν * ₀F₁(; ν + 1; (x / 2) ^ 2)` with the real
  power.
* `Real.hasSum_besselI` — the series `∑ⱼ (x / 2) ^ (2 j + ν) / (j! Γ(j + ν + 1))` for `x > 0`.
* `Real.besselI_pos` — `I_ν(x) > 0` for `ν > -1` and `x > 0`.
* `Real.besselI_zero` — `I_0(0) = 1` and `I_ν(0) = 0` for `ν ≠ 0`.
* `Real.tendsto_rpow_neg_mul_besselI_nhdsGT_zero` — `(x / 2) ^ (-ν) I_ν(x) → 1 / Γ(ν + 1)` as
  `x → 0⁺`.
* `Real.continuousAt_besselI`, `Real.continuous_besselI_natCast`, `Real.measurable_besselI` —
  joint continuity away from `x = 0` (and at `x = 0` for `ν > 0`), continuity in `x` for natural
  orders, and joint measurability.
* `Real.hasDerivAt_besselI` — `I_ν'(x) = I_{ν+1}(x) + (ν / x) I_ν(x)`.
* `Real.besselI_sub_besselI` — the recurrence `I_{ν-1}(x) - I_{ν+1}(x) = (2 ν / x) I_ν(x)`.

## References

* *NIST Digital Library of Mathematical Functions*, §10.25 (definition and power series) and
  §10.29 (recurrence relations and derivatives).
* [mathlib4#43070](https://github.com/leanprover-community/mathlib4/pull/43070), whose proposed
  `Complex.besselI` formula this real-part definition follows.
-/

public section

noncomputable section

open Filter Set
open scoped Nat Topology

namespace Real

/-- The modified Bessel function of the first kind `I_ν(x)` of real order `ν` at a real argument
`x`: the real part of `(x / 2) ^ ν * ₀F₁(; ν + 1; (x / 2) ^ 2)`, with the complex power and the
regularized hypergeometric function `₀F₁`. -/
@[pp_nodot]
def besselI (ν x : ℝ) : ℝ :=
  (((x : ℂ) / 2) ^ (ν : ℂ) * Complex.regularizedHGFun 0 {(ν : ℂ) + 1} (((x : ℂ) / 2) ^ 2)).re

/-- Unfolds `Real.besselI` to the real part of the complex formula defining it. -/
theorem besselI_def (ν x : ℝ) :
    besselI ν x =
      (((x : ℂ) / 2) ^ (ν : ℂ) * Complex.regularizedHGFun 0 {(ν : ℂ) + 1} (((x : ℂ) / 2) ^ 2)).re :=
  (rfl)

/-- `I_ν(x) = (x / 2) ^ ν * ₀F₁(; ν + 1; (x / 2) ^ 2)`, with the real power `Real.rpow` and the
(real) value of `₀F₁` at a real argument. -/
theorem besselI_eq_rpow_mul (ν x : ℝ) :
    besselI ν x =
      (x / 2) ^ ν * (Complex.regularizedHGFun 0 {((ν + 1 : ℝ) : ℂ)} ((x / 2) ^ 2 : ℝ)).re := by
  have hF := Complex.regularizedHGFun_zero_singleton_ofReal_im (ν + 1) ((x / 2) ^ 2)
  rw [besselI_def, rpow_def]
  push_cast at hF ⊢
  rw [Complex.mul_re, hF, mul_zero, sub_zero]

/-- For `x > 0`, `I_ν(x)` is the sum of its power series
`∑ⱼ (x / 2) ^ (2 j + ν) / (j! Γ(j + ν + 1))`. -/
theorem hasSum_besselI (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun j : ℕ => (x / 2) ^ (2 * j + ν) / (j ! * Gamma (j + ν + 1))) (besselI ν x) := by
  have hx2 : 0 < x / 2 := by positivity
  have hcast (j : ℕ) : 2 * (j : ℝ) + ν = ((2 * j : ℕ) : ℝ) + ν := by
    push_cast
    ring
  have hadd (j : ℕ) : (j : ℝ) + ν + 1 = ν + 1 + j := by ring
  rw [besselI_eq_rpow_mul]
  convert (Complex.hasSum_regularizedHGFun_zero_singleton_ofReal_re (ν + 1) ((x / 2) ^ 2)).mul_left
    ((x / 2) ^ ν) using 2 with j
  rw [hcast, rpow_add hx2, rpow_natCast, pow_mul, hadd]
  ring

/-- `I_ν(x)` is positive for `ν > -1` and `x > 0`. -/
theorem besselI_pos {ν x : ℝ} (hν : -1 < ν) (hx : 0 < x) : 0 < besselI ν x := by
  have hterm (j : ℕ) : 0 < (x / 2) ^ (2 * j + ν) / (j ! * Gamma (j + ν + 1)) := by
    have hj : 0 < (j : ℝ) + ν + 1 := by linarith [j.cast_nonneg (α := ℝ)]
    have := Gamma_pos_of_pos hj
    positivity
  exact hasSum_lt (f := 0) (i := 0) (fun j => (hterm j).le) (hterm 0) hasSum_zero
    (hasSum_besselI ν hx)

/-- `I_ν(0)` is `1` for `ν = 0` and `0` otherwise. -/
@[simp]
theorem besselI_zero (ν : ℝ) : besselI ν 0 = if ν = 0 then 1 else 0 := by
  split_ifs with h
  · simp [h, besselI_eq_rpow_mul]
  · simp [besselI_eq_rpow_mul, zero_rpow h]

private theorem continuous_regularizedHGFun_besselI :
    Continuous fun p : ℝ × ℝ =>
      (Complex.regularizedHGFun 0 {((p.1 + 1 : ℝ) : ℂ)} ((p.2 / 2) ^ 2 : ℝ)).re :=
  Complex.continuous_regularizedHGFun_zero_singleton_ofReal_re.comp
    (f := fun p : ℝ × ℝ => (p.1 + 1, (p.2 / 2) ^ 2)) (by fun_prop)

/-- Near `0` from the right, `I_ν(x)` behaves like `(x / 2) ^ ν / Γ(ν + 1)`:
`(x / 2) ^ (-ν) I_ν(x) → 1 / Γ(ν + 1)` as `x → 0⁺`. The limit is `0` when `ν + 1` is a nonpositive
integer, where `1 / Γ` vanishes. -/
theorem tendsto_rpow_neg_mul_besselI_nhdsGT_zero (ν : ℝ) :
    Tendsto (fun x => (x / 2) ^ (-ν) * besselI ν x) (𝓝[>] 0) (𝓝 (Gamma (ν + 1))⁻¹) := by
  have hcont : Tendsto (fun x : ℝ =>
      (Complex.regularizedHGFun 0 {((ν + 1 : ℝ) : ℂ)} ((x / 2) ^ 2 : ℝ)).re) (𝓝[>] 0)
      (𝓝 (Complex.regularizedHGFun 0 {((ν + 1 : ℝ) : ℂ)} ((0 / 2) ^ 2 : ℝ)).re) :=
    (continuous_regularizedHGFun_besselI.comp
      (f := fun x : ℝ => (ν, x)) (by fun_prop)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h0 : (Complex.regularizedHGFun 0 {((ν + 1 : ℝ) : ℂ)} ((0 / 2) ^ 2 : ℝ)).re =
      (Gamma (ν + 1))⁻¹ := by
    have hzero : ((0 / 2) ^ 2 : ℝ) = 0 := by norm_num
    rw [hzero, Complex.ofReal_zero, Complex.regularizedHGFun_zero,
      Complex.regularizedHGFunCoeff_zero_singleton]
    simp only [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, add_zero]
    rw [Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.ofReal_re]
  rw [h0] at hcont
  refine hcont.congr' (eventually_nhdsWithin_of_forall fun x (hx : 0 < x) => ?_)
  have hx2 : 0 < x / 2 := by positivity
  dsimp only
  rw [besselI_eq_rpow_mul, ← mul_assoc, ← rpow_add hx2, neg_add_cancel, rpow_zero, one_mul]

/-- `I_ν(x)` is jointly continuous in the order `ν` and the argument `x` at every point with
`x ≠ 0`, and also at `x = 0` when `ν > 0`. -/
theorem continuousAt_besselI {ν x : ℝ} (h : x ≠ 0 ∨ 0 < ν) :
    ContinuousAt (fun p : ℝ × ℝ => besselI p.1 p.2) (ν, x) := by
  simp_rw [besselI_eq_rpow_mul]
  have hpow : ContinuousAt (fun p : ℝ × ℝ => (p.2 / 2) ^ p.1) (ν, x) :=
    (continuous_snd.div_const 2).continuousAt.rpow continuous_fst.continuousAt (by simpa using h)
  exact hpow.mul continuous_regularizedHGFun_besselI.continuousAt

/-- For a natural order `n`, `I_n` is continuous on all of `ℝ`. -/
theorem continuous_besselI_natCast (n : ℕ) : Continuous (besselI n) := by
  have h : besselI n = fun x => (x / 2) ^ n *
      (Complex.regularizedHGFun 0 {((n + 1 : ℝ) : ℂ)} ((x / 2) ^ 2 : ℝ)).re :=
    funext fun x => by rw [besselI_eq_rpow_mul, rpow_natCast]
  rw [h]
  exact (by fun_prop : Continuous fun x : ℝ => (x / 2) ^ n).mul
    (continuous_regularizedHGFun_besselI.comp (f := fun x : ℝ => ((n : ℝ), x)) (by fun_prop))

/-- `I_ν(x)` is jointly measurable in the order `ν` and the argument `x`. -/
@[fun_prop]
theorem measurable_besselI : Measurable fun p : ℝ × ℝ => besselI p.1 p.2 := by
  simp_rw [besselI_eq_rpow_mul]
  exact ((measurable_snd.div_const 2).pow measurable_fst).mul
    continuous_regularizedHGFun_besselI.measurable

/-- The derivative `I_ν'(x) = I_{ν+1}(x) + (ν / x) I_ν(x)` for `x ≠ 0`. -/
theorem hasDerivAt_besselI (ν : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (besselI ν) (besselI (ν + 1) x + ν / x * besselI ν x) x := by
  have hx2 : x / 2 ≠ 0 := div_ne_zero hx two_ne_zero
  have hpow := ((hasDerivAt_id' x).div_const 2).rpow_const (p := ν) (Or.inl hx2)
  have hF := (Complex.hasDerivAt_regularizedHGFun_zero_singleton_ofReal_re (ν + 1)
    ((x / 2) ^ 2)).comp x (((hasDerivAt_id' x).div_const 2).pow 2)
  refine ((hpow.mul hF).congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [Pi.mul_apply, Function.comp_apply, Pi.pow_apply, besselI_eq_rpow_mul]
  rw [besselI_eq_rpow_mul, besselI_eq_rpow_mul, rpow_sub_one hx2, rpow_add_one hx2]
  simp only [Function.comp_apply, Pi.pow_apply]
  push_cast
  field_simp
  ring

/-- The recurrence `I_{ν-1}(x) - I_{ν+1}(x) = (2 ν / x) I_ν(x)` for `x ≠ 0`. -/
theorem besselI_sub_besselI (ν : ℝ) {x : ℝ} (hx : x ≠ 0) :
    besselI (ν - 1) x - besselI (ν + 1) x = 2 * ν / x * besselI ν x := by
  have hx2 : x / 2 ≠ 0 := div_ne_zero hx two_ne_zero
  have hsub : ((ν - 1 + 1 : ℝ) : ℂ) = ν := by
    push_cast
    ring
  have hadd_two : ((ν + 1 + 1 : ℝ) : ℂ) = ν + 2 := by
    push_cast
    ring
  have hadd_one : ((ν + 1 : ℝ) : ℂ) = ν + 1 := by
    push_cast
    ring
  have h := congrArg Complex.re
    (Complex.regularizedHGFun_zero_singleton_eq_mul_add_mul (ν : ℂ) (((x / 2) ^ 2 : ℝ) : ℂ))
  rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at h
  rw [besselI_eq_rpow_mul, besselI_eq_rpow_mul, besselI_eq_rpow_mul,
    hsub, hadd_two, hadd_one, h, rpow_sub_one hx2, rpow_add_one hx2]
  field_simp
  ring

end Real
