/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Hadamard
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic

import Mathlib.Analysis.Calculus.Deriv.Star
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Growth

/-!
# Hadamard factorization and logarithmic derivative of the completed Riemann zeta function

Combining `orderLE_zetaEntireCompletion`, `zetaEntireCompletion 0 = 1`, confinement of all zeros to
`0 < Re ρ < 1` (`re_mem_Ioo_of_zetaEntireCompletion_eq_zero`), and the functional and conjugation
symmetries (`zetaEntireCompletion_one_sub` and `zetaEntireCompletion_conj`) specializes
`TauCeti.hadamard_of_orderLE_one` and `TauCeti.OrderLE.re_logDeriv_eq_tsum` to twice Riemann's
ξ-function `zetaEntireCompletion`:

* **Hadamard factorization** (`zetaEntireCompletion_eq_cexp_logDeriv_mul_divisorProductOne`,
  `zetaEntireCompletion_hadamard`): `zetaEntireCompletion` factors globally as `exp (a + b * s)`
  times the multipliable genus-one canonical product over its zeros.
* **Cancelled real-part expansion** (`re_logDeriv_zetaEntireCompletion_zero`,
  `re_logDeriv_zetaEntireCompletion_eq_tsum`): `(logDeriv zetaEntireCompletion 0).re =`
  `-∑' ρ, m_ρ * Re (1 / ρ)`, so off the zeros `Re (logDeriv zetaEntireCompletion s)` equals
  `∑' ρ, m_ρ * Re (1 / (s - ρ))` with no additive constant, dominating every finite subsum on
  `1 ≤ Re s` (`sum_divisor_zetaEntireCompletion_toNat_mul_re_one_div_sub_le_re_logDeriv`).

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §11 and §12.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §10.2 and §11.1.
* E. C. Titchmarsh, rev. D. R. Heath-Brown, *The Theory of the Riemann Zeta-Function*, 2nd ed.,
  §2.12.
-/

public section

open Complex ComplexConjugate
open scoped BigOperators

namespace TauCeti.LFunctions

private theorem zetaEntireCompletion_one_sub_eq_conj_conj (z : ℂ) :
    zetaEntireCompletion (1 - z) = 1 * conj (zetaEntireCompletion (conj z)) := by
  rw [one_mul, zetaEntireCompletion_one_sub, zetaEntireCompletion_conj, conj_conj]

/-- **Hadamard factorization of `zetaEntireCompletion`.** Since `zetaEntireCompletion 0 = 1`,
`zetaEntireCompletion s = exp (logDeriv zetaEntireCompletion 0 * s) * divisorProductOne …`. -/
theorem zetaEntireCompletion_eq_cexp_logDeriv_mul_divisorProductOne (s : ℂ) :
    zetaEntireCompletion s =
      exp (logDeriv zetaEntireCompletion 0 * s) * divisorProductOne zetaEntireCompletion s := by
  have h := orderLE_zetaEntireCompletion.eq_mul_cexp_logDeriv_mul_divisorProductOne
    differentiable_zetaEntireCompletion (by simp) s
  simpa using h

/-- **Hadamard product for `zetaEntireCompletion`.** Twice Riemann's ξ-function factors globally as
`exp (a + b * s)` times the multipliable genus-one canonical product over its zeros, with
`exp a = zetaEntireCompletion 0` and `b = logDeriv zetaEntireCompletion 0`. -/
theorem zetaEntireCompletion_hadamard :
    ∃ a b : ℂ, exp a = zetaEntireCompletion 0 ∧ b = logDeriv zetaEntireCompletion 0 ∧ ∀ s : ℂ,
      Multipliable (fun ρ : ℂ ↦
        weierstrassFactorOne (ρ⁻¹ * s) ^
          (MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat) ∧
      zetaEntireCompletion s = exp (a + b * s) * ∏' ρ : ℂ,
        weierstrassFactorOne (ρ⁻¹ * s) ^
          (MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat :=
  hadamard_of_orderLE_one orderLE_zetaEntireCompletion differentiable_zetaEntireCompletion (by simp)

/-- Conjugation commutes with `logDeriv zetaEntireCompletion`. -/
@[simp]
theorem logDeriv_zetaEntireCompletion_conj (s : ℂ) :
    logDeriv zetaEntireCompletion (conj s) = conj (logDeriv zetaEntireCompletion s) := by
  have hfn : zetaEntireCompletion = conj ∘ zetaEntireCompletion ∘ conj :=
    funext fun z ↦ by simp [Function.comp_def]
  conv_lhs => rw [hfn]
  rw [logDeriv_apply, logDeriv_apply, deriv_conj_conj]
  simp

/-- `logDeriv zetaEntireCompletion` is odd across the critical line `s ↦ 1 - s`. -/
theorem logDeriv_zetaEntireCompletion_one_sub (s : ℂ) :
    logDeriv zetaEntireCompletion (1 - s) = -logDeriv zetaEntireCompletion s := by
  have h := logDeriv_one_sub_conj zetaEntireCompletion_one_sub_eq_conj_conj (conj s)
  rwa [conj_conj, logDeriv_zetaEntireCompletion_conj, conj_conj] at h

/-- `logDeriv zetaEntireCompletion` is real on the real axis. -/
@[simp]
theorem im_logDeriv_zetaEntireCompletion_ofReal (σ : ℝ) :
    (logDeriv zetaEntireCompletion σ).im = 0 := by
  refine conj_eq_iff_im.mp ?_
  simpa using (logDeriv_zetaEntireCompletion_conj σ).symm

/-- The paired partial-fraction series of `zetaEntireCompletion` converges absolutely at every
point `s : ℂ`. -/
theorem summable_norm_divisor_zetaEntireCompletion_mul_one_div_sub_add_one_div (s : ℂ) :
    Summable (fun ρ : (MeromorphicOn.divisor zetaEntireCompletion Set.univ).support ↦
      ‖((MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat : ℂ) *
        (1 / (s - ρ) + 1 / ρ)‖) :=
  orderLE_zetaEntireCompletion.summable_norm_divisor_mul_one_div_sub_add_one_div
    differentiable_zetaEntireCompletion (by norm_num) s

/-- The reciprocal real-part series `∑' ρ, m_ρ * Re (1 / ρ)` over the zeros of
`zetaEntireCompletion` is summable. -/
theorem summable_divisor_zetaEntireCompletion_toNat_mul_re_one_div :
    Summable (fun ρ : (MeromorphicOn.divisor zetaEntireCompletion Set.univ).support ↦
      ((MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re) :=
  orderLE_zetaEntireCompletion.summable_divisor_toNat_mul_re_one_div_of_re_le
    differentiable_zetaEntireCompletion (by norm_num)
    (fun _ hρ ↦ (re_mem_Ioo_of_zetaEntireCompletion_eq_zero hρ).2.le)
    zetaEntireCompletion_one_sub_eq_conj_conj

/-- The unsubtracted real-part series `∑' ρ, m_ρ * Re (1 / (s - ρ))` over the zeros of
`zetaEntireCompletion` is summable at every `s : ℂ`. -/
theorem summable_divisor_zetaEntireCompletion_toNat_mul_re_one_div_sub (s : ℂ) :
    Summable (fun ρ : (MeromorphicOn.divisor zetaEntireCompletion Set.univ).support ↦
      ((MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat : ℝ) *
        (1 / (s - ρ)).re) :=
  orderLE_zetaEntireCompletion.summable_divisor_toNat_mul_re_one_div_sub_of_re_le
    differentiable_zetaEntireCompletion (by norm_num)
    (fun _ hρ ↦ (re_mem_Ioo_of_zetaEntireCompletion_eq_zero hρ).2.le)
    zetaEntireCompletion_one_sub_eq_conj_conj s

/-- Paired partial-fraction expansion of `logDeriv zetaEntireCompletion` off the zeros. -/
theorem logDeriv_zetaEntireCompletion_eq_add_tsum {s : ℂ} (hs : zetaEntireCompletion s ≠ 0) :
    logDeriv zetaEntireCompletion s = logDeriv zetaEntireCompletion 0 +
      ∑' ρ : (MeromorphicOn.divisor zetaEntireCompletion Set.univ).support,
        ((MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat : ℂ) *
          (1 / (s - ρ) + 1 / ρ) :=
  orderLE_zetaEntireCompletion.logDeriv_eq_add_tsum differentiable_zetaEntireCompletion (by simp) hs

/-- The real part of the Hadamard linear constant `logDeriv zetaEntireCompletion 0` equals
`-∑' ρ, m_ρ * Re (1 / ρ)`. -/
theorem re_logDeriv_zetaEntireCompletion_zero :
    (logDeriv zetaEntireCompletion 0).re =
      -∑' ρ : (MeromorphicOn.divisor zetaEntireCompletion Set.univ).support,
        ((MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re :=
  orderLE_zetaEntireCompletion.re_logDeriv_zero_eq_neg_tsum differentiable_zetaEntireCompletion
    (by simp) (fun _ hρ ↦ (re_mem_Ioo_of_zetaEntireCompletion_eq_zero hρ).2.le)
    zetaEntireCompletion_one_sub_eq_conj_conj

/-- Cancelled real-part partial-fraction expansion of `logDeriv zetaEntireCompletion` off the
zeros: `Re (logDeriv zetaEntireCompletion s) = ∑' ρ, m_ρ * Re (1 / (s - ρ))`. -/
theorem re_logDeriv_zetaEntireCompletion_eq_tsum {s : ℂ} (hs : zetaEntireCompletion s ≠ 0) :
    (logDeriv zetaEntireCompletion s).re =
      ∑' ρ : (MeromorphicOn.divisor zetaEntireCompletion Set.univ).support,
        ((MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (s - ρ)).re :=
  orderLE_zetaEntireCompletion.re_logDeriv_eq_tsum differentiable_zetaEntireCompletion (by simp)
    (fun _ hρ ↦ (re_mem_Ioo_of_zetaEntireCompletion_eq_zero hρ).2.le)
    zetaEntireCompletion_one_sub_eq_conj_conj hs

/-- On `1 ≤ Re s`, every finite subsum `∑ ρ ∈ S, m_ρ * Re (1 / (s - ρ))` over zeros of
`zetaEntireCompletion` is bounded above by `Re (logDeriv zetaEntireCompletion s)`. -/
theorem sum_divisor_zetaEntireCompletion_toNat_mul_re_one_div_sub_le_re_logDeriv {s : ℂ}
    (hs : 1 ≤ s.re) (S : Finset ℂ) :
    ∑ ρ ∈ S, ((MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat : ℝ) *
      (1 / (s - ρ)).re ≤ (logDeriv zetaEntireCompletion s).re :=
  orderLE_zetaEntireCompletion.sum_divisor_toNat_mul_re_one_div_sub_le_re_logDeriv
    differentiable_zetaEntireCompletion (by simp) zetaEntireCompletion_one_sub_eq_conj_conj
    (zetaEntireCompletion_ne_zero_of_one_le_re hs)
    (fun _ hρ ↦ (re_mem_Ioo_of_zetaEntireCompletion_eq_zero hρ).2.le.trans hs) S

/-- On `1 ≤ Re s`, `Re (logDeriv zetaEntireCompletion s)` is nonnegative. -/
theorem re_logDeriv_zetaEntireCompletion_nonneg {s : ℂ} (hs : 1 ≤ s.re) :
    0 ≤ (logDeriv zetaEntireCompletion s).re := by
  simpa using sum_divisor_zetaEntireCompletion_toNat_mul_re_one_div_sub_le_re_logDeriv hs ∅

end TauCeti.LFunctions
