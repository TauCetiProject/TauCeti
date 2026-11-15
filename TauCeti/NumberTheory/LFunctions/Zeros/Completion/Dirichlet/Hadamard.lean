/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv.Bound
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Hadamard

import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Growth
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.LogDeriv
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Zeros
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta

/-!
# Hadamard factorization and retained-zero inequalities for Dirichlet L-functions

Let `χ` be a primitive Dirichlet character modulo `N`, and write
`Λ₀ = (dirichletData χ hχ).entireCompletion`. For `χ ≠ 1`, `Λ₀` has no poles to clear, while at
conductor `N = 1` it recovers `zetaEntireCompletion`. In all cases `Λ₀` satisfies `Λ₀ 0 ≠ 0`, has
growth order at most `1`, has all its zeros inside the open critical strip `0 < Re ρ < 1`, and
obeys the combined functional and conjugation identity `Λ₀ (1 - z) = ε(χ) * conj (Λ₀ (conj z))`.
Specializing the order-one Hadamard and real-part cancellation theorems gives:

* **Hadamard factorization** (`dirichletData_entireCompletion_hadamard`): for every primitive `χ`,
  `Λ₀` factors globally as `exp (a + b * s)` times the multipliable genus-one canonical product over
  its zeros.
* **Real-part cancellation** (`re_logDeriv_dirichletData_entireCompletion_zero` and
  `re_logDeriv_dirichletData_entireCompletion_eq_tsum`): for every primitive `χ` (real or complex),
  `(logDeriv Λ₀ 0).re = -∑' ρ, m_ρ * (1 / ρ).re`, so off the zeros one has
  `(logDeriv Λ₀ s).re = ∑' ρ, m_ρ * (1 / (s - ρ)).re` with no additive constant.
* **Retained-zero inequalities** (`finite_zero_sum_le_logDeriv` and `one_zero_le_logDeriv`): for
  nonprincipal primitive `χ ≠ 1` and `σ ∈ [1, 2]`, every zero summand `m_ρ * Re (1 / (σ - ρ))` is
  nonnegative and the archimedean logarithmic derivative is bounded in norm by
  `TauCeti.gammaLogDerivBound` (`C_Γ`), so discarding all zeros outside a chosen finite set `S` (or
  keeping a single real zero `0 < β`) yields
  `∑ ρ ∈ S, analyticOrderNatAt χ.LFunction ρ * Re (1 / (σ - ρ)) ≤ Re (L'/L)(σ, χ) + ½ log N + C_Γ`
  and `1 / (σ - β) ≤ Re (L'/L)(σ, χ) + ½ log N + C_Γ`.

Dropping outside nonnegative zero terms on `σ ∈ [1, 2]` turns upper bounds on `-Re (L'/L)(σ, χ)`
into quantitative bounds on zeros near `Re s = 1` (for zero-free regions and real-zero exclusion).
In `finite_zero_sum_le_logDeriv`, the hypothesis `0 < ρ.re` on `S` restricts to the right
half-plane where `Λ₀` and `χ.LFunction` share the same zero multiplicities, excluding the trivial
Gamma-cancelled zero `L(0, χ) = 0` of even characters while allowing non-zeros in `S` since they
contribute `analyticOrderNatAt χ.LFunction ρ = 0`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §§10.2 and
  11.1–11.2, Theorem 10.16 and Corollary 10.18.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 12 and 14.
-/

public section

open Complex ComplexConjugate
open scoped BigOperators

namespace TauCeti.LFunctions

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

private theorem dirichletData_entireCompletion_zero_ne_zero_all :
    (dirichletData χ hχ).entireCompletion 0 ≠ 0 := by
  by_cases hN : N = 1
  · subst N
    rw [dirichletData_modOne, riemannZetaData_entireCompletion]
    exact zetaEntireCompletion_zero_ne_zero
  · exact dirichletData_entireCompletion_zero_ne_zero χ hχ (mt hχ.eq_one_iff.mp hN)

private theorem dirichletData_entireCompletion_ne_zero_of_one_le_re_all {s : ℂ} (hs : 1 ≤ s.re) :
    (dirichletData χ hχ).entireCompletion s ≠ 0 := by
  by_cases hN : N = 1
  · subst N
    rw [dirichletData_modOne, riemannZetaData_entireCompletion]
    exact zetaEntireCompletion_ne_zero_of_one_le_re hs
  · exact dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ (mt hχ.eq_one_iff.mp hN) hs

private theorem re_le_one_of_dirichletData_entireCompletion_eq_zero_all {ρ : ℂ}
    (hρ : (dirichletData χ hχ).entireCompletion ρ = 0) : ρ.re ≤ 1 := by
  by_cases hN : N = 1
  · subst N
    rw [dirichletData_modOne, riemannZetaData_entireCompletion] at hρ
    exact (re_mem_Ioo_of_zetaEntireCompletion_eq_zero hρ).2.le
  · exact (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ (mt hχ.eq_one_iff.mp hN)
      hρ).2.le

private theorem dirichletData_entireCompletion_one_sub_eq_rootNumber_mul_conj_conj (z : ℂ) :
    (dirichletData χ hχ).entireCompletion (1 - z) =
      χ.rootNumber * conj ((dirichletData χ hχ).entireCompletion (conj z)) := by
  by_cases hN : N = 1
  · subst N
    rw [dirichletData_modOne, riemannZetaData_entireCompletion,
      DirichletCharacter.rootNumber_modOne, one_mul, zetaEntireCompletion_one_sub,
      zetaEntireCompletion_conj, conj_conj]
  · have hne : χ ≠ 1 := mt hχ.eq_one_iff.mp hN
    rw [dirichletData_entireCompletion_one_sub χ hχ hne,
      dirichletData_entireCompletion_inv_conj χ hχ hne]

/-! ### Hadamard factorization and partial-fraction expansion -/

/-- Explicit Hadamard factorization of a primitive Dirichlet entire completion in terms of
`TauCeti.divisorProductOne`. -/
theorem dirichletData_entireCompletion_eq_mul_cexp_logDeriv_mul_divisorProductOne (s : ℂ) :
    (dirichletData χ hχ).entireCompletion s =
      (dirichletData χ hχ).entireCompletion 0 *
        exp (logDeriv (dirichletData χ hχ).entireCompletion 0 * s) *
        divisorProductOne (dirichletData χ hχ).entireCompletion s :=
  (dirichletData_entireCompletion_orderLE_one χ hχ).eq_mul_cexp_logDeriv_mul_divisorProductOne
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero_all χ hχ) s

/-- **Hadamard product for primitive Dirichlet completions.** For every primitive Dirichlet
character `χ`, `(dirichletData χ hχ).entireCompletion` factors globally as `exp (a + b * s)` times
the multipliable genus-one canonical product over its zeros, with
`exp a = (dirichletData χ hχ).entireCompletion 0` and
`b = logDeriv (dirichletData χ hχ).entireCompletion 0`. -/
theorem dirichletData_entireCompletion_hadamard :
    ∃ a b : ℂ, exp a = (dirichletData χ hχ).entireCompletion 0 ∧
      b = logDeriv (dirichletData χ hχ).entireCompletion 0 ∧ ∀ s : ℂ,
      Multipliable (fun ρ : ℂ ↦
        weierstrassFactorOne (ρ⁻¹ * s) ^
          (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat) ∧
      (dirichletData χ hχ).entireCompletion s = exp (a + b * s) * ∏' ρ : ℂ,
        weierstrassFactorOne (ρ⁻¹ * s) ^
          (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat :=
  hadamard_of_orderLE_one
    (dirichletData_entireCompletion_orderLE_one χ hχ)
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero_all χ hχ)

/-- The paired partial-fraction series of a primitive Dirichlet entire completion converges
absolutely at every `s : ℂ`. -/
theorem summable_norm_divisor_dirichletData_entireCompletion_mul_one_div_sub_add_one_div (s : ℂ) :
    Summable
      (fun ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support ↦
        ‖((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℂ) *
          (1 / (s - ρ) + 1 / ρ)‖) :=
  (dirichletData_entireCompletion_orderLE_one χ hχ
    ).summable_norm_divisor_mul_one_div_sub_add_one_div
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion (by norm_num) s

/-- The reciprocal real-part series `∑' ρ, m_ρ * Re (1 / ρ)` over the zeros of a primitive
Dirichlet entire completion is summable. -/
theorem summable_divisor_dirichletData_entireCompletion_toNat_mul_re_one_div :
    Summable
      (fun ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support ↦
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (ρ : ℂ)).re) :=
  (dirichletData_entireCompletion_orderLE_one χ hχ).summable_divisor_toNat_mul_re_one_div_of_re_le
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion (by norm_num)
    (fun _ hρ ↦ re_le_one_of_dirichletData_entireCompletion_eq_zero_all χ hχ hρ)
    (dirichletData_entireCompletion_one_sub_eq_rootNumber_mul_conj_conj χ hχ)

/-- The unsubtracted real-part series `∑' ρ, m_ρ * Re (1 / (s - ρ))` over the zeros of a primitive
Dirichlet entire completion is summable at every `s : ℂ`. -/
theorem summable_divisor_dirichletData_entireCompletion_toNat_mul_re_one_div_sub (s : ℂ) :
    Summable
      (fun ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support ↦
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (s - ρ)).re) :=
  (dirichletData_entireCompletion_orderLE_one χ hχ
    ).summable_divisor_toNat_mul_re_one_div_sub_of_re_le
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion (by norm_num)
    (fun _ hρ ↦ re_le_one_of_dirichletData_entireCompletion_eq_zero_all χ hχ hρ)
    (dirichletData_entireCompletion_one_sub_eq_rootNumber_mul_conj_conj χ hχ) s

/-- Paired partial-fraction expansion of the logarithmic derivative of a primitive Dirichlet entire
completion off its zeros. -/
theorem logDeriv_dirichletData_entireCompletion_eq_add_tsum {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    logDeriv (dirichletData χ hχ).entireCompletion s =
      logDeriv (dirichletData χ hχ).entireCompletion 0 +
        ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
          ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℂ) *
            (1 / (s - ρ) + 1 / ρ) :=
  (dirichletData_entireCompletion_orderLE_one χ hχ).logDeriv_eq_add_tsum
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero_all χ hχ) hs

/-- **Real-part formula for the Hadamard linear constant.** For every primitive Dirichlet character
`χ` (real or complex), the real part of `logDeriv (dirichletData χ hχ).entireCompletion 0` equals
`-∑' ρ, m_ρ * Re (1 / ρ)`. -/
theorem re_logDeriv_dirichletData_entireCompletion_zero :
    (logDeriv (dirichletData χ hχ).entireCompletion 0).re =
      -∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (ρ : ℂ)).re :=
  (dirichletData_entireCompletion_orderLE_one χ hχ).re_logDeriv_zero_eq_neg_tsum
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero_all χ hχ)
    (fun _ hρ ↦ re_le_one_of_dirichletData_entireCompletion_eq_zero_all χ hχ hρ)
    (dirichletData_entireCompletion_one_sub_eq_rootNumber_mul_conj_conj χ hχ)

/-- **Cancelled real-part partial-fraction expansion.** Off the zeros of
`(dirichletData χ hχ).entireCompletion`, its logarithmic derivative has real part
`∑' ρ, m_ρ * Re (1 / (s - ρ))`, with no additive constant. -/
theorem re_logDeriv_dirichletData_entireCompletion_eq_tsum {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    (logDeriv (dirichletData χ hχ).entireCompletion s).re =
      ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (s - ρ)).re :=
  (dirichletData_entireCompletion_orderLE_one χ hχ).re_logDeriv_eq_tsum
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero_all χ hχ)
    (fun _ hρ ↦ re_le_one_of_dirichletData_entireCompletion_eq_zero_all χ hχ hρ)
    (dirichletData_entireCompletion_one_sub_eq_rootNumber_mul_conj_conj χ hχ) hs

/-- On `1 ≤ Re s`, every finite subsum `∑ ρ ∈ S, m_ρ * Re (1 / (s - ρ))` over zeros of a primitive
Dirichlet entire completion is bounded above by
`Re (logDeriv (dirichletData χ hχ).entireCompletion s)`. -/
theorem sum_divisor_dirichletData_entireCompletion_toNat_mul_re_one_div_sub_le_re_logDeriv
    {s : ℂ} (hs : 1 ≤ s.re) (S : Finset ℂ) :
    ∑ ρ ∈ S, ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
      (1 / (s - ρ)).re ≤ (logDeriv (dirichletData χ hχ).entireCompletion s).re :=
  (dirichletData_entireCompletion_orderLE_one χ hχ
    ).sum_divisor_toNat_mul_re_one_div_sub_le_re_logDeriv
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero_all χ hχ)
    (dirichletData_entireCompletion_one_sub_eq_rootNumber_mul_conj_conj χ hχ)
    (dirichletData_entireCompletion_ne_zero_of_one_le_re_all χ hχ hs)
    (fun _ hρ ↦ (re_le_one_of_dirichletData_entireCompletion_eq_zero_all χ hχ hρ).trans hs) S

/-- On `1 ≤ Re s`, the real part of the logarithmic derivative of a primitive Dirichlet entire
completion is nonnegative. -/
theorem re_logDeriv_dirichletData_entireCompletion_nonneg {s : ℂ} (hs : 1 ≤ s.re) :
    0 ≤ (logDeriv (dirichletData χ hχ).entireCompletion s).re := by
  simpa using sum_divisor_dirichletData_entireCompletion_toNat_mul_re_one_div_sub_le_re_logDeriv
    χ hχ hs ∅

/-! ### Retained-zero inequalities -/

include hχ in
/-- **Finite retained-zero inequality.** For any primitive nonprincipal Dirichlet character `χ` of
conductor `N` (real or complex), any finite set `S ⊆ {ρ : ℂ | 0 < ρ.re}`, and any `σ ∈ [1, 2]`,
the multiplicity-weighted sum over `S` satisfies
`∑ ρ ∈ S, analyticOrderNatAt χ.LFunction ρ * Re (1 / (σ - ρ)) ≤`
`Re (L'/L)(σ, χ) + ½ log N + gammaLogDerivBound`. -/
theorem finite_zero_sum_le_logDeriv (hne : χ ≠ 1) (S : Finset ℂ) (hS : ∀ ρ ∈ S, 0 < ρ.re)
    {σ : ℝ} (hσ : σ ∈ Set.Icc 1 2) :
    ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re ≤
      (logDeriv χ.LFunction σ).re + Real.log N / 2 + gammaLogDerivBound := by
  have hσ1 : 1 ≤ (σ : ℂ).re := by simpa using hσ.1
  have hσ0 : 0 < (σ : ℂ).re := zero_lt_one.trans_le hσ1
  have hLσ : χ.LFunction σ ≠ 0 := χ.LFunction_ne_zero_of_one_le_re (.inl hne) hσ1
  have hfin :=
    sum_divisor_dirichletData_entireCompletion_toNat_mul_re_one_div_sub_le_re_logDeriv χ hχ hσ1 S
  have hsum_eq : ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re =
      ∑ ρ ∈ S, ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat :
        ℝ) * (1 / ((σ : ℂ) - ρ)).re := by
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    rw [toNat_divisor_dirichletData_entireCompletion_eq_analyticOrderNatAt χ hχ hne (hS ρ hρ)]
  have hdecomp : (logDeriv (dirichletData χ hχ).entireCompletion σ).re =
      Real.log N / 2 + (logDeriv χ.gammaFactor σ).re + (logDeriv χ.LFunction σ).re := by
    rw [logDeriv_dirichletData_entireCompletion χ hχ hne hσ0 hLσ, add_re, add_re,
      div_ofNat_re, ofReal_re]
  have hgamma : (logDeriv χ.gammaFactor σ).re ≤ gammaLogDerivBound :=
    (le_abs_self _).trans ((abs_re_le_norm _).trans (χ.norm_logDeriv_gammaFactor_ofReal_le hσ))
  linarith

include hχ in
/-- **One-zero inequality.** For any primitive nonprincipal Dirichlet character `χ` of conductor
`N` (real or complex), any real zero `0 < β` of `L(·, χ)`, and any `σ ∈ [1, 2]`,
`1 / (σ - β) ≤ Re (L'/L)(σ, χ) + ½ log N + gammaLogDerivBound`. -/
theorem one_zero_le_logDeriv (hne : χ ≠ 1) {β σ : ℝ} (hβ : 0 < β)
    (hzero : χ.LFunction β = 0) (hσ : σ ∈ Set.Icc 1 2) :
    1 / (σ - β) ≤ (logDeriv χ.LFunction σ).re + Real.log N / 2 + gammaLogDerivBound := by
  have hβre : 0 < ((β : ℂ)).re := by simpa using hβ
  have hΛβ : (dirichletData χ hχ).entireCompletion β = 0 :=
    (dirichletData_entireCompletion_eq_zero_iff χ hχ hne hβre).mpr hzero
  have hβ1 : β < 1 := by
    simpa using (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hne hΛβ).2
  have hσβ : 0 < σ - β := by linarith [hσ.1]
  have hm_pos : 1 ≤ analyticOrderNatAt χ.LFunction β := by
    have haL := (DirichletCharacter.differentiable_LFunction hne).analyticAt (β : ℂ)
    have hne_top : analyticOrderAt χ.LFunction β ≠ ⊤ := by
      rw [← analyticOrderAt_dirichletData_entireCompletion_eq_LFunction χ hχ hne hβre]
      exact analyticOrderAt_dirichletData_entireCompletion_ne_top χ hχ hne β
    rw [Nat.one_le_iff_ne_zero, ← Nat.cast_ne_zero (R := ℕ∞),
      Nat.cast_analyticOrderNatAt hne_top]
    exact haL.analyticOrderAt_ne_zero.mpr hzero
  have hre_sub : (1 / ((σ : ℂ) - (β : ℂ))).re = 1 / (σ - β) := by
    rw [← ofReal_sub, ← ofReal_one, ← ofReal_div, ofReal_re]
  have hsingle := finite_zero_sum_le_logDeriv χ hχ hne {(β : ℂ)}
    (fun ρ hρ ↦ by rw [Finset.mem_singleton.mp hρ]; exact hβre) hσ
  rw [Finset.sum_singleton, hre_sub] at hsingle
  have hmult : 1 * (1 / (σ - β)) ≤
      (analyticOrderNatAt χ.LFunction β : ℝ) * (1 / (σ - β)) := by
    refine mul_le_mul_of_nonneg_right ?_ (div_nonneg zero_le_one hσβ.le)
    exact_mod_cast hm_pos
  linarith

/-! ### Example -/

include hχ in
/-- Specializing `finite_zero_sum_le_logDeriv` to the empty set at `σ = 2` shows that for every
primitive nonprincipal Dirichlet character `χ` modulo `N`,
`0 ≤ Re (L'/L)(2, χ) + ½ log N + gammaLogDerivBound`. -/
example (hne : χ ≠ 1) :
    0 ≤ (logDeriv χ.LFunction 2).re + Real.log N / 2 + gammaLogDerivBound := by
  have h := finite_zero_sum_le_logDeriv χ hχ hne ∅ (by simp) (σ := 2) ⟨by norm_num, le_rfl⟩
  simpa using h

end TauCeti.LFunctions
