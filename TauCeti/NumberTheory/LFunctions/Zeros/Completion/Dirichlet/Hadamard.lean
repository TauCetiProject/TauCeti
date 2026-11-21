/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.OrderOne
public import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv.Bound
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Basic

import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Growth
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.LogDeriv
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Zeros
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Hadamard
public import TauCeti.Analysis.Complex.Hadamard.RealPart
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Growth
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.LogDeriv
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Zeros

/-!
# Hadamard factorization and retained-zero inequalities for Dirichlet L-functions

Let `χ` be a primitive Dirichlet character modulo `N`, and write
`Λ₀ = (dirichletData χ hχ).entireCompletion`. For `χ ≠ 1`, `Λ₀` has no poles to clear, while at
conductor `N = 1` it recovers `zetaEntireCompletion`. In all cases `Λ₀` satisfies `Λ₀ 0 ≠ 0`, has
growth order at most `1`, has all its zeros inside the open critical strip `0 < Re ρ < 1`, and
obeys the combined functional and conjugation identity `Λ₀ (1 - z) = ε(χ) * conj (Λ₀ (conj z))`.
Specializing `TauCeti.hadamard_of_orderLE_one` and the record-level real-part cancellation theorems
of `TauCeti.NumberTheory.LFunctions.Zeros.Completion.Hadamard` gives:

* **Hadamard factorization** (`dirichletData_entireCompletion_hadamard`): for every primitive `χ`,
  `Λ₀` factors globally as `exp (a + b * s)` times the multipliable genus-one canonical product over
  its zeros.
* **Real-part cancellation** (`re_logDeriv_dirichletData_entireCompletion_zero` and
  `re_logDeriv_dirichletData_entireCompletion_eq_tsum`): for every primitive `χ` (real or complex),
  `(logDeriv Λ₀ 0).re = -∑' ρ, m_ρ * (1 / ρ).re`, so off the zeros one has
  `(logDeriv Λ₀ s).re = ∑' ρ, m_ρ * (1 / (s - ρ)).re` with no additive constant.
* **Retained-zero inequalities** (in `namespace DirichletCharacter`,
  `sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_re_logDeriv_LFunction_add` and
  `one_div_sub_le_re_logDeriv_LFunction_add`): for nonprincipal primitive `χ ≠ 1` and `σ ∈ [1, 2]`,
  every zero summand `m_ρ * Re (1 / (σ - ρ))` is nonnegative and the archimedean logarithmic
  derivative is bounded in norm by `TauCeti.gammaLogDerivBound` (`C_Γ`), so discarding all zeros
  outside a chosen finite set `S` (or keeping a single real zero `0 < β`) yields
  `∑ ρ ∈ S, analyticOrderNatAt χ.LFunction ρ * Re (1 / (σ - ρ)) ≤ Re (L'/L)(σ, χ) + ½ log N + C_Γ`
  and `1 / (σ - β) ≤ Re (L'/L)(σ, χ) + ½ log N + C_Γ`.

Dropping outside nonnegative zero terms on `σ ∈ [1, 2]` turns lower bounds on `-Re (L'/L)(σ, χ)`
(equivalently upper bounds on `Re (L'/L)(σ, χ)`) into quantitative bounds on zeros near `Re s = 1`
(for zero-free regions and real-zero exclusion), and conversely yields upper bounds on
`-Re (L'/L)(σ, χ)` from retained zeros.
In `sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_re_logDeriv_LFunction_add`, the
hypothesis `0 < ρ.re` on `S` restricts to the right half-plane where `Λ₀` and `χ.LFunction` share
the same zero multiplicities, excluding the trivial Gamma-cancelled zero `L(0, χ) = 0` of even
characters while allowing non-zeros in `S` since they contribute
`analyticOrderNatAt χ.LFunction ρ = 0`.

The same cancellation is also stated with the sums over zeros indexed by `ℂ` and weighted by
`analyticOrderNatAt`, which agrees with the multiplicity of `ρ` as a nontrivial zero of Mathlib's
`χ.completedLFunction` (`analyticOrderNatAt_dirichletData_entireCompletion`). For nonprincipal
primitive `χ`, on `0 < Re s` off the zeros of `L(s, χ)`
(`DirichletCharacter.re_logDeriv_LFunction_add_eq_tsum`),
`Re (L'/L(s, χ)) + ½ log N + Re (γ'/γ(s, χ)) = ∑' ρ, m_ρ Re (1 / (s - ρ))`, and
`Re (Λ'/Λ(0, χ)) + ½ log N = -∑' ρ, m_ρ Re (1 / ρ)`
(`DirichletCharacter.re_logDeriv_completedLFunction_zero_add_eq_neg_tsum`). Dropping nonnegative
zero terms on `1 ≤ Re s` keeps the exact archimedean term
(`DirichletCharacter.sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_add_gammaFactor`,
`DirichletCharacter.re_one_div_sub_le_re_logDeriv_LFunction_add_gammaFactor`), and on `σ ∈ [1, 2]`
a single complex zero `ρ` with `0 < Re ρ` gives
`Re (1 / (σ - ρ)) ≤ Re (L'/L)(σ, χ) + ½ log N + C_Γ`
(`DirichletCharacter.re_one_div_sub_le_re_logDeriv_LFunction_add`).

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §§10.2 and
  11.1–11.2, Theorem 10.16 and Corollary 10.18.
* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 12 and 14.
-/

public section

open Complex ComplexConjugate Filter Topology Bornology
open scoped BigOperators

namespace TauCeti.LFunctions

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)

/-! ### Hadamard factorization and real-part cancellation -/

/-- **Hadamard product for primitive Dirichlet completions.** For every primitive Dirichlet
character `χ`, `(dirichletData χ hχ).entireCompletion` factors globally as `exp (a + b * s)` times
the multipliable genus-one canonical product over its zeros, with
`exp a = (dirichletData χ hχ).entireCompletion 0` and
`b = logDeriv (dirichletData χ hχ).entireCompletion 0`. -/
theorem dirichletData_entireCompletion_hadamard :
    ∃ a b : ℂ, exp a = (dirichletData χ hχ).entireCompletion 0 ∧
      b = logDeriv (dirichletData χ hχ).entireCompletion 0 ∧ ∀ s : ℂ,
      Multipliable (fun ρ : ℂ ↦
        weierstrassFactor 1 (ρ⁻¹ * s) ^
          (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat) ∧
      (dirichletData χ hχ).entireCompletion s = exp (a + b * s) * ∏' ρ : ℂ,
        weierstrassFactor 1 (ρ⁻¹ * s) ^
          (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat :=
  hadamard_of_orderLE_one
    (dirichletData_entireCompletion_orderLE_one χ hχ)
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero χ hχ)

/-- **Real-part formula for the Hadamard linear constant.** For every primitive Dirichlet character
`χ` (real or complex), the real part of `logDeriv (dirichletData χ hχ).entireCompletion 0` equals
`-∑' ρ, m_ρ * Re (1 / ρ)`. -/
theorem re_logDeriv_dirichletData_entireCompletion_zero :
    (logDeriv (dirichletData χ hχ).entireCompletion 0).re =
      -∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (ρ : ℂ)).re :=
  (dirichletData_hasFunctionalEquation χ hχ).re_logDeriv_entireCompletion_zero
    (dirichletData_hasMeromorphicContinuation χ hχ)
    (dirichletData_entireCompletion_orderLE_one χ hχ)
    (fun _ ↦ dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ)

/-- **Cancelled real-part partial-fraction expansion.** Off the zeros of
`(dirichletData χ hχ).entireCompletion`, its logarithmic derivative has real part
`∑' ρ, m_ρ * Re (1 / (s - ρ))`, with no additive constant. -/
theorem re_logDeriv_dirichletData_entireCompletion_eq_tsum {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    (logDeriv (dirichletData χ hχ).entireCompletion s).re =
      ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (s - ρ)).re :=
  (dirichletData_hasFunctionalEquation χ hχ).re_logDeriv_entireCompletion_eq_tsum
    (dirichletData_hasMeromorphicContinuation χ hχ)
    (dirichletData_entireCompletion_orderLE_one χ hχ)
    (fun _ ↦ dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ) hs

/-! ### Partial fractions and positivity -/

/-- **Partial fractions.** Off its zeros, the logarithmic derivative of a primitive
Dirichlet entire completion is `B(χ) + ∑_ρ m_ρ (1 / (s - ρ) + 1 / ρ)` with `B(χ) = Λ₀'/Λ₀ (0)`. -/
theorem logDeriv_dirichletData_entireCompletion_eq_add_tsum {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    logDeriv (dirichletData χ hχ).entireCompletion s =
      logDeriv (dirichletData χ hχ).entireCompletion 0 +
        ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
          ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℂ) *
            (1 / (s - ρ) + 1 / ρ) :=
  (dirichletData_entireCompletion_orderLE_one χ hχ).logDeriv_eq_add_tsum
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero χ hχ) hs

/-- The partial-fraction series of a primitive Dirichlet entire completion converges
absolutely. -/
theorem summable_norm_divisor_dirichletData_entireCompletion_mul_one_div_sub_add_one_div
    (s : ℂ) :
    Summable (fun ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion
        Set.univ).support ↦
      ‖((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℂ) *
        (1 / (s - ρ) + 1 / ρ)‖) :=
  OrderLE.summable_norm_divisor_mul_one_div_sub_add_one_div
    (dirichletData_entireCompletion_orderLE_one χ hχ)
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion (by norm_num) s

/-- The partial-fraction series of a primitive Dirichlet entire completion converges
locally uniformly off its zeros to `Λ₀'/Λ₀ - B(χ)`. -/
theorem hasSumLocallyUniformlyOn_logDeriv_dirichletData_entireCompletion_sub :
    HasSumLocallyUniformlyOn
      (fun (ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support)
          s ↦
        ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℂ) *
          (1 / (s - ρ) + 1 / ρ))
      (fun s ↦ logDeriv (dirichletData χ hχ).entireCompletion s -
        logDeriv (dirichletData χ hχ).entireCompletion 0)
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support)ᶜ :=
  (dirichletData_entireCompletion_orderLE_one χ hχ).hasSumLocallyUniformlyOn_logDeriv_sub
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (dirichletData_entireCompletion_zero_ne_zero χ hχ)

/-! ### Real parts of the sum over zeros -/

/-- Every zero of `Λ₀` has `0 ≤ Re ρ`, the zero-location hypothesis of the general real-part
lemmas. -/
private theorem re_nonneg_of_divisor_dirichletData_entireCompletion_pos (ρ : ℂ)
    (hρ : 0 < MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ) :
    0 ≤ ρ.re :=
  (re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hχ hρ).1.le

/-- Every zero of `Λ₀` has `|Re ρ| ≤ 1`. -/
private theorem abs_re_le_one_of_divisor_dirichletData_entireCompletion_pos (ρ : ℂ)
    (hρ : 0 < MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ) :
    |ρ.re| ≤ 1 :=
  have h := re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hχ hρ
  abs_le.mpr ⟨by linarith [h.1], h.2.le⟩

/-- The real parts `m_ρ Re (1 / ρ)` over the zeros form a summable family. -/
theorem summable_divisor_dirichletData_entireCompletion_mul_re_one_div :
    Summable (fun ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion
        Set.univ).support ↦
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
        (1 / (ρ : ℂ)).re) :=
  (dirichletData_entireCompletion_orderLE_one χ hχ).summable_divisor_mul_re_one_div
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion
    (by norm_num) (abs_re_le_one_of_divisor_dirichletData_entireCompletion_pos χ hχ)

/-- The real parts `m_ρ Re (1 / (s - ρ))` form a summable family. The complex terms
`m_ρ / (s - ρ)` are not absolutely summable. -/
theorem summable_divisor_dirichletData_entireCompletion_mul_re_one_div_sub (s : ℂ) :
    Summable (fun ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion
        Set.univ).support ↦
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
        (1 / (s - ρ)).re) :=
  (dirichletData_entireCompletion_orderLE_one χ hχ).summable_divisor_mul_re_one_div_sub
    (dirichletData_hasMeromorphicContinuation χ hχ).differentiable_entireCompletion (by norm_num)
    (abs_re_le_one_of_divisor_dirichletData_entireCompletion_pos χ hχ) s

/-- For `1 ≤ Re s`, each weighted summand `m_ρ Re (1 / (s - ρ))` is nonnegative. -/
theorem divisor_dirichletData_entireCompletion_mul_re_one_div_sub_nonneg {s : ℂ}
    (hs : 1 ≤ s.re) (ρ : ℂ) :
    0 ≤ ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
      (1 / (s - ρ)).re :=
  divisor_mul_re_one_div_sub_nonneg fun hρ ↦
    (re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hχ hρ).2.le.trans hs

/-- For `1 ≤ Re s`, the weighted summand `m_ρ Re (1 / (s - ρ))` at a zero `ρ` is positive, since
`Re ρ < 1 ≤ Re s`. -/
theorem divisor_dirichletData_entireCompletion_mul_re_one_div_sub_pos {s ρ : ℂ}
    (hs : 1 ≤ s.re)
    (hρ : 0 < MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ) :
    0 < ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
      (1 / (s - ρ)).re :=
  divisor_mul_re_one_div_sub_pos hρ
    ((re_mem_Ioo_of_divisor_dirichletData_entireCompletion_pos χ hχ hρ).2.trans_le hs)

/-- **Positivity of the sum over zeros.** For `1 ≤ Re s`, `0 ≤ ∑_ρ m_ρ Re (1 / (s - ρ))`, an
absolutely convergent sum of nonnegative terms. -/
theorem tsum_divisor_dirichletData_entireCompletion_mul_re_one_div_sub_nonneg
    {s : ℂ} (hs : 1 ≤ s.re) :
    0 ≤ ∑' ρ : (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support,
      ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat : ℝ) *
        (1 / (s - ρ)).re :=
  tsum_nonneg fun ρ ↦
    divisor_dirichletData_entireCompletion_mul_re_one_div_sub_nonneg χ hχ hs ρ

/-- For `1 ≤ Re s`, the real part of `Λ₀'/Λ₀ (s)` is nonnegative. -/
theorem re_logDeriv_dirichletData_entireCompletion_nonneg {s : ℂ}
    (hs : 1 ≤ s.re) : 0 ≤ (logDeriv (dirichletData χ hχ).entireCompletion s).re := by
  rw [re_logDeriv_dirichletData_entireCompletion_eq_tsum χ hχ
    (dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hs)]
  exact tsum_divisor_dirichletData_entireCompletion_mul_re_one_div_sub_nonneg χ hχ hs

/-! ### Sums over zeros weighted by natural multiplicities -/

/-- The zeros of a primitive Dirichlet entire completion have bounded real parts. -/
theorem isBounded_re_divisor_support_dirichletData_entireCompletion :
    IsBounded (Complex.re ''
      (MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ).support) :=
  (dirichletData_hasFunctionalEquation χ hχ).isBounded_re_divisor_support_entireCompletion
    (dirichletData_hasMeromorphicContinuation χ hχ) (B := 1) fun _ hρ ↦
      (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hρ).2.le

/-- Absolute summability of `(analyticOrderNatAt Λ₀ ρ) * Re (1 / (s - ρ))` over `ℂ` for a
primitive Dirichlet entire completion. -/
theorem summable_norm_analyticOrderNatAt_dirichletData_entireCompletion_mul_re_one_div_sub
    (s : ℂ) :
    Summable (fun ρ : ℂ ↦
      ‖(analyticOrderNatAt (dirichletData χ hχ).entireCompletion ρ : ℝ) * (1 / (s - ρ)).re‖) :=
  (dirichletData_hasMeromorphicContinuation χ hχ
    ).summable_norm_analyticOrderNatAt_entireCompletion_mul_re_one_div_sub
    (dirichletData_entireCompletion_orderLE_one χ hχ) (by norm_num)
    (isBounded_re_divisor_support_dirichletData_entireCompletion χ hχ) s

/-- Signed summability of `(analyticOrderNatAt Λ₀ ρ) * Re (1 / (s - ρ))` over `ℂ` for a primitive
Dirichlet entire completion. -/
theorem summable_analyticOrderNatAt_dirichletData_entireCompletion_mul_re_one_div_sub (s : ℂ) :
    Summable (fun ρ : ℂ ↦
      (analyticOrderNatAt (dirichletData χ hχ).entireCompletion ρ : ℝ) * (1 / (s - ρ)).re) :=
  (summable_norm_analyticOrderNatAt_dirichletData_entireCompletion_mul_re_one_div_sub χ hχ
    s).of_norm

/-- Absolute summability of `(analyticOrderNatAt Λ₀ ρ) * Re (1 / ρ)` over `ℂ` for a primitive
Dirichlet entire completion. -/
theorem summable_norm_analyticOrderNatAt_dirichletData_entireCompletion_mul_re_one_div :
    Summable (fun ρ : ℂ ↦
      ‖(analyticOrderNatAt (dirichletData χ hχ).entireCompletion ρ : ℝ) * (1 / ρ).re‖) :=
  (dirichletData_hasMeromorphicContinuation χ hχ
    ).summable_norm_analyticOrderNatAt_entireCompletion_mul_re_one_div
    (dirichletData_entireCompletion_orderLE_one χ hχ) (by norm_num)
    (isBounded_re_divisor_support_dirichletData_entireCompletion χ hχ)

/-- Signed summability of `(analyticOrderNatAt Λ₀ ρ) * Re (1 / ρ)` over `ℂ` for a primitive
Dirichlet entire completion. -/
theorem summable_analyticOrderNatAt_dirichletData_entireCompletion_mul_re_one_div :
    Summable (fun ρ : ℂ ↦
      (analyticOrderNatAt (dirichletData χ hχ).entireCompletion ρ : ℝ) * (1 / ρ).re) :=
  (summable_norm_analyticOrderNatAt_dirichletData_entireCompletion_mul_re_one_div χ hχ).of_norm

/-- **Unpaired real-part partial fractions over `ℂ`.** Off the zeros of `Λ₀(s, χ)`,
`(logDeriv Λ₀ s).re = ∑' ρ : ℂ, m_ρ Re (1 / (s - ρ))` with `m_ρ = analyticOrderNatAt Λ₀ ρ`. -/
theorem re_logDeriv_dirichletData_entireCompletion {s : ℂ}
    (hs : (dirichletData χ hχ).entireCompletion s ≠ 0) :
    (logDeriv (dirichletData χ hχ).entireCompletion s).re =
      ∑' ρ : ℂ,
        (analyticOrderNatAt (dirichletData χ hχ).entireCompletion ρ : ℝ) * (1 / (s - ρ)).re :=
  (dirichletData_hasFunctionalEquation χ hχ).re_logDeriv_entireCompletion
    (dirichletData_hasMeromorphicContinuation χ hχ)
    (dirichletData_entireCompletion_orderLE_one χ hχ)
    (dirichletData_entireCompletion_zero_ne_zero χ hχ)
    (isBounded_re_divisor_support_dirichletData_entireCompletion χ hχ) hs

/-- On `1 ≤ Re s`, any finite sum of zero terms of a primitive Dirichlet entire completion is
bounded by `(logDeriv Λ₀ s).re`. -/
theorem sum_analyticOrderNatAt_dirichletData_entireCompletion_mul_re_one_div_sub_le
    {s : ℂ} (hs : 1 ≤ s.re) (S : Finset ℂ) :
    (∑ ρ ∈ S,
        (analyticOrderNatAt (dirichletData χ hχ).entireCompletion ρ : ℝ) * (1 / (s - ρ)).re) ≤
      (logDeriv (dirichletData χ hχ).entireCompletion s).re :=
  (dirichletData_hasFunctionalEquation χ hχ
    ).sum_analyticOrderNatAt_entireCompletion_mul_re_one_div_sub_le
    (dirichletData_hasMeromorphicContinuation χ hχ)
    (dirichletData_entireCompletion_orderLE_one χ hχ)
    (dirichletData_entireCompletion_zero_ne_zero χ hχ)
    (dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hs)
    (fun _ hρ ↦ (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hρ).2.le.trans hs) S

/-- On `1 ≤ Re s`, every zero `ρ` of a primitive Dirichlet entire completion satisfies
`Re (1 / (s - ρ)) ≤ (logDeriv Λ₀ s).re`. -/
theorem re_one_div_sub_le_re_logDeriv_dirichletData_entireCompletion
    {ρ : ℂ} (hρ : (dirichletData χ hχ).entireCompletion ρ = 0) {s : ℂ} (hs : 1 ≤ s.re) :
    (1 / (s - ρ)).re ≤ (logDeriv (dirichletData χ hχ).entireCompletion s).re :=
  (dirichletData_hasFunctionalEquation χ hχ).re_one_div_sub_le_re_logDeriv_entireCompletion
    (dirichletData_hasMeromorphicContinuation χ hχ)
    (dirichletData_entireCompletion_orderLE_one χ hχ)
    (dirichletData_entireCompletion_zero_ne_zero χ hχ)
    (dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ hs)
    (fun _ hz ↦ (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hz).2.le.trans hs)
    hρ

end TauCeti.LFunctions

/-! ### Retained-zero inequalities -/

namespace DirichletCharacter

open TauCeti.LFunctions

/-- **Finite retained-zero inequality.** For any primitive nonprincipal Dirichlet character `χ` of
conductor `N` (real or complex), any finite set `S ⊆ {ρ : ℂ | 0 < ρ.re}`, and any `σ ∈ [1, 2]`,
the multiplicity-weighted sum over `S` satisfies
`∑ ρ ∈ S, analyticOrderNatAt χ.LFunction ρ * Re (1 / (σ - ρ)) ≤`
`Re (L'/L)(σ, χ) + ½ log N + TauCeti.gammaLogDerivBound`. -/
theorem sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_re_logDeriv_LFunction_add
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, 0 < ρ.re) {σ : ℝ} (hσ : σ ∈ Set.Icc 1 2) :
    ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re ≤
      (logDeriv χ.LFunction σ).re + Real.log N / 2 + TauCeti.gammaLogDerivBound := by
  have hσ1 : 1 ≤ (σ : ℂ).re := by simpa using hσ.1
  have hσ0 : 0 < (σ : ℂ).re := zero_lt_one.trans_le hσ1
  have hLσ : χ.LFunction σ ≠ 0 := χ.LFunction_ne_zero_of_one_le_re (.inl hne) hσ1
  have hfin :=
    (dirichletData_hasFunctionalEquation χ hχ
      ).sum_divisor_entireCompletion_toNat_mul_re_one_div_sub_le_re_logDeriv
      (dirichletData_hasMeromorphicContinuation χ hχ)
      (dirichletData_entireCompletion_orderLE_one χ hχ)
      (fun _ ↦ dirichletData_entireCompletion_ne_zero_of_one_le_re χ hχ) hσ1 S
  have hsum_eq : ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re =
      ∑ ρ ∈ S, ((MeromorphicOn.divisor (dirichletData χ hχ).entireCompletion Set.univ ρ).toNat :
        ℝ) * (1 / ((σ : ℂ) - ρ)).re := by
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    rw [toNat_divisor_dirichletData_entireCompletion_eq_analyticOrderNatAt χ hχ hne (hS ρ hρ)]
  have hdecomp : (logDeriv (dirichletData χ hχ).entireCompletion σ).re =
      Real.log N / 2 + (logDeriv χ.gammaFactor σ).re + (logDeriv χ.LFunction σ).re := by
    rw [logDeriv_dirichletData_entireCompletion χ hχ hne hσ0 hLσ, add_re, add_re,
      div_ofNat_re, ofReal_re]
  have hgamma : (logDeriv χ.gammaFactor σ).re ≤ TauCeti.gammaLogDerivBound :=
    (le_abs_self _).trans ((abs_re_le_norm _).trans (χ.norm_logDeriv_gammaFactor_ofReal_le hσ))
  linarith

/-- **One-zero inequality.** For any primitive nonprincipal Dirichlet character `χ` of conductor
`N` (real or complex), any real zero `0 < β` of `L(·, χ)`, and any `σ ∈ [1, 2]`,
`1 / (σ - β) ≤ Re (L'/L)(σ, χ) + ½ log N + TauCeti.gammaLogDerivBound`. -/
theorem one_div_sub_le_re_logDeriv_LFunction_add {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {β σ : ℝ} (hβ : 0 < β) (hzero : χ.LFunction β = 0)
    (hσ : σ ∈ Set.Icc 1 2) :
    1 / (σ - β) ≤ (logDeriv χ.LFunction σ).re + Real.log N / 2 + TauCeti.gammaLogDerivBound := by
  have hβre : 0 < ((β : ℂ)).re := by simpa using hβ
  have hΛβ : (dirichletData χ hχ).entireCompletion β = 0 :=
    (dirichletData_entireCompletion_eq_zero_iff χ hχ hne hβre).mpr hzero
  have hβ1 : β < 1 := by
    simpa using (re_mem_Ioo_of_dirichletData_entireCompletion_eq_zero χ hχ hΛβ).2
  have hσβ : 0 < σ - β := by linarith [hσ.1]
  have hm_pos : 1 ≤ analyticOrderNatAt χ.LFunction β := by
    have haL := (DirichletCharacter.differentiable_LFunction hne).analyticAt (β : ℂ)
    have hne_top : analyticOrderAt χ.LFunction β ≠ ⊤ := by
      rw [← analyticOrderAt_dirichletData_entireCompletion_eq_LFunction χ hχ hne hβre]
      exact analyticOrderAt_dirichletData_entireCompletion_ne_top χ hχ β
    rw [Nat.one_le_iff_ne_zero, ← Nat.cast_ne_zero (R := ℕ∞),
      Nat.cast_analyticOrderNatAt hne_top]
    exact haL.analyticOrderAt_ne_zero.mpr hzero
  have hre_sub : (1 / ((σ : ℂ) - (β : ℂ))).re = 1 / (σ - β) := by
    rw [← ofReal_sub, ← ofReal_one, ← ofReal_div, ofReal_re]
  have hsingle :=
    χ.sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_re_logDeriv_LFunction_add hχ hne
      {(β : ℂ)} (fun ρ hρ ↦ by rw [Finset.mem_singleton.mp hρ]; exact hβre) hσ
  rw [Finset.sum_singleton, hre_sub] at hsingle
  have hmult : 1 * (1 / (σ - β)) ≤
      (analyticOrderNatAt χ.LFunction β : ℝ) * (1 / (σ - β)) := by
    refine mul_le_mul_of_nonneg_right ?_ (div_nonneg zero_le_one hσβ.le)
    exact_mod_cast hm_pos
  linarith

/-! ### Formulas in terms of `DirichletCharacter.LFunction` -/

section Formulas

variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

/-- Absolute summability of `(analyticOrderNatAt χ.completedLFunction ρ) * Re (1 / (s - ρ))` over
`ℂ` for a nonprincipal primitive character `χ`. -/
theorem summable_norm_analyticOrderNatAt_completedLFunction_mul_re_one_div_sub
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ) :
    Summable (fun ρ : ℂ ↦
      ‖(analyticOrderNatAt χ.completedLFunction ρ : ℝ) * (1 / (s - ρ)).re‖) := by
  simpa only [analyticOrderNatAt_dirichletData_entireCompletion χ hχ hne] using
    summable_norm_analyticOrderNatAt_dirichletData_entireCompletion_mul_re_one_div_sub χ hχ s

/-- Signed summability of `(analyticOrderNatAt χ.completedLFunction ρ) * Re (1 / (s - ρ))` over `ℂ`
for a nonprincipal primitive character `χ`. -/
theorem summable_analyticOrderNatAt_completedLFunction_mul_re_one_div_sub
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ) :
    Summable (fun ρ : ℂ ↦
      (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * (1 / (s - ρ)).re) :=
  (χ.summable_norm_analyticOrderNatAt_completedLFunction_mul_re_one_div_sub hχ hne s).of_norm

/-- Absolute summability of `(analyticOrderNatAt χ.completedLFunction ρ) * Re (1 / ρ)` over `ℂ` for
a nonprincipal primitive character `χ`. -/
theorem summable_norm_analyticOrderNatAt_completedLFunction_mul_re_one_div
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    Summable (fun ρ : ℂ ↦ ‖(analyticOrderNatAt χ.completedLFunction ρ : ℝ) * (1 / ρ).re‖) := by
  simpa only [analyticOrderNatAt_dirichletData_entireCompletion χ hχ hne] using
    summable_norm_analyticOrderNatAt_dirichletData_entireCompletion_mul_re_one_div χ hχ

/-- Signed summability of `(analyticOrderNatAt χ.completedLFunction ρ) * Re (1 / ρ)` over `ℂ` for a
nonprincipal primitive character `χ`. -/
theorem summable_analyticOrderNatAt_completedLFunction_mul_re_one_div
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * (1 / ρ).re) :=
  (χ.summable_norm_analyticOrderNatAt_completedLFunction_mul_re_one_div hχ hne).of_norm

/-- **Real part of the Hadamard constant for Mathlib's completed Dirichlet L-function.** For a
nonprincipal primitive character `χ` modulo `N`,
`Re (logDeriv χ.completedLFunction 0) + ½ log N = -∑' ρ, m_ρ Re (1 / ρ)`. -/
theorem re_logDeriv_completedLFunction_zero_add_eq_neg_tsum (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    (logDeriv χ.completedLFunction 0).re + Real.log N / 2 =
      -∑' ρ : ℂ, (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * (1 / ρ).re := by
  have h0 : χ.completedLFunction 0 ≠ 0 := by
    have hΛ := dirichletData_entireCompletion_zero_ne_zero χ hχ
    rw [dirichletData_entireCompletion_eq χ hχ hne] at hΛ
    exact right_ne_zero_of_mul hΛ
  have hzero := (dirichletData_hasFunctionalEquation χ hχ
    ).re_logDeriv_entireCompletion_zero_of_isBounded
    (dirichletData_hasMeromorphicContinuation χ hχ)
    (dirichletData_entireCompletion_orderLE_one χ hχ)
    (dirichletData_entireCompletion_zero_ne_zero χ hχ)
    (isBounded_re_divisor_support_dirichletData_entireCompletion χ hχ)
  have hlog := congrArg Complex.re
    (logDeriv_dirichletData_entireCompletion_eq_completed χ hχ hne h0)
  rw [add_re, div_ofNat_re, ofReal_re, hzero] at hlog
  simp_rw [← analyticOrderNatAt_dirichletData_entireCompletion χ hχ hne]
  linarith

/-- **Unpaired real-part partial fractions for `DirichletCharacter.LFunction`.** For a nonprincipal
primitive character `χ` modulo `N`, on `0 < Re s` away from the zeros of `L(s, χ)`,
`Re (L'/L(s, χ)) + ½ log N + Re (γ'/γ(s, χ)) = ∑' ρ, m_ρ Re (1 / (s - ρ))`, where `m_ρ` is the
multiplicity of `ρ` as a nontrivial zero (`analyticOrderNatAt χ.completedLFunction ρ`). -/
theorem re_logDeriv_LFunction_add_eq_tsum (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) (hL : χ.LFunction s ≠ 0) :
    (logDeriv χ.LFunction s).re + Real.log N / 2 + (logDeriv χ.gammaFactor s).re =
      ∑' ρ : ℂ, (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * (1 / (s - ρ)).re := by
  have hΛ : (dirichletData χ hχ).entireCompletion s ≠ 0 :=
    (dirichletData_entireCompletion_eq_zero_iff χ hχ hne hs).not.mpr hL
  have hlog := congrArg Complex.re (logDeriv_dirichletData_entireCompletion χ hχ hne hs hL)
  rw [add_re, add_re, div_ofNat_re, ofReal_re,
    re_logDeriv_dirichletData_entireCompletion χ hχ hΛ] at hlog
  simp_rw [← analyticOrderNatAt_dirichletData_entireCompletion χ hχ hne]
  linarith

/-- **Retained finite zero sum on `1 ≤ Re s`.** For a nonprincipal primitive character `χ` modulo
`N`, any finite set `S` in the open right half-plane `0 < Re ρ`, and any `s` with `1 ≤ Re s`, the
finite sum of `m_ρ Re (1 / (s - ρ))` weighted by the analytic multiplicities of `χ.LFunction` is
bounded by `Re (L'/L(s, χ)) + ½ log N + Re (γ'/γ(s, χ))`. -/
theorem sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_add_gammaFactor
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {S : Finset ℂ} (hS : ∀ ρ ∈ S, 0 < ρ.re)
    {s : ℂ} (hs : 1 ≤ s.re) :
    (∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / (s - ρ)).re) ≤
      (logDeriv χ.LFunction s).re + Real.log N / 2 + (logDeriv χ.gammaFactor s).re := by
  have hspos : 0 < s.re := by linarith
  have hL : χ.LFunction s ≠ 0 := χ.LFunction_ne_zero_of_one_le_re (.inl hne) hs
  have hsum : (∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / (s - ρ)).re) =
      ∑ ρ ∈ S,
        (analyticOrderNatAt (dirichletData χ hχ).entireCompletion ρ : ℝ) * (1 / (s - ρ)).re := by
    refine Finset.sum_congr rfl fun ρ hρ ↦ ?_
    rw [analyticOrderNatAt_dirichletData_entireCompletion_eq_LFunction χ hχ hne (hS ρ hρ)]
  have hlog := congrArg Complex.re (logDeriv_dirichletData_entireCompletion χ hχ hne hspos hL)
  rw [add_re, add_re, div_ofNat_re, ofReal_re] at hlog
  have hle := sum_analyticOrderNatAt_dirichletData_entireCompletion_mul_re_one_div_sub_le χ hχ
    hs S
  linarith

/-- **Single-zero lower bound on `1 ≤ Re s`.** For a nonprincipal primitive character `χ` modulo
`N`, if `ρ` is a zero of `χ.LFunction` with `0 < Re ρ` and `1 ≤ Re s`, then
`Re (1 / (s - ρ)) ≤ Re (L'/L(s, χ)) + ½ log N + Re (γ'/γ(s, χ))`. -/
theorem re_one_div_sub_le_re_logDeriv_LFunction_add_gammaFactor (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hz : χ.LFunction ρ = 0) {s : ℂ} (hs : 1 ≤ s.re) :
    (1 / (s - ρ)).re ≤
      (logDeriv χ.LFunction s).re + Real.log N / 2 + (logDeriv χ.gammaFactor s).re := by
  have hspos : 0 < s.re := by linarith
  have hL : χ.LFunction s ≠ 0 := χ.LFunction_ne_zero_of_one_le_re (.inl hne) hs
  have hΛ0 : (dirichletData χ hχ).entireCompletion ρ = 0 :=
    (dirichletData_entireCompletion_eq_zero_iff χ hχ hne hρ).mpr hz
  have hle := re_one_div_sub_le_re_logDeriv_dirichletData_entireCompletion χ hχ hΛ0 hs
  have hlog := congrArg Complex.re (logDeriv_dirichletData_entireCompletion χ hχ hne hspos hL)
  rw [add_re, add_re, div_ofNat_re, ofReal_re] at hlog
  linarith

/-- **Single complex zero lower bound on `[1, 2]`.** For a nonprincipal primitive character `χ`
modulo `N`, if `ρ` is a zero of `χ.LFunction` with `0 < Re ρ` and `σ ∈ [1, 2]`, then
`Re (1 / (σ - ρ)) ≤ Re (L'/L(σ, χ)) + ½ log N + TauCeti.gammaLogDerivBound`. -/
theorem re_one_div_sub_le_re_logDeriv_LFunction_add (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hz : χ.LFunction ρ = 0) {σ : ℝ} (hσ : σ ∈ Set.Icc 1 2) :
    (1 / ((σ : ℂ) - ρ)).re ≤
      (logDeriv χ.LFunction σ).re + Real.log N / 2 + TauCeti.gammaLogDerivBound := by
  have hle := χ.re_one_div_sub_le_re_logDeriv_LFunction_add_gammaFactor hχ hne hρ hz
    (s := (σ : ℂ)) (by simpa using hσ.1)
  have hγ : (logDeriv χ.gammaFactor (σ : ℂ)).re ≤ TauCeti.gammaLogDerivBound :=
    (re_le_norm _).trans (χ.norm_logDeriv_gammaFactor_ofReal_le hσ)
  linarith

end Formulas

/-! ### Examples -/

/-- Specializing `sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_re_logDeriv_LFunction_add`
to the empty set at `σ = 2` shows that for every primitive nonprincipal Dirichlet character `χ`
modulo `N`, `0 ≤ Re (L'/L)(2, χ) + ½ log N + TauCeti.gammaLogDerivBound`. -/
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hne : χ ≠ 1) :
    0 ≤ (logDeriv χ.LFunction 2).re + Real.log N / 2 + TauCeti.gammaLogDerivBound := by
  have h := χ.sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_re_logDeriv_LFunction_add hχ
    hne ∅ (by simp) (σ := 2) ⟨by norm_num, le_rfl⟩
  simpa using h

/-- The retained zero-sum bound specializes directly when `S` consists of nontrivial zeros in the
open critical strip and `1 < σ ≤ 2`. -/
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, (0 < ρ.re ∧ ρ.re < 1) ∧ χ.LFunction ρ = 0)
    {σ : ℝ} (hσ₁ : 1 < σ) (hσ₂ : σ ≤ 2) :
    ∑ ρ ∈ S, (analyticOrderNatAt χ.LFunction ρ : ℝ) * (1 / ((σ : ℂ) - ρ)).re ≤
      (logDeriv χ.LFunction σ).re + Real.log N / 2 + TauCeti.gammaLogDerivBound :=
  χ.sum_analyticOrderNatAt_LFunction_mul_re_one_div_sub_le_re_logDeriv_LFunction_add hχ hne S
    (fun ρ hρ ↦ (hS ρ hρ).1.1) ⟨hσ₁.le, hσ₂⟩

/-- Every nonprincipal Dirichlet character has modulus `N ≥ 3`, so `Real.log N / 2 > 0` in the
retained-zero inequalities (moduli `1` and `2` admit only the principal character). -/
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hne : χ ≠ 1) :
    3 ≤ N ∧ 0 < Real.log N / 2 := by
  have hN3 : 3 ≤ N := by
    by_contra hlt
    have hpos : 0 < N := NeZero.pos N
    interval_cases N
    · exact hne <| MulChar.ext fun u ↦ by
        rw [(by decide : ∀ u : (ZMod 1)ˣ, (u : ZMod 1) = 1) u]
        simp
    · exact hne <| MulChar.ext fun u ↦ by
        rw [(by decide : ∀ u : (ZMod 2)ˣ, (u : ZMod 2) = 1) u]
        simp
  refine ⟨hN3, div_pos (Real.log_pos ?_) two_pos⟩
  exact_mod_cast (by omega : 1 < N)

/-- Sign check on a complex critical-strip summand: at `s = 2` and `ρ = 1/2 + 14i`, the retained
partial-fraction term `(1 / (2 - ρ)).re` is strictly positive. -/
example : 0 < (1 / ((2 : ℂ) - (1 / 2 + 14 * I))).re := by
  rw [one_div, Complex.inv_re_pos]
  simp
  norm_num

end DirichletCharacter
