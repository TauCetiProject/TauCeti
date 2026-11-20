/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.RealPart
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Basic

/-!
# Real-part Hadamard expansions for completed L-function records

For an `AnalyticLFunctionData` record `d` admitting meromorphic continuation, a functional
equation, growth order at most `1` (or less than `2` for summability alone), and no zeros on the
closed right half-plane `1 ≤ Re s`, all zeros of `d.entireCompletion` lie in the open critical
strip `0 < Re ρ < 1` (`HasFunctionalEquation.re_mem_Ioo_of_entireCompletion_eq_zero`),
`d.entireCompletion 0 ≠ 0`, and `d.entireCompletion` obeys the combined symmetry
`Λ₀(1 - s) = (-1) ^ deg(P_d) * ε * conj (Λ₀(conj s))`.

Specializing `TauCeti.OrderLE` real-part cancellation once at the record level gives:

* `HasFunctionalEquation.summable_divisor_entireCompletion_toNat_mul_re_one_div`,
  `HasFunctionalEquation.summable_divisor_entireCompletion_toNat_mul_re_one_div_sub`: separate
  summability of `m_ρ * Re (1 / ρ)` and `m_ρ * Re (1 / (s - ρ))` for every order below `2`.
* `HasFunctionalEquation.re_logDeriv_entireCompletion_zero`,
  `HasFunctionalEquation.re_logDeriv_entireCompletion_eq_tsum`:
  `Re (logDeriv d.entireCompletion 0) = -∑' ρ, m_ρ * Re (1 / ρ)` and
  `Re (logDeriv d.entireCompletion s) = ∑' ρ, m_ρ * Re (1 / (s - ρ))` away from the zeros.
* `HasFunctionalEquation.sum_divisor_entireCompletion_toNat_mul_re_one_div_sub_le_re_logDeriv`,
  `HasFunctionalEquation.re_logDeriv_entireCompletion_nonneg`: on `1 ≤ Re s`, every finite subsum
  over `S : Finset ℂ` is bounded above by `Re (logDeriv d.entireCompletion s)`, which is
  in particular nonnegative.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Chapters 11–12.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Cambridge University
  Press, 2007, §§10.2 and 11.1.
-/

public section

open Complex
open scoped BigOperators

namespace TauCeti.LFunctions.AnalyticLFunctionData

variable {d : AnalyticLFunctionData}

/-- For a meromorphically continued record with functional equation, growth order below `2`, and
no zeros on `1 ≤ Re s`, the reciprocal real-part series `∑' ρ, m_ρ * Re (1 / ρ)` over the zeros of
`d.entireCompletion` is summable. -/
theorem HasFunctionalEquation.summable_divisor_entireCompletion_toNat_mul_re_one_div
    (hfe : d.HasFunctionalEquation) (h : d.HasMeromorphicContinuation)
    {A : ℝ} (hord : OrderLE d.entireCompletion A) (hA : A < 2)
    (h1 : ∀ z : ℂ, 1 ≤ z.re → d.entireCompletion z ≠ 0) :
    Summable (fun ρ : (MeromorphicOn.divisor d.entireCompletion Set.univ).support ↦
      ((MeromorphicOn.divisor d.entireCompletion Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re) :=
  hord.summable_divisor_toNat_mul_re_one_div_of_re_le h.differentiable_entireCompletion hA
    (fun _ hρ ↦ (hfe.re_mem_Ioo_of_entireCompletion_eq_zero h h1 hρ).2.le)
    (hfe.entireCompletion_one_sub_eq_mul_conj_conj h)

/-- For a meromorphically continued record with functional equation, growth order below `2`, and
no zeros on `1 ≤ Re s`, the unsubtracted real-part series `∑' ρ, m_ρ * Re (1 / (s - ρ))` over the
zeros of `d.entireCompletion` is summable at every `s : ℂ`. -/
theorem HasFunctionalEquation.summable_divisor_entireCompletion_toNat_mul_re_one_div_sub
    (hfe : d.HasFunctionalEquation) (h : d.HasMeromorphicContinuation)
    {A : ℝ} (hord : OrderLE d.entireCompletion A) (hA : A < 2)
    (h1 : ∀ z : ℂ, 1 ≤ z.re → d.entireCompletion z ≠ 0) (s : ℂ) :
    Summable (fun ρ : (MeromorphicOn.divisor d.entireCompletion Set.univ).support ↦
      ((MeromorphicOn.divisor d.entireCompletion Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re) :=
  (hord.summable_divisor_toNat_mul_re_one_div_sub_iff h.differentiable_entireCompletion hA s).mpr
    (hfe.summable_divisor_entireCompletion_toNat_mul_re_one_div h hord hA h1)

/-- **Real-part formula for the Hadamard linear constant of an L-function record.** Under
meromorphic continuation, functional equation, order at most `1`, and nonvanishing on `1 ≤ Re s`,
`Re (logDeriv d.entireCompletion 0) = -∑' ρ, m_ρ * Re (1 / ρ)`. -/
theorem HasFunctionalEquation.re_logDeriv_entireCompletion_zero
    (hfe : d.HasFunctionalEquation) (h : d.HasMeromorphicContinuation)
    (hord : OrderLE d.entireCompletion 1)
    (h1 : ∀ z : ℂ, 1 ≤ z.re → d.entireCompletion z ≠ 0) :
    (logDeriv d.entireCompletion 0).re =
      -∑' ρ : (MeromorphicOn.divisor d.entireCompletion Set.univ).support,
        ((MeromorphicOn.divisor d.entireCompletion Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re :=
  hord.re_logDeriv_zero_eq_neg_tsum h.differentiable_entireCompletion
    (hfe.entireCompletion_ne_zero_of_re_nonpos h h1 (by simp))
    (hfe.summable_divisor_entireCompletion_toNat_mul_re_one_div h hord (by norm_num) h1)
    (hfe.entireCompletion_one_sub_eq_mul_conj_conj h)

/-- **Cancelled real-part partial-fraction expansion of an L-function record.** Under meromorphic
continuation, functional equation, order at most `1`, and nonvanishing on `1 ≤ Re s`, off the
zeros of `d.entireCompletion` one has
`Re (logDeriv d.entireCompletion s) = ∑' ρ, m_ρ * Re (1 / (s - ρ))`. -/
theorem HasFunctionalEquation.re_logDeriv_entireCompletion_eq_tsum
    (hfe : d.HasFunctionalEquation) (h : d.HasMeromorphicContinuation)
    (hord : OrderLE d.entireCompletion 1)
    (h1 : ∀ z : ℂ, 1 ≤ z.re → d.entireCompletion z ≠ 0)
    {s : ℂ} (hs : d.entireCompletion s ≠ 0) :
    (logDeriv d.entireCompletion s).re =
      ∑' ρ : (MeromorphicOn.divisor d.entireCompletion Set.univ).support,
        ((MeromorphicOn.divisor d.entireCompletion Set.univ ρ).toNat : ℝ) * (1 / (s - ρ)).re :=
  hord.re_logDeriv_eq_tsum h.differentiable_entireCompletion
    (hfe.entireCompletion_ne_zero_of_re_nonpos h h1 (by simp))
    (hfe.summable_divisor_entireCompletion_toNat_mul_re_one_div h hord (by norm_num) h1)
    (hfe.entireCompletion_one_sub_eq_mul_conj_conj h) hs

/-- On `1 ≤ Re s`, every finite subsum `∑ ρ ∈ S, m_ρ * Re (1 / (s - ρ))` over zeros of
`d.entireCompletion` is bounded above by `Re (logDeriv d.entireCompletion s)`. -/
theorem HasFunctionalEquation.sum_divisor_entireCompletion_toNat_mul_re_one_div_sub_le_re_logDeriv
    (hfe : d.HasFunctionalEquation) (h : d.HasMeromorphicContinuation)
    (hord : OrderLE d.entireCompletion 1)
    (h1 : ∀ z : ℂ, 1 ≤ z.re → d.entireCompletion z ≠ 0)
    {s : ℂ} (hs : 1 ≤ s.re) (S : Finset ℂ) :
    ∑ ρ ∈ S, ((MeromorphicOn.divisor d.entireCompletion Set.univ ρ).toNat : ℝ) *
      (1 / (s - ρ)).re ≤ (logDeriv d.entireCompletion s).re :=
  hord.sum_divisor_toNat_mul_re_one_div_sub_le_re_logDeriv h.differentiable_entireCompletion
    (hfe.entireCompletion_ne_zero_of_re_nonpos h h1 (by simp))
    (hfe.entireCompletion_one_sub_eq_mul_conj_conj h) (h1 s hs) S
    fun _ _ hρ ↦ (hfe.re_mem_Ioo_of_entireCompletion_eq_zero h h1 hρ).2.le.trans hs

/-- On `1 ≤ Re s`, `Re (logDeriv d.entireCompletion s)` is nonnegative. -/
theorem HasFunctionalEquation.re_logDeriv_entireCompletion_nonneg
    (hfe : d.HasFunctionalEquation) (h : d.HasMeromorphicContinuation)
    (hord : OrderLE d.entireCompletion 1)
    (h1 : ∀ z : ℂ, 1 ≤ z.re → d.entireCompletion z ≠ 0)
    {s : ℂ} (hs : 1 ≤ s.re) :
    0 ≤ (logDeriv d.entireCompletion s).re :=
  hord.re_logDeriv_nonneg h.differentiable_entireCompletion
    (hfe.entireCompletion_ne_zero_of_re_nonpos h h1 (by simp))
    (hfe.entireCompletion_one_sub_eq_mul_conj_conj h) (h1 s hs)
    fun _ hρ ↦ (hfe.re_mem_Ioo_of_entireCompletion_eq_zero h h1 hρ).2.le.trans hs

end TauCeti.LFunctions.AnalyticLFunctionData
