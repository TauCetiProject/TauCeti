/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.RealPart
public import TauCeti.Analysis.Complex.Hadamard.VerticalStrip
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.Divisor

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

Without assuming nonvanishing on `1 ≤ Re s`, the vertical-strip theorems of
`TauCeti.Analysis.Complex.Hadamard.VerticalStrip` give the same cancellation in terms of the natural
zero multiplicities `analyticOrderNatAt d.entireCompletion` (which agree with
`(MeromorphicOn.divisor d.completed Set.univ ·).toNat` by
`HasMeromorphicContinuation.analyticOrderNatAt_entireCompletion_eq_toNat_divisor_completed`),
assuming only `d.entireCompletion 0 ≠ 0` and zeros of bounded real part. Here the functional
equation gives `(logDeriv d.entireCompletion 1).re = -(logDeriv d.entireCompletion 0).re` whether or
not `d` has poles, and every upper bound `Re ρ ≤ B` on the zeros yields `1 - B ≤ Re ρ` by
reflection:

* `HasMeromorphicContinuation.summable_norm_analyticOrderNatAt_entireCompletion_mul_re_one_div_sub`,
  `HasMeromorphicContinuation.summable_analyticOrderNatAt_entireCompletion_mul_re_one_div_sub`,
  `HasMeromorphicContinuation.summable_norm_analyticOrderNatAt_entireCompletion_mul_re_one_div`,
  and `HasMeromorphicContinuation.summable_analyticOrderNatAt_entireCompletion_mul_re_one_div`:
  absolute and signed convergence of the real-part zero series below order two.
* `HasFunctionalEquation.isBounded_re_divisor_support_entireCompletion`: strip boundedness of the
  zeros from any one-sided upper bound `Re ρ ≤ B`.
* `HasFunctionalEquation.re_logDeriv_entireCompletion_zero_of_isBounded` and
  `HasFunctionalEquation.re_logDeriv_entireCompletion`: real-part formula for the Hadamard constant
  and unpaired real-part partial-fraction expansion of `Λ₀'/Λ₀`.
* `HasFunctionalEquation.re_logDeriv_entireCompletion_nonneg_of_zero_ne_zero`,
  `HasFunctionalEquation.sum_analyticOrderNatAt_entireCompletion_mul_re_one_div_sub_le`, and
  `HasFunctionalEquation.re_one_div_sub_le_re_logDeriv_entireCompletion`: positivity, finite-subset
  lower bounds, and single-zero lower bounds to the right of all zeros.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., GTM 74, Chapters 11–12.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Cambridge University
  Press, 2007, §§10.2 and 11.1, Theorem 10.16 and Corollary 10.18.
-/

public section

open Complex ComplexConjugate Filter Topology Bornology
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

section VerticalStrip

variable (h : d.HasMeromorphicContinuation)
include h

/-! ### Absolute and signed summability of real-part zero series -/

namespace HasMeromorphicContinuation

/-- When `d.entireCompletion` has order strictly below two and zeros of bounded real part, the real
parts `(analyticOrderNatAt d.entireCompletion ρ : ℝ) * (1 / (z - ρ)).re` are absolutely summable
over `ℂ` for every `z`. -/
theorem summable_norm_analyticOrderNatAt_entireCompletion_mul_re_one_div_sub
    {A : ℝ} (hord : OrderLE d.entireCompletion A) (hA : A < 2)
    (hre : IsBounded (Complex.re '' (MeromorphicOn.divisor d.entireCompletion Set.univ).support))
    (z : ℂ) :
    Summable (fun ρ : ℂ ↦
      ‖(analyticOrderNatAt d.entireCompletion ρ : ℝ) * (1 / (z - ρ)).re‖) :=
  hord.summable_norm_analyticOrderNatAt_mul_re_one_div_sub h.differentiable_entireCompletion hA
    hre z

/-- Signed summability companion to
`HasMeromorphicContinuation.summable_norm_analyticOrderNatAt_entireCompletion_mul_re_one_div_sub`.
-/
theorem summable_analyticOrderNatAt_entireCompletion_mul_re_one_div_sub
    {A : ℝ} (hord : OrderLE d.entireCompletion A) (hA : A < 2)
    (hre : IsBounded (Complex.re '' (MeromorphicOn.divisor d.entireCompletion Set.univ).support))
    (z : ℂ) :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt d.entireCompletion ρ : ℝ) * (1 / (z - ρ)).re) :=
  (h.summable_norm_analyticOrderNatAt_entireCompletion_mul_re_one_div_sub hord hA hre z).of_norm

/-- When `d.entireCompletion` has order strictly below two and zeros of bounded real part, the
reciprocal real parts `(analyticOrderNatAt d.entireCompletion ρ : ℝ) * (1 / ρ).re` are absolutely
summable over `ℂ`. -/
theorem summable_norm_analyticOrderNatAt_entireCompletion_mul_re_one_div
    {A : ℝ} (hord : OrderLE d.entireCompletion A) (hA : A < 2)
    (hre : IsBounded (Complex.re '' (MeromorphicOn.divisor d.entireCompletion Set.univ).support)) :
    Summable (fun ρ : ℂ ↦ ‖(analyticOrderNatAt d.entireCompletion ρ : ℝ) * (1 / ρ).re‖) :=
  hord.summable_norm_analyticOrderNatAt_mul_re_one_div h.differentiable_entireCompletion hA hre

/-- Signed summability companion to
`HasMeromorphicContinuation.summable_norm_analyticOrderNatAt_entireCompletion_mul_re_one_div`. -/
theorem summable_analyticOrderNatAt_entireCompletion_mul_re_one_div
    {A : ℝ} (hord : OrderLE d.entireCompletion A) (hA : A < 2)
    (hre : IsBounded (Complex.re '' (MeromorphicOn.divisor d.entireCompletion Set.univ).support)) :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt d.entireCompletion ρ : ℝ) * (1 / ρ).re) :=
  (h.summable_norm_analyticOrderNatAt_entireCompletion_mul_re_one_div hord hA hre).of_norm

end HasMeromorphicContinuation

/-! ### Order-one real-part partial fractions for completed L-functions -/

/-- Under a functional equation, any upper bound `ρ.re ≤ B` on the zeros of `d.entireCompletion`
confines the real parts of all zeros to `[1 - B, B]` and hence bounds the real parts of its divisor
support. -/
theorem HasFunctionalEquation.isBounded_re_divisor_support_entireCompletion
    (hfe : d.HasFunctionalEquation) {B : ℝ}
    (hB : ∀ ρ, d.entireCompletion ρ = 0 → ρ.re ≤ B) :
    IsBounded (Complex.re '' (MeromorphicOn.divisor d.entireCompletion Set.univ).support) :=
  h.differentiable_entireCompletion.isBounded_re_divisor_support_of_le (a := 1)
    (by simpa using hfe.analyticOrderNatAt_entireCompletion_one_sub_conj h) hB

/-- **Real part of the Hadamard constant.** For an order-one record with functional equation,
`d.entireCompletion 0 ≠ 0`, and zeros of bounded real part,
`(logDeriv d.entireCompletion 0).re = -∑' ρ, m_ρ (1 / ρ).re`. -/
theorem HasFunctionalEquation.re_logDeriv_entireCompletion_zero_of_isBounded
    (hfe : d.HasFunctionalEquation)
    (hord : OrderLE d.entireCompletion 1) (h0 : d.entireCompletion 0 ≠ 0)
    (hre : IsBounded (Complex.re '' (MeromorphicOn.divisor d.entireCompletion Set.univ).support)) :
    (logDeriv d.entireCompletion 0).re =
      -∑' ρ : ℂ, (analyticOrderNatAt d.entireCompletion ρ : ℝ) * (1 / ρ).re :=
  hord.re_logDeriv_zero_eq_neg_tsum_of_isBounded h.differentiable_entireCompletion h0 hre (a := 1)
    (by simpa using hfe.analyticOrderNatAt_entireCompletion_one_sub_conj h)
    (by simpa using hfe.re_logDeriv_entireCompletion_one h)

/-- **Unpaired real-part partial fractions for an entire completion.** Off the zeros of an order-one
record with functional equation, `d.entireCompletion 0 ≠ 0`, and zeros of bounded real part,
`(logDeriv d.entireCompletion z).re = ∑' ρ, m_ρ (1 / (z - ρ)).re`. -/
theorem HasFunctionalEquation.re_logDeriv_entireCompletion (hfe : d.HasFunctionalEquation)
    (hord : OrderLE d.entireCompletion 1) (h0 : d.entireCompletion 0 ≠ 0)
    (hre : IsBounded (Complex.re '' (MeromorphicOn.divisor d.entireCompletion Set.univ).support))
    {z : ℂ} (hz : d.entireCompletion z ≠ 0) :
    (logDeriv d.entireCompletion z).re =
      ∑' ρ : ℂ, (analyticOrderNatAt d.entireCompletion ρ : ℝ) * (1 / (z - ρ)).re :=
  hord.re_logDeriv_eq_tsum_of_isBounded h.differentiable_entireCompletion h0 hre (a := 1)
    (by simpa using hfe.analyticOrderNatAt_entireCompletion_one_sub_conj h)
    (by simpa using hfe.re_logDeriv_entireCompletion_one h) hz

/-- For an order-one record with functional equation and `d.entireCompletion 0 ≠ 0`, the real part
`(logDeriv d.entireCompletion z).re` is nonnegative at every `z` with `d.entireCompletion z ≠ 0`
lying to the right of all zeros. -/
theorem HasFunctionalEquation.re_logDeriv_entireCompletion_nonneg_of_zero_ne_zero
    (hfe : d.HasFunctionalEquation)
    (hord : OrderLE d.entireCompletion 1) (h0 : d.entireCompletion 0 ≠ 0)
    {z : ℂ} (hz : d.entireCompletion z ≠ 0) (hle : ∀ ρ, d.entireCompletion ρ = 0 → ρ.re ≤ z.re) :
    0 ≤ (logDeriv d.entireCompletion z).re :=
  hord.re_logDeriv_nonneg_of_analyticOrderNatAt h.differentiable_entireCompletion h0 (a := 1)
    (by simpa using hfe.analyticOrderNatAt_entireCompletion_one_sub_conj h)
    (by simpa using hfe.re_logDeriv_entireCompletion_one h) hz hle

/-- **Finite-subset zero bound for an entire completion.** For an order-one record with functional
equation and `d.entireCompletion 0 ≠ 0`, at any `z` with `d.entireCompletion z ≠ 0` to the right of
all zeros, any finite sum of zero terms is at most `(logDeriv d.entireCompletion z).re`. -/
theorem HasFunctionalEquation.sum_analyticOrderNatAt_entireCompletion_mul_re_one_div_sub_le
    (hfe : d.HasFunctionalEquation) (hord : OrderLE d.entireCompletion 1)
    (h0 : d.entireCompletion 0 ≠ 0) {z : ℂ} (hz : d.entireCompletion z ≠ 0)
    (hle : ∀ ρ, d.entireCompletion ρ = 0 → ρ.re ≤ z.re) (S : Finset ℂ) :
    (∑ ρ ∈ S, (analyticOrderNatAt d.entireCompletion ρ : ℝ) * (1 / (z - ρ)).re) ≤
      (logDeriv d.entireCompletion z).re :=
  hord.sum_analyticOrderNatAt_mul_re_one_div_sub_le h.differentiable_entireCompletion h0 (a := 1)
    (by simpa using hfe.analyticOrderNatAt_entireCompletion_one_sub_conj h)
    (by simpa using hfe.re_logDeriv_entireCompletion_one h) hz hle S

/-- **Single-zero lower bound for an entire completion.** For an order-one record with functional
equation and `d.entireCompletion 0 ≠ 0`, at any `z` with `d.entireCompletion z ≠ 0` to the right of
all zeros, every zero `ρ` of `d.entireCompletion` satisfies
`(1 / (z - ρ)).re ≤ (logDeriv d.entireCompletion z).re`. -/
theorem HasFunctionalEquation.re_one_div_sub_le_re_logDeriv_entireCompletion
    (hfe : d.HasFunctionalEquation) (hord : OrderLE d.entireCompletion 1)
    (h0 : d.entireCompletion 0 ≠ 0) {z : ℂ} (hz : d.entireCompletion z ≠ 0)
    (hle : ∀ ρ, d.entireCompletion ρ = 0 → ρ.re ≤ z.re)
    {ρ : ℂ} (hρ : d.entireCompletion ρ = 0) :
    (1 / (z - ρ)).re ≤ (logDeriv d.entireCompletion z).re :=
  hord.re_one_div_sub_le_re_logDeriv h.differentiable_entireCompletion h0 (a := 1)
    (by simpa using hfe.analyticOrderNatAt_entireCompletion_one_sub_conj h)
    (by simpa using hfe.re_logDeriv_entireCompletion_one h) hz hle hρ

end VerticalStrip

end TauCeti.LFunctions.AnalyticLFunctionData
