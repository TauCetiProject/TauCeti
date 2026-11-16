/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.VerticalStrip
public import TauCeti.NumberTheory.LFunctions.Zeros.Divisor

/-!
# Hadamard real-part identities for completed L-function records

Let `d : AnalyticLFunctionData` be a meromorphically continued record. By the reflection symmetries
of `TauCeti.NumberTheory.LFunctions.Zeros.Completion.Basic`, a functional equation gives
`Λ₀'/Λ₀(d, 1 - conj s) = -conj (Λ₀'/Λ₀(d, s))` everywhere — whether or not `d` has poles — and in
particular `(logDeriv d.entireCompletion 1).re = -(logDeriv d.entireCompletion 0).re`, while
`s ↦ 1 - conj s` preserves the natural zero multiplicities `analyticOrderNatAt d.entireCompletion`
(which agree with `(MeromorphicOn.divisor d.completed Set.univ ·).toNat` by
`HasMeromorphicContinuation.analyticOrderNatAt_entireCompletion_eq_toNat_divisor_completed`).

When `d.entireCompletion` has order strictly below two and zeros of bounded real part, the
real-part reciprocal series over its zeros converge absolutely. At order at most one with
`d.entireCompletion 0 ≠ 0`, combining logarithmic-derivative antisymmetry with the vertical-strip
partial-fraction expansion cancels the Hadamard constant:
`(logDeriv d.entireCompletion 0).re = -∑' ρ, (analyticOrderNatAt d.entireCompletion ρ) * Re (1 / ρ)`
and `(logDeriv d.entireCompletion z).re = ∑' ρ, m_ρ Re (1 / (z - ρ))` off the zeros. Every upper
bound `Re ρ ≤ B` on the zeros automatically yields the lower bound `1 - B ≤ Re ρ` by reflection
(without assuming `d.entireCompletion 0 ≠ 0`), so positivity, finite-subset bounds, and single-zero
bounds to the right of all zeros require no separate strip-boundedness assumption.

## Main results

* `HasMeromorphicContinuation.summable_norm_analyticOrderNatAt_entireCompletion_mul_re_one_div_sub`,
  `HasMeromorphicContinuation.summable_analyticOrderNatAt_entireCompletion_mul_re_one_div_sub`,
  `HasMeromorphicContinuation.summable_norm_analyticOrderNatAt_entireCompletion_mul_re_one_div`,
  and `HasMeromorphicContinuation.summable_analyticOrderNatAt_entireCompletion_mul_re_one_div`:
  absolute and signed convergence of the real-part zero series below order two.
* `HasFunctionalEquation.isBounded_re_divisor_support_entireCompletion`: strip boundedness of the
  zeros from any one-sided upper bound `Re ρ ≤ B`.
* `HasFunctionalEquation.re_logDeriv_entireCompletion_zero` and
  `HasFunctionalEquation.re_logDeriv_entireCompletion`: real-part formula for the Hadamard constant
  and unpaired real-part partial-fraction expansion of `Λ₀'/Λ₀`.
* `HasFunctionalEquation.re_logDeriv_entireCompletion_nonneg`,
  `HasFunctionalEquation.sum_analyticOrderNatAt_entireCompletion_mul_re_one_div_sub_le`, and
  `HasFunctionalEquation.re_one_div_sub_le_re_logDeriv_entireCompletion`: positivity, finite-subset
  lower bounds, and single-zero lower bounds to the right of all zeros.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 12 and 14.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §10.2,
  Theorem 10.16 and Corollary 10.18.
-/

public section

open Complex ComplexConjugate Filter Topology Bornology
open scoped BigOperators

namespace TauCeti.LFunctions.AnalyticLFunctionData

variable {d : AnalyticLFunctionData} (h : d.HasMeromorphicContinuation)
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
theorem HasFunctionalEquation.re_logDeriv_entireCompletion_zero (hfe : d.HasFunctionalEquation)
    (hord : OrderLE d.entireCompletion 1) (h0 : d.entireCompletion 0 ≠ 0)
    (hre : IsBounded (Complex.re '' (MeromorphicOn.divisor d.entireCompletion Set.univ).support)) :
    (logDeriv d.entireCompletion 0).re =
      -∑' ρ : ℂ, (analyticOrderNatAt d.entireCompletion ρ : ℝ) * (1 / ρ).re :=
  hord.re_logDeriv_zero_eq_neg_tsum h.differentiable_entireCompletion h0 hre (a := 1)
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
  hord.re_logDeriv_eq_tsum h.differentiable_entireCompletion h0 hre (a := 1)
    (by simpa using hfe.analyticOrderNatAt_entireCompletion_one_sub_conj h)
    (by simpa using hfe.re_logDeriv_entireCompletion_one h) hz

/-- For an order-one record with functional equation and `d.entireCompletion 0 ≠ 0`, the real part
`(logDeriv d.entireCompletion z).re` is nonnegative at every `z` with `d.entireCompletion z ≠ 0`
lying to the right of all zeros. -/
theorem HasFunctionalEquation.re_logDeriv_entireCompletion_nonneg (hfe : d.HasFunctionalEquation)
    (hord : OrderLE d.entireCompletion 1) (h0 : d.entireCompletion 0 ≠ 0)
    {z : ℂ} (hz : d.entireCompletion z ≠ 0) (hle : ∀ ρ, d.entireCompletion ρ = 0 → ρ.re ≤ z.re) :
    0 ≤ (logDeriv d.entireCompletion z).re :=
  hord.re_logDeriv_nonneg h.differentiable_entireCompletion h0 (a := 1)
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

end TauCeti.LFunctions.AnalyticLFunctionData
