/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.VerticalStrip
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Basic
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Hadamard real-part identities for completed L-function records

For a meromorphically continued record `d : AnalyticLFunctionData`, conjugation carries the polar
polynomial and the repaired entire completion of `d` to those of `d.dual`. When `d` also satisfies a
functional equation, substituting `1 - s` into the polar polynomial multiplies the dual polar
polynomial by `(-1) ^ deg`, so the functional equation extends across cleared poles as
`Λ₀(d, 1 - s) = (-1) ^ deg · ε(d) · Λ₀(d^∨, s)`. Because the prefactor is a nonzero constant,
differentiating logarithmically gives `Λ₀'/Λ₀(d, 1 - s) = -Λ₀'/Λ₀(d^∨, s)` and hence
`Λ₀'/Λ₀(d, 1 - conj s) = -conj (Λ₀'/Λ₀(d, s))` at every point of `ℂ` — whether or not `d` has poles.
In particular `(logDeriv d.entireCompletion 1).re = -(logDeriv d.entireCompletion 0).re`.

When `d.entireCompletion` has order at most one, is nonzero at `0`, and has zeros of bounded real
part, combining this antisymmetry with the vertical-strip partial-fraction expansion cancels the
Hadamard constant:
`(logDeriv d.entireCompletion 0).re = -∑' ρ, (analyticOrderNatAt d.entireCompletion ρ) * Re (1 / ρ)`
and `(logDeriv d.entireCompletion z).re = ∑' ρ, m_ρ Re (1 / (z - ρ))` off the zeros. Every upper
bound `Re ρ ≤ B` on the zeros automatically yields the lower bound `1 - B ≤ Re ρ` by reflection, so
positivity and finite-subset bounds to the right of all zeros require no separate boundedness
assumption.

## Main results

* `TauCeti.LFunctions.AnalyticLFunctionData.HasMeromorphicContinuation.dual_entireCompletion_apply`
  and `HasFunctionalEquation.entireCompletion_one_sub`: reflection and functional equation of the
  pole-cleared entire completion, including records with poles.
* `HasFunctionalEquation.logDeriv_entireCompletion_one_sub_conj` and
  `HasFunctionalEquation.re_logDeriv_entireCompletion_one`: functional equation of `Λ₀'/Λ₀` and
  antisymmetry between `s = 0` and `s = 1`.
* `HasFunctionalEquation.re_logDeriv_entireCompletion_zero` and
  `HasFunctionalEquation.re_logDeriv_entireCompletion`: real-part formula for the Hadamard constant
  and unpaired real-part partial-fraction expansion of `Λ₀'/Λ₀`.
* `HasFunctionalEquation.re_logDeriv_entireCompletion_nonneg` and
  `HasFunctionalEquation.sum_analyticOrderNatAt_entireCompletion_mul_re_one_div_sub_le`:
  positivity and finite-subset lower bounds to the right of all zeros.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapters 12 and 14.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §10.2,
  Theorem 10.16 and Corollary 10.18.
-/

public section

open Complex ComplexConjugate Filter Topology Polynomial Bornology
open scoped BigOperators

namespace TauCeti.LFunctions.AnalyticLFunctionData

variable (d : AnalyticLFunctionData)

/-! ### Polar polynomial under conjugation and reflection -/

/-- The degree of the polar polynomial is the total multiplicity of all recorded poles. -/
theorem natDegree_polarPolynomial :
    d.polarPolynomial.natDegree = ∑ p ∈ d.polarOrder.support, d.polarOrder p := by
  classical
  rw [polarPolynomial_def, Finsupp.prod,
    Polynomial.natDegree_prod_of_monic _ _ (fun p _ ↦ (monic_X_sub_C p).pow _)]
  simp

/-- Evaluating the polar polynomial of the dual card conjugates evaluation at the conjugate point.
-/
theorem dual_polarPolynomial_eval (s : ℂ) :
    d.dual.polarPolynomial.eval s = conj (d.polarPolynomial.eval (conj s)) := by
  classical
  let e : ℂ ≃ ℂ := ⟨conj, conj, Complex.conj_conj, Complex.conj_conj⟩
  rw [polarPolynomial_eval, polarPolynomial_eval, map_prod]
  refine (Finset.prod_equiv e ?_ ?_).symm
  · intro p
    simp [e, Finsupp.mem_support_iff]
  · intro p _
    simp [e]

variable {d}

/-- A functional equation equates the polar order of `d` at `1 - s` with that of `d.dual` at `s`. -/
theorem HasFunctionalEquation.polarOrder_one_sub (hfe : d.HasFunctionalEquation) (s : ℂ) :
    d.polarOrder (1 - s) = d.dual.polarOrder s := by
  rw [dual_polarOrder_apply, ← hfe.polarOrder_one_sub_conj (conj s), Complex.conj_conj]

/-- Under a functional equation, evaluating the polar polynomial at `1 - s` multiplies evaluation of
the dual polar polynomial at `s` by `(-1) ^ d.polarPolynomial.natDegree`. -/
theorem HasFunctionalEquation.polarPolynomial_eval_one_sub (hfe : d.HasFunctionalEquation) (s : ℂ) :
    d.polarPolynomial.eval (1 - s) =
      (-1 : ℂ) ^ d.polarPolynomial.natDegree * d.dual.polarPolynomial.eval s := by
  classical
  let e : ℂ ≃ ℂ :=
    ⟨fun p ↦ 1 - p, fun p ↦ 1 - p, fun p ↦ sub_sub_cancel 1 p, fun p ↦ sub_sub_cancel 1 p⟩
  have hmem (p : ℂ) : p ∈ d.polarOrder.support ↔ e p ∈ d.dual.polarOrder.support := by
    simp [e, Finsupp.mem_support_iff, ← hfe.polarOrder_one_sub]
  have hdeg : d.polarPolynomial.natDegree =
      ∑ p ∈ d.dual.polarOrder.support, d.dual.polarOrder p := by
    rw [natDegree_polarPolynomial]
    refine Finset.sum_equiv e hmem fun p _ ↦ ?_
    simp [e, ← hfe.polarOrder_one_sub]
  rw [polarPolynomial_eval, polarPolynomial_eval, hdeg, ← Finset.prod_pow_eq_pow_sum,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_equiv e hmem fun p _ ↦ ?_
  simp only [e, Equiv.coe_fn_mk, ← hfe.polarOrder_one_sub, sub_sub_cancel, ← mul_pow]
  congr 1
  ring

/-! ### Functional equation of the entire completion and its logarithmic derivative -/

variable (h : d.HasMeromorphicContinuation)
include h

/-- The entire completion of the dual card is `s ↦ conj (d.entireCompletion (conj s))` everywhere,
including at cleared poles. -/
theorem HasMeromorphicContinuation.dual_entireCompletion_apply (s : ℂ) :
    d.dual.entireCompletion s = conj (d.entireCompletion (conj s)) := by
  have heq : (fun z ↦ conj (d.entireCompletion (conj z))) = d.dual.entireCompletion := by
    refine h.dual.entireCompletion_unique ?_ fun z hz ↦ ?_
    · exact continuous_conj.comp (h.differentiable_entireCompletion.continuous.comp continuous_conj)
    · rw [dual_polarOrder_apply] at hz
      rw [h.entireCompletion_eq hz, map_mul, ← dual_polarPolynomial_eval, ← dual_completed_apply]
  exact (congrFun heq s).symm

/-- Reflection across the real axis conjugates the entire completion into that of the dual card. -/
theorem HasMeromorphicContinuation.dual_entireCompletion_conj (s : ℂ) :
    d.dual.entireCompletion (conj s) = conj (d.entireCompletion s) := by
  rw [h.dual_entireCompletion_apply, Complex.conj_conj]

/-- Conjugation carries the logarithmic derivative of the entire completion to that of the dual
card. -/
theorem HasMeromorphicContinuation.logDeriv_dual_entireCompletion_conj (s : ℂ) :
    logDeriv d.dual.entireCompletion (conj s) = conj (logDeriv d.entireCompletion s) := by
  have hfn : d.dual.entireCompletion = conj ∘ d.entireCompletion ∘ conj :=
    funext h.dual_entireCompletion_apply
  rw [hfn, logDeriv_apply, logDeriv_apply, deriv_conj_conj]
  simp

/-- **Functional equation of the entire completion.** Clearing poles multiplies the root number by
`(-1) ^ d.polarPolynomial.natDegree` and extends the functional equation to every `s : ℂ`. -/
theorem HasFunctionalEquation.entireCompletion_one_sub (hfe : d.HasFunctionalEquation) (s : ℂ) :
    d.entireCompletion (1 - s) =
      (-1 : ℂ) ^ d.polarPolynomial.natDegree * d.rootNumber * d.dual.entireCompletion s := by
  have heq :
      (fun z ↦ (-1 : ℂ) ^ d.polarPolynomial.natDegree * d.rootNumber *
        d.dual.entireCompletion (1 - z)) = d.entireCompletion := by
    refine h.entireCompletion_unique ?_ fun z hz ↦ ?_
    · exact continuous_const.mul (h.dual.differentiable_entireCompletion.continuous.comp
        (continuous_const.sub continuous_id))
    · have hz' : d.dual.polarOrder (1 - z) = 0 := by
        rwa [← hfe.polarOrder_one_sub, sub_sub_cancel]
      have hz'' : d.polarOrder (1 - conj z) = 0 := by
        rwa [hfe.polarOrder_one_sub_conj]
      have hp := hfe.polarPolynomial_eval_one_sub (1 - z)
      rw [sub_sub_cancel] at hp
      rw [h.dual.entireCompletion_eq hz', hp, hfe.completed_eq z hz hz'']
      ring
  simpa only [sub_sub_cancel] using (congrFun heq (1 - s)).symm

/-- Nonvanishing of the entire completion at `0` transfers to `1` under a functional equation. -/
theorem HasFunctionalEquation.entireCompletion_one_ne_zero (hfe : d.HasFunctionalEquation)
    (h0 : d.entireCompletion 0 ≠ 0) : d.entireCompletion 1 ≠ 0 := by
  have heq : d.entireCompletion 1 =
      (-1 : ℂ) ^ d.polarPolynomial.natDegree * d.rootNumber * conj (d.entireCompletion 0) := by
    simpa using (hfe.entireCompletion_one_sub h (conj 0)).trans
      (by rw [h.dual_entireCompletion_conj])
  rw [heq]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_) (by simpa using h0)
  exact norm_ne_zero_iff.mp (by simp [hfe.norm_rootNumber])

/-- The functional equation negates the logarithmic derivative of the entire completion against that
of the dual card at every point, including zeros and cleared poles. -/
theorem HasFunctionalEquation.logDeriv_entireCompletion_one_sub (hfe : d.HasFunctionalEquation)
    (s : ℂ) : logDeriv d.entireCompletion (1 - s) = -logDeriv d.dual.entireCompletion s := by
  have hc : (-1 : ℂ) ^ d.polarPolynomial.natDegree * d.rootNumber ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num))
      (norm_ne_zero_iff.mp (by simp [hfe.norm_rootNumber]))
  have hcomp : logDeriv (fun z ↦ d.entireCompletion (1 - z)) s =
      -logDeriv d.entireCompletion (1 - s) := by
    rw [logDeriv_apply, logDeriv_apply, deriv_comp_const_sub, neg_div]
  rw [← neg_neg (logDeriv _ (1 - s)), ← hcomp,
    funext (hfe.entireCompletion_one_sub h), logDeriv_const_mul s _ hc]

/-- Reflection `s ↦ 1 - conj s` sends `logDeriv d.entireCompletion s` to `-conj` of itself. -/
theorem HasFunctionalEquation.logDeriv_entireCompletion_one_sub_conj (hfe : d.HasFunctionalEquation)
    (s : ℂ) : logDeriv d.entireCompletion (1 - conj s) = -conj (logDeriv d.entireCompletion s) := by
  rw [hfe.logDeriv_entireCompletion_one_sub h, h.logDeriv_dual_entireCompletion_conj]

/-- At `0` and `1`, the real parts of `logDeriv d.entireCompletion` are negatives of one another. -/
theorem HasFunctionalEquation.re_logDeriv_entireCompletion_one (hfe : d.HasFunctionalEquation) :
    (logDeriv d.entireCompletion 1).re = -(logDeriv d.entireCompletion 0).re := by
  simpa using congrArg Complex.re (hfe.logDeriv_entireCompletion_one_sub_conj h 0)

/-- Reflection `s ↦ 1 - conj s` preserves the analytic order of the entire completion. -/
theorem HasFunctionalEquation.analyticOrderAt_entireCompletion_one_sub_conj
    (hfe : d.HasFunctionalEquation) (s : ℂ) :
    analyticOrderAt d.entireCompletion (1 - conj s) = analyticOrderAt d.entireCompletion s := by
  have hm := hfe.meromorphicOrderAt_entireCompletion_one_sub_conj h s
  rw [(h.analyticAt_entireCompletion _).meromorphicOrderAt_eq,
    (h.analyticAt_entireCompletion _).meromorphicOrderAt_eq] at hm
  exact ENat.map_natCast_injective hm

/-- Reflection `s ↦ 1 - conj s` preserves the natural zero multiplicity of the entire completion. -/
theorem HasFunctionalEquation.analyticOrderNatAt_entireCompletion_one_sub_conj
    (hfe : d.HasFunctionalEquation) (s : ℂ) :
    analyticOrderNatAt d.entireCompletion (1 - conj s) =
      analyticOrderNatAt d.entireCompletion s :=
  congrArg ENat.toNat (hfe.analyticOrderAt_entireCompletion_one_sub_conj h s)

/-! ### Order-one real-part partial fractions for completed L-functions -/

/-- Under a functional equation, any upper bound `ρ.re ≤ B` on the zeros of `d.entireCompletion`
confines all zeros to `[1 - B, B]` and hence bounds the real parts of its divisor support. -/
theorem HasFunctionalEquation.isBounded_re_divisor_support_entireCompletion
    (hfe : d.HasFunctionalEquation) (h0 : d.entireCompletion 0 ≠ 0) {B : ℝ}
    (hB : ∀ ρ, d.entireCompletion ρ = 0 → ρ.re ≤ B) :
    IsBounded (Complex.re '' (MeromorphicOn.divisor d.entireCompletion Set.univ).support) :=
  isBounded_re_divisor_support_of_le h.differentiable_entireCompletion h0 (a := 1)
    (by simpa using hfe.analyticOrderNatAt_entireCompletion_one_sub_conj h) hB

/-- **Real part of the Hadamard constant.** For an order-one record with functional equation,
`d.entireCompletion 0 ≠ 0`, and zeros of bounded real part,
`(logDeriv d.entireCompletion 0).re = -∑' ρ, m_ρ (1 / ρ).re`. -/
theorem HasFunctionalEquation.re_logDeriv_entireCompletion_zero (hfe : d.HasFunctionalEquation)
    (hord : OrderLE d.entireCompletion 1) (h0 : d.entireCompletion 0 ≠ 0)
    (hre : IsBounded (Complex.re '' (MeromorphicOn.divisor d.entireCompletion Set.univ).support)) :
    (logDeriv d.entireCompletion 0).re =
      -∑' ρ : ℂ, (analyticOrderNatAt d.entireCompletion ρ : ℝ) * (1 / ρ).re :=
  hord.re_logDeriv_zero_eq_neg_tsum h.differentiable_entireCompletion h0 hre
    (a := 1) (by simpa using hfe.entireCompletion_one_ne_zero h h0)
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
  hord.re_logDeriv_eq_tsum h.differentiable_entireCompletion h0 hre
    (a := 1) (by simpa using hfe.entireCompletion_one_ne_zero h h0)
    (by simpa using hfe.analyticOrderNatAt_entireCompletion_one_sub_conj h)
    (by simpa using hfe.re_logDeriv_entireCompletion_one h) hz

/-- For an order-one record with functional equation and `d.entireCompletion 0 ≠ 0`, the real part
`(logDeriv d.entireCompletion z).re` is nonnegative at every `z` with `d.entireCompletion z ≠ 0`
lying to the right of all zeros. -/
theorem HasFunctionalEquation.re_logDeriv_entireCompletion_nonneg (hfe : d.HasFunctionalEquation)
    (hord : OrderLE d.entireCompletion 1) (h0 : d.entireCompletion 0 ≠ 0)
    {z : ℂ} (hz : d.entireCompletion z ≠ 0) (hle : ∀ ρ, d.entireCompletion ρ = 0 → ρ.re ≤ z.re) :
    0 ≤ (logDeriv d.entireCompletion z).re :=
  hord.re_logDeriv_nonneg h.differentiable_entireCompletion h0
    (a := 1) (by simpa using hfe.entireCompletion_one_ne_zero h h0)
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
  hord.sum_analyticOrderNatAt_mul_re_one_div_sub_le h.differentiable_entireCompletion h0
    (a := 1) (by simpa using hfe.entireCompletion_one_ne_zero h h0)
    (by simpa using hfe.analyticOrderNatAt_entireCompletion_one_sub_conj h)
    (by simpa using hfe.re_logDeriv_entireCompletion_one h) hz hle S

end TauCeti.LFunctions.AnalyticLFunctionData
