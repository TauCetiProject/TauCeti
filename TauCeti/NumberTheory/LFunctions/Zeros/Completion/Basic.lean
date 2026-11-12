/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Polynomial
public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.NumberTheory.LFunctions.Data.Basic

/-!
# Entire completions of meromorphic L-function records

The polar polynomial has precisely the recorded poles as roots, with their recorded
multiplicities. Multiplying it by the completed function cancels the poles at the level of
germs, but the pointwise product still has the wrong values at those points. The function
`AnalyticLFunctionData.entireCompletion` repairs these values using Mathlib's normal-form
representative `toMeromorphicNFOn`.

For a record with meromorphic continuation, the resulting function is entire, has the
expected orders and divisor, and is nonzero at every cleared pole. The uniqueness theorem
allows identification with explicit entire formulas without unfolding the extension.

The orders of the entire completion are symmetric: reflection across the real axis carries the
orders of `Λ₀(d)` at `s` to those of `Λ₀(d^∨)` at `conj s`, and with a functional equation the
orders of `Λ₀(d)` at `1 - s` are those of `Λ₀(d^∨)` at `s`. Together, `s ↦ 1 - conj s` preserves
the orders and the divisor of `Λ₀(d)`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §11–12.
-/

public section

open ComplexConjugate Filter Topology Polynomial

namespace TauCeti.LFunctions.AnalyticLFunctionData

variable (d : AnalyticLFunctionData)

/-- The monic polynomial whose roots are the recorded poles, with their pole orders. -/
noncomputable def polarPolynomial : ℂ[X] :=
  d.polarOrder.prod fun p n ↦ (X - C p) ^ n

theorem polarPolynomial_def :
    d.polarPolynomial = d.polarOrder.prod fun p n ↦ (X - C p) ^ n := (rfl)

/-- The polar polynomial is monic, including when there are no poles. -/
theorem monic_polarPolynomial : d.polarPolynomial.Monic := by
  classical
  exact monic_prod_of_monic _ _ fun p _ ↦ (monic_X_sub_C p).pow _

/-- Evaluation of the polar polynomial as a finite product. -/
theorem polarPolynomial_eval (s : ℂ) :
    d.polarPolynomial.eval s = ∏ p ∈ d.polarOrder.support, (s - p) ^ d.polarOrder p := by
  classical
  simp [polarPolynomial_def, Finsupp.prod, Polynomial.eval_prod]

/-- The polar polynomial has exactly the prescribed order at each point. -/
@[simp]
theorem meromorphicOrderAt_polarPolynomial (s : ℂ) :
    meromorphicOrderAt (fun z ↦ d.polarPolynomial.eval z) s = (d.polarOrder s : ℕ) := by
  classical
  simp_rw [polarPolynomial_eval]
  rw [meromorphicOrderAt_fun_prod (fun p _ ↦ by fun_prop)]
  rw [Finset.sum_eq_single s]
  · exact meromorphicOrderAt_pow_id_sub_const
  · intro p _ hps
    have ha : AnalyticAt ℂ (fun z : ℂ ↦ (z - p) ^ d.polarOrder p) s := by fun_prop
    exact ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
      (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hps)))
  · intro hs
    simpa [Finsupp.notMem_support_iff.mp hs] using meromorphicOrderAt_const s (1 : ℂ)

/-- The roots of the polar polynomial are precisely the recorded poles. -/
@[simp]
theorem polarPolynomial_eval_eq_zero_iff (s : ℂ) :
    d.polarPolynomial.eval s = 0 ↔ d.polarOrder s ≠ 0 := by
  have ha := AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) d.polarPolynomial s trivial
  apply not_iff_not.mp
  simpa using ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.symm

/-- The analytic representative of the product of the polar polynomial and the completion.
At a cleared pole this is the removable extension, not the raw pointwise product. -/
noncomputable def entireCompletion : ℂ → ℂ :=
  toMeromorphicNFOn (fun s ↦ d.polarPolynomial.eval s * d.completed s) Set.univ

theorem entireCompletion_def : d.entireCompletion =
    toMeromorphicNFOn (fun s ↦ d.polarPolynomial.eval s * d.completed s) Set.univ := (rfl)

variable {d} (h : d.HasMeromorphicContinuation)

include h

private theorem meromorphic_polarPolynomial_mul :
    Meromorphic (fun s ↦ d.polarPolynomial.eval s * d.completed s) :=
  fun s ↦ (AnalyticOnNhd.eval_polynomial d.polarPolynomial s trivial).meromorphicAt.mul
    (h.meromorphic s)

/-- The entire completion agrees with the pole-cleared product as a punctured germ everywhere. -/
theorem HasMeromorphicContinuation.entireCompletion_eventuallyEq (s : ℂ) :
    d.entireCompletion =ᶠ[𝓝[≠] s] fun z ↦ d.polarPolynomial.eval z * d.completed z := by
  rw [entireCompletion_def]
  exact (meromorphic_polarPolynomial_mul h).meromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE
    (Set.mem_univ s)

/-- Clearing the poles adds the polar multiplicity to the meromorphic order. -/
theorem HasMeromorphicContinuation.meromorphicOrderAt_entireCompletion (s : ℂ) :
    meromorphicOrderAt d.entireCompletion s =
      meromorphicOrderAt d.completed s + (d.polarOrder s : ℕ) := by
  rw [meromorphicOrderAt_congr (h.entireCompletion_eventuallyEq s),
    fun_meromorphicOrderAt_mul
      (AnalyticOnNhd.eval_polynomial d.polarPolynomial s trivial).meromorphicAt (h.meromorphic s),
    meromorphicOrderAt_polarPolynomial, add_comm]

/-- The repaired product is analytic at every point, including the cleared poles. -/
theorem HasMeromorphicContinuation.analyticAt_entireCompletion (s : ℂ) :
    AnalyticAt ℂ d.entireCompletion s := by
  have hnf := meromorphicNFOn_toMeromorphicNFOn
    (fun z ↦ d.polarPolynomial.eval z * d.completed z) Set.univ (Set.mem_univ s)
  apply hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [← entireCompletion_def, h.meromorphicOrderAt_entireCompletion]
  by_cases hs : d.polarOrder s = 0
  · simpa [hs] using (h.analyticAt s hs).meromorphicOrderAt_nonneg
  · rw [h.meromorphicOrderAt_eq s hs]
    simp

/-- The entire completion is entire. -/
theorem HasMeromorphicContinuation.differentiable_entireCompletion :
    Differentiable ℂ d.entireCompletion :=
  fun s ↦ (h.analyticAt_entireCompletion s).differentiableAt

/-- The entire completion is meromorphic on `ℂ`. -/
theorem HasMeromorphicContinuation.meromorphicOn_entireCompletion :
    MeromorphicOn d.entireCompletion Set.univ :=
  fun s _ ↦ (h.analyticAt_entireCompletion s).meromorphicAt

/-- Away from the poles no value is changed. -/
theorem HasMeromorphicContinuation.entireCompletion_eq {s : ℂ} (hs : d.polarOrder s = 0) :
    d.entireCompletion s = d.polarPolynomial.eval s * d.completed s := by
  rw [entireCompletion_def]
  exact toMeromorphicNFOn_apply_of_analyticAt (meromorphic_polarPolynomial_mul h)
    ((AnalyticOnNhd.eval_polynomial d.polarPolynomial s trivial).mul (h.analyticAt s hs))

/-- At a cleared pole the entire completion has order zero. -/
@[simp]
theorem HasMeromorphicContinuation.meromorphicOrderAt_entireCompletion_of_pole {s : ℂ}
    (hs : d.polarOrder s ≠ 0) : meromorphicOrderAt d.entireCompletion s = 0 := by
  rw [h.meromorphicOrderAt_entireCompletion, h.meromorphicOrderAt_eq s hs]
  simp

/-- Removing a pole does not create a zero. -/
@[simp]
theorem HasMeromorphicContinuation.entireCompletion_ne_zero_of_pole {s : ℂ}
    (hs : d.polarOrder s ≠ 0) : d.entireCompletion s ≠ 0 :=
  (h.analyticAt_entireCompletion s).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp
    (h.meromorphicOrderAt_entireCompletion_of_pole hs)

/-- Pointwise divisor formula, including at the cleared poles. -/
theorem HasMeromorphicContinuation.divisor_entireCompletion (s : ℂ) :
    MeromorphicOn.divisor d.entireCompletion Set.univ s =
      MeromorphicOn.divisor d.completed Set.univ s + (d.polarOrder s : ℤ) := by
  rw [MeromorphicOn.divisor_apply h.meromorphicOn_entireCompletion (Set.mem_univ s),
    MeromorphicOn.divisor_apply h.meromorphic.meromorphicOn (Set.mem_univ s),
    h.meromorphicOrderAt_entireCompletion]
  by_cases hs : d.polarOrder s = 0
  · simp [hs]
  · rw [h.meromorphicOrderAt_eq s hs]
    simp

/-- A continuous function agreeing with the cleared product off the poles equals the
entire completion. -/
theorem HasMeromorphicContinuation.entireCompletion_unique {F : ℂ → ℂ}
    (hF : Continuous F)
    (heq : ∀ s, d.polarOrder s = 0 → F s = d.polarPolynomial.eval s * d.completed s) :
    F = d.entireCompletion := by
  funext s
  apply Filter.EventuallyEq.eq_of_nhds
  apply (hF.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (h.analyticAt_entireCompletion s).continuousAt).mp
  have hfin := d.polarOrder.support.finite_toSet
  filter_upwards [nhdsNE_of_nhdsNE_sdiff_finite (x := s) univ_mem hfin.to_subtype]
    with z hz
  have hz0 : d.polarOrder z = 0 := by simpa using hz.2
  rw [heq z hz0, h.entireCompletion_eq hz0]

/-! ### Symmetries of the orders -/

/-- Reflection across the real axis carries the orders of the entire completion at `s` to those
of the entire completion of the dual card at `conj s`. -/
theorem HasMeromorphicContinuation.meromorphicOrderAt_dual_entireCompletion_conj (s : ℂ) :
    meromorphicOrderAt d.dual.entireCompletion (conj s) =
      meromorphicOrderAt d.entireCompletion s := by
  rw [h.dual.meromorphicOrderAt_entireCompletion, h.meromorphicOrderAt_entireCompletion,
    dual_completed, TauCeti.meromorphicOrderAt_conj_conj, dual_polarOrder_apply,
    Complex.conj_conj]

/-- The divisor form of `HasMeromorphicContinuation.meromorphicOrderAt_dual_entireCompletion_conj`.
-/
theorem HasMeromorphicContinuation.divisor_dual_entireCompletion_conj (s : ℂ) :
    MeromorphicOn.divisor d.dual.entireCompletion Set.univ (conj s) =
      MeromorphicOn.divisor d.entireCompletion Set.univ s := by
  rw [MeromorphicOn.divisor_apply h.dual.meromorphicOn_entireCompletion (Set.mem_univ _),
    MeromorphicOn.divisor_apply h.meromorphicOn_entireCompletion (Set.mem_univ _),
    h.meromorphicOrderAt_dual_entireCompletion_conj]

/-- The functional equation carries the orders of the entire completion of the dual card at `s`
to those of the entire completion at `1 - s`. -/
theorem HasFunctionalEquation.meromorphicOrderAt_entireCompletion_one_sub
    (hfe : d.HasFunctionalEquation) (s : ℂ) :
    meromorphicOrderAt d.entireCompletion (1 - s) =
      meromorphicOrderAt d.dual.entireCompletion s := by
  have hε : d.rootNumber ≠ 0 := norm_ne_zero_iff.mp (by simp [hfe.norm_rootNumber])
  have hc : meromorphicOrderAt d.completed (1 - s) = meromorphicOrderAt d.dual.completed s := by
    rw [meromorphicOrderAt_congr (hfe.eventuallyEq (1 - s)),
      show (fun z ↦ d.rootNumber * d.dual.completed (1 - z)) =
        d.rootNumber • (d.dual.completed ∘ fun z ↦ 1 - z) by
          funext z; simp [Function.comp_def, smul_eq_mul],
      meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hε,
      meromorphicOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp), sub_sub_cancel]
  rw [h.meromorphicOrderAt_entireCompletion, h.dual.meromorphicOrderAt_entireCompletion, hc,
    dual_polarOrder_apply, ← hfe.polarOrder_one_sub_conj (conj s), Complex.conj_conj]

/-- The divisor form of `HasFunctionalEquation.meromorphicOrderAt_entireCompletion_one_sub`. -/
theorem HasFunctionalEquation.divisor_entireCompletion_one_sub (hfe : d.HasFunctionalEquation)
    (s : ℂ) :
    MeromorphicOn.divisor d.entireCompletion Set.univ (1 - s) =
      MeromorphicOn.divisor d.dual.entireCompletion Set.univ s := by
  rw [MeromorphicOn.divisor_apply h.meromorphicOn_entireCompletion (Set.mem_univ _),
    MeromorphicOn.divisor_apply h.dual.meromorphicOn_entireCompletion (Set.mem_univ _),
    hfe.meromorphicOrderAt_entireCompletion_one_sub h]

/-- The reflection `s ↦ 1 - conj s` preserves the orders of the entire completion. -/
theorem HasFunctionalEquation.meromorphicOrderAt_entireCompletion_one_sub_conj
    (hfe : d.HasFunctionalEquation) (s : ℂ) :
    meromorphicOrderAt d.entireCompletion (1 - conj s) =
      meromorphicOrderAt d.entireCompletion s := by
  rw [hfe.meromorphicOrderAt_entireCompletion_one_sub h,
    h.meromorphicOrderAt_dual_entireCompletion_conj]

/-- The reflection `s ↦ 1 - conj s` preserves the divisor of the entire completion. -/
theorem HasFunctionalEquation.divisor_entireCompletion_one_sub_conj
    (hfe : d.HasFunctionalEquation) (s : ℂ) :
    MeromorphicOn.divisor d.entireCompletion Set.univ (1 - conj s) =
      MeromorphicOn.divisor d.entireCompletion Set.univ s := by
  rw [hfe.divisor_entireCompletion_one_sub h, h.divisor_dual_entireCompletion_conj]

end TauCeti.LFunctions.AnalyticLFunctionData
