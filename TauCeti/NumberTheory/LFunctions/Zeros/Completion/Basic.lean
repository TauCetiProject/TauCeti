/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.LogDeriv
public import TauCeti.Analysis.Meromorphic.Continuation
public import TauCeti.NumberTheory.LFunctions.Data.Basic

import TauCeti.Analysis.Calculus.LogDeriv.Symmetry

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

The entire completion inherits both value, logarithmic-derivative, and order symmetries:
reflection across the real axis gives `Λ₀(d^∨)(s) = conj (Λ₀(d)(conj s))` and
`logDeriv Λ₀(d^∨) (conj s) = conj (logDeriv Λ₀(d) s)`, and with a functional equation
`Λ₀(d)(1 - s) = (-1) ^ deg(P_d) * ε * Λ₀(d^∨)(s)` and
`logDeriv Λ₀(d) (1 - s) = -logDeriv Λ₀(d^∨) s`. Together, `s ↦ 1 - conj s` preserves the orders
and divisor of `Λ₀(d)`, and nonvanishing on `1 ≤ Re s` reflects to `Re s ≤ 0`, confining all zeros
of `Λ₀(d)` to the open critical strip `0 < Re ρ < 1`.

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

/-- The degree of the polar polynomial is the total multiplicity of the recorded poles. -/
theorem natDegree_polarPolynomial :
    d.polarPolynomial.natDegree = ∑ p ∈ d.polarOrder.support, d.polarOrder p := by
  classical
  rw [polarPolynomial_def, Finsupp.prod,
    natDegree_prod_of_monic _ _ fun p _ ↦ (monic_X_sub_C p).pow _]
  simp [natDegree_pow]

/-- Evaluating the dual polar polynomial at `s` conjugates the polar polynomial at `conj s`. -/
theorem dual_polarPolynomial_eval (s : ℂ) :
    d.dual.polarPolynomial.eval s = conj (d.polarPolynomial.eval (conj s)) := by
  classical
  rw [polarPolynomial_eval, polarPolynomial_eval, map_prod]
  refine Finset.prod_bij (fun p _ ↦ conj p) ?_ ?_ ?_ ?_
  · intro p hp
    simpa using hp
  · intro p₁ _ p₂ _ h
    exact (starRingEnd ℂ).injective h
  · intro q hq
    exact ⟨conj q, by simpa using hq, Complex.conj_conj q⟩
  · intro p _
    simp

/-- Under a functional equation, reflecting the polar polynomial across `1/2` recovers the dual
polar polynomial up to the sign `(-1) ^ deg(P_d)`. -/
theorem HasFunctionalEquation.polarPolynomial_eval_one_sub {d : AnalyticLFunctionData}
    (hfe : d.HasFunctionalEquation) (s : ℂ) :
    d.polarPolynomial.eval (1 - s) =
      (-1) ^ d.polarPolynomial.natDegree * d.dual.polarPolynomial.eval s := by
  classical
  have hord : ∀ p : ℂ, d.dual.polarOrder (1 - p) = d.polarOrder p := fun p ↦ by
    rw [dual_polarOrder_apply, map_sub, map_one, hfe.polarOrder_one_sub_conj]
  rw [polarPolynomial_eval, polarPolynomial_eval, natDegree_polarPolynomial,
    ← Finset.prod_pow_eq_pow_sum]
  have hprod : ∏ p ∈ d.polarOrder.support, (1 - s - p) ^ d.polarOrder p =
      (∏ p ∈ d.polarOrder.support, (-1 : ℂ) ^ d.polarOrder p) *
        ∏ p ∈ d.polarOrder.support, (s - (1 - p)) ^ d.polarOrder p := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ ↦ ?_
    rw [← mul_pow]
    congr 1
    ring
  rw [hprod]
  congr 1
  refine Finset.prod_bij (fun p _ ↦ 1 - p) ?_ ?_ ?_ ?_
  · intro p hp
    simpa [hord p] using hp
  · intro p₁ _ p₂ _ h
    exact sub_right_injective h
  · intro q hq
    refine ⟨1 - q, ?_, sub_sub_cancel 1 q⟩
    have hq' := hord (1 - q)
    rw [sub_sub_cancel] at hq'
    simpa [hq'] using hq
  · intro p _
    rw [hord p]

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

/-! ### Value, logarithmic-derivative, and zero-location symmetries -/

/-- Reflection across the real axis carries the entire completion to that of the dual card. -/
theorem HasMeromorphicContinuation.dual_entireCompletion (s : ℂ) :
    d.dual.entireCompletion s = conj (d.entireCompletion (conj s)) := by
  have heq : (fun z ↦ conj (d.entireCompletion (conj z))) = d.dual.entireCompletion := by
    apply h.dual.entireCompletion_unique
    · exact Complex.continuous_conj.comp
        (h.differentiable_entireCompletion.continuous.comp Complex.continuous_conj)
    · intro z hz
      rw [dual_polarOrder_apply] at hz
      rw [h.entireCompletion_eq hz, map_mul, ← dual_polarPolynomial_eval, dual_completed_apply]
  exact (congrFun heq s).symm

/-- The functional equation of the entire completion, with the sign `(-1) ^ deg(P_d)` from
reflecting the polar polynomial across `1/2`. -/
theorem HasFunctionalEquation.entireCompletion_one_sub (hfe : d.HasFunctionalEquation) (s : ℂ) :
    d.entireCompletion (1 - s) =
      (-1) ^ d.polarPolynomial.natDegree * d.rootNumber * d.dual.entireCompletion s := by
  have heq : (fun z ↦ (-1) ^ d.polarPolynomial.natDegree * d.rootNumber *
      d.dual.entireCompletion (1 - z)) = d.entireCompletion := by
    apply h.entireCompletion_unique
    · exact continuous_const.mul
        (h.dual.differentiable_entireCompletion.continuous.comp
          (continuous_const.sub continuous_id))
    · intro z hz
      have hz' : d.dual.polarOrder (1 - z) = 0 := by
        rw [dual_polarOrder_apply, map_sub, map_one, hfe.polarOrder_one_sub_conj, hz]
      rw [h.dual.entireCompletion_eq hz',
        hfe.completed_eq z hz (by rw [hfe.polarOrder_one_sub_conj, hz])]
      have hp := hfe.polarPolynomial_eval_one_sub (1 - z)
      rw [sub_sub_cancel] at hp
      rw [hp]
      ring
  exact (congrFun heq (1 - s)).symm.trans (by rw [sub_sub_cancel])

/-- Combined functional and conjugation symmetry of the entire completion. -/
theorem HasFunctionalEquation.entireCompletion_one_sub_eq_mul_conj_conj
    (hfe : d.HasFunctionalEquation) (s : ℂ) :
    d.entireCompletion (1 - s) =
      (-1) ^ d.polarPolynomial.natDegree * d.rootNumber *
        conj (d.entireCompletion (conj s)) := by
  rw [hfe.entireCompletion_one_sub h, h.dual_entireCompletion]

/-- Reflection across the real axis conjugates the logarithmic derivative of the entire
completion. -/
theorem HasMeromorphicContinuation.logDeriv_dual_entireCompletion_conj (s : ℂ) :
    logDeriv d.dual.entireCompletion (conj s) = conj (logDeriv d.entireCompletion s) := by
  have hfun : d.dual.entireCompletion = conj ∘ d.entireCompletion ∘ conj :=
    funext h.dual_entireCompletion
  rw [hfun, TauCeti.logDeriv_conj_conj, Complex.conj_conj]

/-- The functional equation negates and dualizes the logarithmic derivative of the entire
completion across `s ↦ 1 - s`. -/
theorem HasFunctionalEquation.logDeriv_entireCompletion_one_sub
    (hfe : d.HasFunctionalEquation) (s : ℂ) :
    logDeriv d.entireCompletion (1 - s) = -logDeriv d.dual.entireCompletion s := by
  have hc : (-1 : ℂ) ^ d.polarPolynomial.natDegree * d.rootNumber ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num))
      (norm_ne_zero_iff.mp (by simp [hfe.norm_rootNumber]))
  have hfun : (fun z ↦ d.entireCompletion (1 - z)) =
      fun z ↦ ((-1 : ℂ) ^ d.polarPolynomial.natDegree * d.rootNumber) *
        d.dual.entireCompletion z :=
    funext (hfe.entireCompletion_one_sub h)
  have h1 := congrFun (congrArg logDeriv hfun) s
  rw [TauCeti.logDeriv_comp_const_sub, logDeriv_const_mul _ _ hc] at h1
  exact neg_eq_iff_eq_neg.mp h1

/-- Under a functional equation, nonvanishing of the entire completion on `1 ≤ Re s` reflects to
nonvanishing on `Re s ≤ 0`. -/
theorem HasFunctionalEquation.entireCompletion_ne_zero_of_re_nonpos
    (hfe : d.HasFunctionalEquation) (h1 : ∀ z : ℂ, 1 ≤ z.re → d.entireCompletion z ≠ 0)
    {s : ℂ} (hs : s.re ≤ 0) : d.entireCompletion s ≠ 0 := by
  have hsym := hfe.entireCompletion_one_sub_eq_mul_conj_conj h (1 - s)
  rw [sub_sub_cancel] at hsym
  rw [hsym]
  have hc : (-1 : ℂ) ^ d.polarPolynomial.natDegree * d.rootNumber ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num))
      (norm_ne_zero_iff.mp (by simp [hfe.norm_rootNumber]))
  refine mul_ne_zero hc ((map_ne_zero (starRingEnd ℂ)).mpr ?_)
  exact h1 (conj (1 - s)) (by simp; linarith)

/-- Under a functional equation, nonvanishing of the entire completion on `1 ≤ Re s` confines all
zeros of `d.entireCompletion` to the open critical strip `0 < Re ρ < 1`. -/
theorem HasFunctionalEquation.re_mem_Ioo_of_entireCompletion_eq_zero
    (hfe : d.HasFunctionalEquation) (h1 : ∀ z : ℂ, 1 ≤ z.re → d.entireCompletion z ≠ 0)
    {ρ : ℂ} (hρ : d.entireCompletion ρ = 0) : ρ.re ∈ Set.Ioo 0 1 := by
  refine ⟨?_, ?_⟩
  · by_contra hle
    exact hfe.entireCompletion_ne_zero_of_re_nonpos h h1 (not_lt.mp hle) hρ
  · by_contra hle
    exact h1 ρ (not_lt.mp hle) hρ

end TauCeti.LFunctions.AnalyticLFunctionData
