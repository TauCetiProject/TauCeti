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

Conjugation carries the polar polynomial and entire completion of `d` to those of `d.dual`. Under a
functional equation, substituting `1 - s` into the polar polynomial multiplies the dual polar
polynomial by `(-1) ^ deg`, extending the functional equation across cleared poles as
`Λ₀(d, 1 - s) = (-1) ^ deg · ε(d) · Λ₀(d^∨, s)` and
`Λ₀(d, 1 - conj s) = (-1) ^ deg · ε(d) · conj (Λ₀(d, s))`. Differentiating logarithmically cancels
the nonzero constant prefactor, giving `Λ₀'/Λ₀(d, 1 - s) = -Λ₀'/Λ₀(d^∨, s)` and
`Λ₀'/Λ₀(d, 1 - conj s) = -conj (Λ₀'/Λ₀(d, s))` everywhere, while `s ↦ 1 - conj s` preserves the
meromorphic, analytic, and divisor orders of `Λ₀(d)`.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §11–12.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §10.2.
-/

public section

open Complex ComplexConjugate Filter Topology Polynomial
open scoped BigOperators

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

/-- The degree of the polar polynomial is the total multiplicity of all recorded poles. -/
theorem natDegree_polarPolynomial :
    d.polarPolynomial.natDegree = ∑ p ∈ d.polarOrder.support, d.polarOrder p := by
  classical
  rw [polarPolynomial_def, Finsupp.prod,
    Polynomial.natDegree_prod_of_monic _ _ (fun p _ ↦ (monic_X_sub_C p).pow _)]
  simp

/-- The polar polynomial of the dual card has the same degree as that of `d`. -/
@[simp]
theorem natDegree_dual_polarPolynomial :
    d.dual.polarPolynomial.natDegree = d.polarPolynomial.natDegree := by
  classical
  let e : ℂ ≃ ℂ := ⟨conj, conj, Complex.conj_conj, Complex.conj_conj⟩
  rw [natDegree_polarPolynomial, natDegree_polarPolynomial]
  refine (Finset.sum_equiv e ?_ ?_).symm
  · intro p
    simp [e, Finsupp.mem_support_iff]
  · intro p _
    simp [e]

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

/-- Under a functional equation, evaluating the polar polynomial at `1 - s` multiplies evaluation of
the dual polar polynomial at `s` by `(-1) ^ d.polarPolynomial.natDegree`. -/
theorem HasFunctionalEquation.polarPolynomial_eval_one_sub {d : AnalyticLFunctionData}
    (hfe : d.HasFunctionalEquation) (s : ℂ) :
    d.polarPolynomial.eval (1 - s) =
      (-1 : ℂ) ^ d.polarPolynomial.natDegree * d.dual.polarPolynomial.eval s := by
  classical
  let e : ℂ ≃ ℂ :=
    ⟨fun p ↦ 1 - p, fun p ↦ 1 - p, fun p ↦ sub_sub_cancel 1 p, fun p ↦ sub_sub_cancel 1 p⟩
  have hmem (p : ℂ) : p ∈ d.polarOrder.support ↔ e p ∈ d.dual.polarOrder.support := by
    simp [e, Finsupp.mem_support_iff, ← hfe.polarOrder_one_sub]
  rw [polarPolynomial_eval, polarPolynomial_eval, ← natDegree_dual_polarPolynomial,
    natDegree_polarPolynomial, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_equiv e hmem fun p _ ↦ ?_
  simp only [e, Equiv.coe_fn_mk, ← hfe.polarOrder_one_sub, sub_sub_cancel, ← mul_pow]
  congr 1
  ring

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

/-! ### Conjugation and functional equation of the entire completion -/

/-- The entire completion of the dual card is `conj ∘ d.entireCompletion ∘ conj`, including at
cleared poles. -/
theorem HasMeromorphicContinuation.dual_entireCompletion :
    d.dual.entireCompletion = conj ∘ d.entireCompletion ∘ conj := by
  symm
  refine h.dual.entireCompletion_unique ?_ fun z hz ↦ ?_
  · exact continuous_conj.comp (h.differentiable_entireCompletion.continuous.comp continuous_conj)
  · rw [dual_polarOrder_apply] at hz
    simp only [Function.comp_apply, h.entireCompletion_eq hz, map_mul, ← dual_polarPolynomial_eval,
      ← dual_completed_apply]

/-- Pointwise form of `HasMeromorphicContinuation.dual_entireCompletion`. -/
theorem HasMeromorphicContinuation.dual_entireCompletion_apply (s : ℂ) :
    d.dual.entireCompletion s = conj (d.entireCompletion (conj s)) :=
  congrFun h.dual_entireCompletion s

/-- Reflection across the real axis conjugates the entire completion into that of the dual card. -/
theorem HasMeromorphicContinuation.dual_entireCompletion_conj (s : ℂ) :
    d.dual.entireCompletion (conj s) = conj (d.entireCompletion s) := by
  rw [h.dual_entireCompletion_apply, Complex.conj_conj]

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

/-- Reflection `s ↦ 1 - conj s` conjugates the entire completion and multiplies by
`(-1) ^ d.polarPolynomial.natDegree * d.rootNumber`. -/
theorem HasFunctionalEquation.entireCompletion_one_sub_conj (hfe : d.HasFunctionalEquation)
    (s : ℂ) :
    d.entireCompletion (1 - conj s) =
      (-1 : ℂ) ^ d.polarPolynomial.natDegree * d.rootNumber * conj (d.entireCompletion s) := by
  rw [hfe.entireCompletion_one_sub h, h.dual_entireCompletion_conj]

/-- Under a functional equation, `d.entireCompletion` vanishes at `1 - conj s` if and only if it
vanishes at `s`. -/
theorem HasFunctionalEquation.entireCompletion_one_sub_conj_eq_zero_iff
    (hfe : d.HasFunctionalEquation) (s : ℂ) :
    d.entireCompletion (1 - conj s) = 0 ↔ d.entireCompletion s = 0 := by
  have hc : (-1 : ℂ) ^ d.polarPolynomial.natDegree * d.rootNumber ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num))
      (norm_ne_zero_iff.mp (by simp [hfe.norm_rootNumber]))
  rw [hfe.entireCompletion_one_sub_conj h, mul_eq_zero_iff_left hc, map_eq_zero]

/-- Under a functional equation, `d.entireCompletion` vanishes at `1` if and only if it vanishes at
`0`. -/
theorem HasFunctionalEquation.entireCompletion_one_eq_zero_iff (hfe : d.HasFunctionalEquation) :
    d.entireCompletion 1 = 0 ↔ d.entireCompletion 0 = 0 := by
  simpa using hfe.entireCompletion_one_sub_conj_eq_zero_iff h 0

/-- Nonvanishing of the entire completion at `0` transfers to `1` under a functional equation. -/
theorem HasFunctionalEquation.entireCompletion_one_ne_zero (hfe : d.HasFunctionalEquation)
    (h0 : d.entireCompletion 0 ≠ 0) : d.entireCompletion 1 ≠ 0 :=
  (hfe.entireCompletion_one_eq_zero_iff h).not.mpr h0

/-! ### Symmetries of the orders and logarithmic derivative -/

/-- Reflection across the real axis carries the orders of the entire completion at `s` to those
of the entire completion of the dual card at `conj s`. -/
theorem HasMeromorphicContinuation.meromorphicOrderAt_dual_entireCompletion_conj (s : ℂ) :
    meromorphicOrderAt d.dual.entireCompletion (conj s) =
      meromorphicOrderAt d.entireCompletion s := by
  rw [h.dual.meromorphicOrderAt_entireCompletion, h.meromorphicOrderAt_entireCompletion,
    dual_completed, TauCeti.meromorphicOrderAt_conj_conj, dual_polarOrder_apply,
    Complex.conj_conj]

/-- Reflection across the real axis carries the analytic order of the entire completion at `s` to
that of the dual card at `conj s`. -/
theorem HasMeromorphicContinuation.analyticOrderAt_dual_entireCompletion_conj (s : ℂ) :
    analyticOrderAt d.dual.entireCompletion (conj s) = analyticOrderAt d.entireCompletion s := by
  have hm := h.meromorphicOrderAt_dual_entireCompletion_conj s
  rw [(h.dual.analyticAt_entireCompletion _).meromorphicOrderAt_eq,
    (h.analyticAt_entireCompletion _).meromorphicOrderAt_eq] at hm
  exact ENat.map_natCast_injective hm

/-- Reflection across the real axis carries the natural zero multiplicity of the entire completion
at `s` to that of the dual card at `conj s`. -/
theorem HasMeromorphicContinuation.analyticOrderNatAt_dual_entireCompletion_conj (s : ℂ) :
    analyticOrderNatAt d.dual.entireCompletion (conj s) =
      analyticOrderNatAt d.entireCompletion s :=
  congrArg ENat.toNat (h.analyticOrderAt_dual_entireCompletion_conj s)

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

/-- The functional equation carries the analytic order of the dual entire completion at `s` to that
of `d.entireCompletion` at `1 - s`. -/
theorem HasFunctionalEquation.analyticOrderAt_entireCompletion_one_sub
    (hfe : d.HasFunctionalEquation) (s : ℂ) :
    analyticOrderAt d.entireCompletion (1 - s) = analyticOrderAt d.dual.entireCompletion s := by
  have hm := hfe.meromorphicOrderAt_entireCompletion_one_sub h s
  rw [(h.analyticAt_entireCompletion _).meromorphicOrderAt_eq,
    (h.dual.analyticAt_entireCompletion _).meromorphicOrderAt_eq] at hm
  exact ENat.map_natCast_injective hm

/-- The functional equation carries the natural zero multiplicity of the dual entire completion at
`s` to that of `d.entireCompletion` at `1 - s`. -/
theorem HasFunctionalEquation.analyticOrderNatAt_entireCompletion_one_sub
    (hfe : d.HasFunctionalEquation) (s : ℂ) :
    analyticOrderNatAt d.entireCompletion (1 - s) =
      analyticOrderNatAt d.dual.entireCompletion s :=
  congrArg ENat.toNat (hfe.analyticOrderAt_entireCompletion_one_sub h s)

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

/-- Reflection `s ↦ 1 - conj s` preserves the analytic order of the entire completion. -/
theorem HasFunctionalEquation.analyticOrderAt_entireCompletion_one_sub_conj
    (hfe : d.HasFunctionalEquation) (s : ℂ) :
    analyticOrderAt d.entireCompletion (1 - conj s) = analyticOrderAt d.entireCompletion s := by
  rw [hfe.analyticOrderAt_entireCompletion_one_sub h, h.analyticOrderAt_dual_entireCompletion_conj]

/-- Reflection `s ↦ 1 - conj s` preserves the natural zero multiplicity of the entire completion. -/
theorem HasFunctionalEquation.analyticOrderNatAt_entireCompletion_one_sub_conj
    (hfe : d.HasFunctionalEquation) (s : ℂ) :
    analyticOrderNatAt d.entireCompletion (1 - conj s) =
      analyticOrderNatAt d.entireCompletion s :=
  congrArg ENat.toNat (hfe.analyticOrderAt_entireCompletion_one_sub_conj h s)

/-- The reflection `s ↦ 1 - conj s` preserves the divisor of the entire completion. -/
theorem HasFunctionalEquation.divisor_entireCompletion_one_sub_conj
    (hfe : d.HasFunctionalEquation) (s : ℂ) :
    MeromorphicOn.divisor d.entireCompletion Set.univ (1 - conj s) =
      MeromorphicOn.divisor d.entireCompletion Set.univ s := by
  rw [hfe.divisor_entireCompletion_one_sub h, h.divisor_dual_entireCompletion_conj]

/-- Conjugation carries the logarithmic derivative of the entire completion to that of the dual
card. -/
theorem HasMeromorphicContinuation.logDeriv_dual_entireCompletion_conj (s : ℂ) :
    logDeriv d.dual.entireCompletion (conj s) = conj (logDeriv d.entireCompletion s) := by
  rw [h.dual_entireCompletion, logDeriv_apply, logDeriv_apply, deriv_conj_conj]
  simp

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

end TauCeti.LFunctions.AnalyticLFunctionData
