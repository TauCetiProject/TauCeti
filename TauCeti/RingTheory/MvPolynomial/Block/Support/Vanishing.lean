/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Block.Support.Count
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.BlockSubst
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Multihomogeneous polynomials with simultaneous weight constraints

If high-weight monomials in several block coordinate systems impose fewer equations than
there are monomials of the given multidegree, a nonzero polynomial satisfies all the coefficient
vanishing conditions. For bounded weights and thresholds at least the corresponding means plus
the prescribed deviations, the exponential support count provides a sufficient budget.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace theorem*,
  Ann. of Math. 177 (2013), §13, Lemma 13.5.
-/

public section

open Finset

open MvPolynomial

namespace TauCeti

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- If the number of selected coefficient positions across the block substitutions is less than
the number of monomials of multidegree `r`, there is a nonzero polynomial of that multidegree
whose coefficients at those positions vanish in each substitution. -/
theorem exists_ne_zero_isMultiHomogeneous_forall_coeff_blockSubst_eq_zero
    [DecidableEq κ] [DecidableEq ι] {K ν : Type*} [Field K] [Fintype ν] (A : ν → Matrix ι ι K)
    {r : κ → ℕ} (B : ν → Finset (κ × ι →₀ ℕ)) (hcount : ∑ v, #(B v) < #(multiMons ι r)) :
    ∃ P : MvPolynomial (κ × ι) K, P ≠ 0 ∧ IsMultiHomogeneous r P ∧
      ∀ v n, n ∈ B v → (blockSubst (A v) P).coeff n = 0 := by
  classical
  let S := multiMons ι r
  let V := restrictSupport K (↑S : Set (κ × ι →₀ ℕ))
  let b := basisRestrictSupport K (↑S : Set (κ × ι →₀ ℕ))
  have : FiniteDimensional K V := Module.Finite.of_basis b
  let conditions : V →ₗ[K] ((Σ v, B v) → K) := LinearMap.pi fun q ↦
    lcoeff K q.2.val ∘ₗ (blockSubst (A q.1)).toLinearMap ∘ₗ V.subtype
  have hdim : Module.finrank K ((Σ v, B v) → K) < Module.finrank K V := by
    rw [Module.finrank_eq_nat_card_basis b, Nat.card_coe_set_eq, Set.ncard_coe_finset]
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma, Fintype.card_coe] using
      hcount
  obtain ⟨P, hP, hP₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := conditions) hdim)
  refine ⟨P.val, fun h ↦ hP₀ (Subtype.ext h),
    isMultiHomogeneous_iff_support_subset.2 ((mem_restrictSupport_iff K).1 P.property), ?_⟩
  intro v n hn
  have h := congrFun (LinearMap.mem_ker.1 hP) (⟨v, ⟨n, hn⟩⟩ : Σ v, B v)
  simpa only [conditions, LinearMap.pi_apply, LinearMap.comp_apply, lcoeff_apply,
    AlgHom.toLinearMap_apply, Submodule.subtype_apply, Pi.zero_apply] using h

/-- If the weights are bounded by `γ v` in absolute value and each threshold is at least its
mean plus the deviation, the exponential budget guarantees a nonzero polynomial of multidegree
`r` whose coefficients above those thresholds vanish after each block substitution.
Exponents outside `multiMons ι r` have zero coefficients by multihomogeneity. -/
theorem exists_ne_zero_isMultiHomogeneous_forall_coeff_blockSubst_eq_zero_of_weight_gt
    [DecidableEq κ] {K ν : Type*} [Field K] [Fintype ν] [Nonempty ι] (A : ν → Matrix ι ι K)
    {r : κ → ℕ} (hr : ∀ h, 0 < r h) {w : ν → κ → ι → ℝ} {γ θ : ν → ℝ} {ε : ℝ}
    (hγ : ∀ v, 0 ≤ γ v) (hw : ∀ v h i, |w v h i| ≤ γ v) (hε : 0 ≤ ε)
    (hθ : ∀ v, (∑ h, (∑ i, w v h i) / Fintype.card ι) +
      Fintype.card κ * γ v * ε ≤ θ v)
    (hbudget : 2 * (Fintype.card ν : ℝ) ≤ Real.exp (Fintype.card κ * ε ^ 2 / 2)) :
    ∃ P : MvPolynomial (κ × ι) K, P ≠ 0 ∧ IsMultiHomogeneous r P ∧ ∀ v n,
      θ v < n.weight (fun p ↦ w v p.1 p.2 / r p.1) → (blockSubst (A v) P).coeff n = 0 := by
  classical
  let B (v : ν) := (multiMons ι r).filter fun n ↦
    θ v < n.weight (fun p ↦ w v p.1 p.2 / r p.1)
  have hcount : 2 * (∑ v, #(B v)) ≤ #(multiMons ι r) :=
    two_mul_sum_card_filter_multiMons_weight_gt_le hr hγ hw hε hθ hbudget
  have hS : 0 < #(multiMons ι r) := by
    rw [card_multiMons]
    exact prod_pos fun h _ ↦ Nat.choose_pos (by have := Fintype.card_pos (α := ι); omega)
  obtain ⟨P, hP, hhom, hcoeff⟩ :=
    exists_ne_zero_isMultiHomogeneous_forall_coeff_blockSubst_eq_zero A (r := r) B (by omega)
  refine ⟨P, hP, hhom, fun v n hn ↦ ?_⟩
  by_cases hm : n ∈ multiMons ι r
  · exact hcoeff v n (mem_filter.2 ⟨hm, hn⟩)
  · exact notMem_support_iff.1 fun hs ↦ hm
      (isMultiHomogeneous_iff_support_subset.1 (hhom.blockSubst (A v)) hs)

end TauCeti
