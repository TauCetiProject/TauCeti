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
vanishing conditions. The weight bound also gives vanishing for Hasse derivatives, with a
loss proportional to the normalized order of differentiation.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace theorem*,
  Ann. of Math. 177 (2013), §13, Lemma 13.5 and the differentiation argument in Proposition 13.6.
-/

public section

open Finset

namespace MvPolynomial

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

/-- In finitely many coordinate systems the high-weight coefficients can simultaneously be
made zero in a nonzero polynomial of multidegree `r`, provided the exponential budget from
the support count is met. All exponent vectors above the thresholds are covered, since those
outside `multiMons ι r` have zero coefficients by multihomogeneity. -/
theorem exists_ne_zero_isMultiHomogeneous_forall_coeff_blockSubst_eq_zero_of_weight_gt
    [DecidableEq κ] {K ν : Type*} [Field K] [Fintype ν] [Nonempty ι] (A : ν → Matrix ι ι K)
    {r : κ → ℕ} (hr : ∀ h, 0 < r h) {w : ν → κ → ι → ℝ} {γ θ : ν → ℝ} {ε : ℝ}
    (hγ : ∀ v, 0 < γ v) (hw : ∀ v h i, |w v h i| ≤ γ v) (hε : 0 ≤ ε)
    (hθ : ∀ v, (∑ h, (∑ i, w v h i) / Fintype.card ι) +
      Fintype.card κ * γ v * ε ≤ θ v)
    (hbudget : 2 * (Fintype.card ν : ℝ) ≤ Real.exp (Fintype.card κ * ε ^ 2 / 2)) :
    ∃ P : MvPolynomial (κ × ι) K, P ≠ 0 ∧ IsMultiHomogeneous r P ∧ ∀ v n,
      θ v < n.weight (fun p ↦ w v p.1 p.2 / r p.1) → (blockSubst (A v) P).coeff n = 0 := by
  classical
  let S := multiMons ι r
  let B (v : ν) := S.filter fun n ↦ θ v < n.weight (fun p ↦ w v p.1 p.2 / r p.1)
  let writePoly := Fintype.linearCombination K fun n : S ↦ monomial n.val (1 : K)
  let conditions : (S → K) →ₗ[K] ((Σ v, B v) → K) := LinearMap.pi fun q ↦
    lcoeff K q.2.val ∘ₗ (blockSubst (A q.1)).toLinearMap ∘ₗ writePoly
  have hcount : 2 * (∑ v, #(B v)) ≤ #S :=
    two_mul_sum_card_filter_multiMons_weight_gt_le hr hγ hw hε hθ hbudget
  have hS : 0 < #S := by
    rw [card_multiMons]
    exact prod_pos fun h _ ↦ Nat.choose_pos (by have := Fintype.card_pos (α := ι); omega)
  have hdim : Module.finrank K ((Σ v, B v) → K) < Module.finrank K (S → K) := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sigma, Fintype.card_coe]
    omega
  obtain ⟨c, hc, hc₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := conditions) hdim)
  have hmono : LinearIndependent K (fun n : S ↦ monomial n.val (1 : K)) :=
    (basisMonomials (κ × ι) K).linearIndependent.comp Subtype.val Subtype.val_injective
  have hinj : Function.Injective writePoly := hmono.fintypeLinearCombination_injective
  have hhom : IsMultiHomogeneous r (writePoly c) := by
    rw [Fintype.linearCombination_apply]
    refine IsMultiHomogeneous.sum _ _ fun n _ ↦ ?_
    rw [smul_eq_C_mul]
    exact (isMultiHomogeneous_monomial (mem_multiMons.1 n.property) 1).C_mul _
  refine ⟨writePoly c, fun h ↦ hc₀ (hinj (h.trans (map_zero writePoly).symm)),
    hhom, fun v n hn ↦ ?_⟩
  by_cases hm : n ∈ S
  · have h := congrFun (LinearMap.mem_ker.1 hc) (⟨v, ⟨n, mem_filter.2 ⟨hm, hn⟩⟩⟩ : Σ v, B v)
    simpa only [conditions, LinearMap.pi_apply, LinearMap.comp_apply, lcoeff_apply,
      AlgHom.toLinearMap_apply, Pi.zero_apply] using h
  · exact notMem_support_iff.1 fun hs ↦ hm
      (isMultiHomogeneous_iff_support_subset.1 (hhom.blockSubst (A v)) hs)

/-- If high-weight coefficients of a polynomial in the coordinates of `A` vanish, the same
holds for a Hasse derivative above the old threshold plus `γ` times the normalized order.
The bound uses the same block degrees to normalize the derivative and the original polynomial. -/
theorem coeff_blockSubst_inv_hasseDeriv_eq_zero_of_weight_gt {K : Type*} [CommRing K]
    [DecidableEq ι]
    {A : Matrix ι ι K} (hA : IsUnit A.det) {P : MvPolynomial (κ × ι) K} {r : κ → ℕ}
    {w : κ → ι → ℝ} {γ θ : ℝ} (hw : ∀ h i, -γ ≤ w h i)
    (hP : ∀ n : κ × ι →₀ ℕ, θ < n.weight (fun p ↦ w p.1 p.2 / r p.1) →
      (blockSubst A⁻¹ P).coeff n = 0) {I J : κ × ι →₀ ℕ}
    (hJ : θ + γ * (∑ h, ((∑ i, I (h, i) : ℕ) : ℝ) / r h) <
      J.weight (fun p ↦ w p.1 p.2 / r p.1)) :
    (blockSubst A⁻¹ (hasseDeriv I P)).coeff J = 0 := by
  classical
  refine coeff_blockSubst_hasseDeriv_eq_zero_of_forall_coeff_add hA fun e he ↦ hP (J + e) ?_
  have hshift : -γ * (∑ h, ((∑ i, I (h, i) : ℕ) : ℝ) / r h) ≤
      e.weight (fun p ↦ w p.1 p.2 / r p.1) := by
    rw [mul_sum, Finsupp.weight_prod_div_eq_sum]
    refine sum_le_sum fun h _ ↦ ?_
    rw [← he h, Nat.cast_sum, ← mul_div_assoc, mul_sum]
    refine div_le_div_of_nonneg_right (sum_le_sum fun i _ ↦ ?_) (Nat.cast_nonneg _)
    rw [mul_comm (-γ)]
    exact mul_le_mul_of_nonneg_left (hw h i) (Nat.cast_nonneg _)
  rw [map_add]
  linarith

end MvPolynomial
