/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Degrees
public import TauCeti.Algebra.BigOperators.ProperFace

/-!
# Proper-face polynomials

For a finite index type `ι` and coefficients `c : Finset ι → R`, the *proper-face polynomial*
`∑_{s ⊊ ι} C(c_s) ∏_{i ∈ s} X_i` is the `MvPolynomial` whose evaluation is the proper-face sum
`TauCeti.properFaceSum c`. Its monomials are the squarefree monomials `∏_{i ∈ s} X_i` for proper
subsets `s`, so the top monomial `∏_i X_i` is missing.

## Main definitions

* `TauCeti.properFacePolynomial c`: the proper-face polynomial.

## Main results

* `TauCeti.eval_properFacePolynomial`: evaluation gives the proper-face sum.
* `TauCeti.properFacePolynomial_add`, `TauCeti.properFacePolynomial_smul`,
  `TauCeti.properFacePolynomial_sum`: linearity in the coefficients.
* `TauCeti.coeff_properFacePolynomial`, `TauCeti.coeff_sum_single_properFacePolynomial`,
  `TauCeti.coeff_sum_univ_single_properFacePolynomial`: the coefficients; in particular the top
  monomial has coefficient zero.
* `TauCeti.totalDegree_properFacePolynomial_le`, `TauCeti.degreeOf_properFacePolynomial_le`:
  total degree at most `|ι| - 1` and degree at most one in each variable.

## References

* Weibo Fu, *Sharp bounds for multiplicities of Bianchi modular forms*, Ann. of Math. 200
  (2024), 123–152; arXiv:2201.11190, Theorem 1.2, Theorem 1.4 and §§6–7.
-/

public section

namespace TauCeti

open Finset MvPolynomial

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- The `MvPolynomial` `∑_{s ⊊ ι} C(c_s) ∏_{i ∈ s} X_i` whose evaluation is the proper-face sum
`properFaceSum c`. -/
noncomputable def properFacePolynomial (c : Finset ι → R) : MvPolynomial ι R :=
  ∑ s ∈ (univ : Finset ι).ssubsets, C (c s) * ∏ i ∈ s, X i

theorem properFacePolynomial_def (c : Finset ι → R) :
    properFacePolynomial c = ∑ s ∈ (univ : Finset ι).ssubsets, C (c s) * ∏ i ∈ s, X i := by
  rw [properFacePolynomial]

@[simp]
theorem eval_properFacePolynomial (c : Finset ι → R) (x : ι → R) :
    eval x (properFacePolynomial c) = properFaceSum c x := by
  simp [properFacePolynomial, properFaceSum_def]

@[simp]
theorem properFacePolynomial_zero : properFacePolynomial (0 : Finset ι → R) = 0 := by
  simp [properFacePolynomial]

@[simp]
theorem properFacePolynomial_add (c d : Finset ι → R) :
    properFacePolynomial (c + d) = properFacePolynomial c + properFacePolynomial d := by
  simp [properFacePolynomial, add_mul, sum_add_distrib]

@[simp]
theorem properFacePolynomial_smul (a : R) (c : Finset ι → R) :
    properFacePolynomial (a • c) = a • properFacePolynomial c := by
  simp [properFacePolynomial, smul_sum, smul_eq_C_mul, mul_assoc]

@[simp]
theorem properFacePolynomial_sum {α : Type*} (t : Finset α) (c : α → Finset ι → R) :
    properFacePolynomial (∑ j ∈ t, c j) = ∑ j ∈ t, properFacePolynomial (c j) := by
  simp only [properFacePolynomial, Finset.sum_apply, map_sum, sum_mul]
  exact sum_comm

/-- A single coefficient at a proper subset `s` contributes exactly `C a * ∏_{i ∈ s} X_i`; at
the full subset it contributes nothing. -/
theorem properFacePolynomial_single (s : Finset ι) (a : R) :
    properFacePolynomial (Pi.single s a) = if s = univ then 0 else C a * ∏ i ∈ s, X i := by
  rw [properFacePolynomial]
  split_ifs with hs
  · exact sum_eq_zero fun t ht ↦ by
      rw [Pi.single_eq_of_ne (hs ▸ (mem_ssubsets.1 ht).ne), C_0, zero_mul]
  · rw [sum_eq_single_of_mem s (mem_ssubsets.2 (ssubset_univ_iff.2 hs)) fun t _ hts ↦ by
      rw [Pi.single_eq_of_ne hts, C_0, zero_mul], Pi.single_eq_same]

/-- The coefficient at the full subset does not affect the proper-face polynomial. -/
@[simp]
theorem properFacePolynomial_update_univ (c : Finset ι → R) (a : R) :
    properFacePolynomial (Function.update c univ a) = properFacePolynomial c :=
  sum_congr rfl fun s hs ↦ by rw [Function.update_of_ne (mem_ssubsets.1 hs).ne]

/-- The coefficient of a monomial `m` in a proper-face polynomial is the sum of the
coefficients `c_s` over the proper subsets `s` with `m = ∑_{i ∈ s} e_i`. -/
theorem coeff_properFacePolynomial (m : ι →₀ ℕ) (c : Finset ι → R) :
    (properFacePolynomial c).coeff m =
      ∑ s ∈ (univ : Finset ι).ssubsets with ∑ i ∈ s, Finsupp.single i 1 = m, c s := by
  simp only [properFacePolynomial, coeff_sum, X, ← monomial_sum_index, coeff_monomial,
    sum_filter]

/-- The coefficient of the squarefree monomial `∏_{i ∈ s} X_i` in a proper-face polynomial is
`c_s` for a proper subset `s` and zero for `s = univ`. -/
theorem coeff_sum_single_properFacePolynomial (s : Finset ι) (c : Finset ι → R) :
    (properFacePolynomial c).coeff (∑ i ∈ s, Finsupp.single i 1) =
      if s = univ then 0 else c s := by
  have hinj : ∀ t : Finset ι,
      ∑ i ∈ t, Finsupp.single i 1 = ∑ i ∈ s, Finsupp.single i 1 ↔ t = s := fun t ↦ by
    refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
    ext j
    have := congr($h j)
    simp only [Finset.sum_apply', Finsupp.single_apply, sum_ite_eq'] at this
    split_ifs at this <;> simp_all
  rw [coeff_properFacePolynomial]
  simp only [hinj, filter_eq', mem_ssubsets, ssubset_univ_iff]
  split_ifs <;> simp_all

/-- The top monomial `∏_i X_i` does not occur in a proper-face polynomial. -/
@[simp]
theorem coeff_sum_univ_single_properFacePolynomial (c : Finset ι → R) :
    (properFacePolynomial c).coeff (∑ i, Finsupp.single i 1) = 0 := by
  simp [coeff_sum_single_properFacePolynomial]

/-- A proper-face polynomial has total degree at most `|ι| - 1`. -/
theorem totalDegree_properFacePolynomial_le (c : Finset ι → R) :
    (properFacePolynomial c).totalDegree ≤ Fintype.card ι - 1 := by
  rcases subsingleton_or_nontrivial R with _ | _
  · simp [Subsingleton.elim (properFacePolynomial c) 0]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs ↦ ?_)
  have hcard : #s < Fintype.card ι := card_univ (α := ι) ▸ card_lt_card (mem_ssubsets.1 hs)
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  simp only [totalDegree_X, sum_const, smul_eq_mul, mul_one]
  omega

/-- A proper-face polynomial has degree at most one in each variable. -/
theorem degreeOf_properFacePolynomial_le (c : Finset ι → R) (i : ι) :
    (properFacePolynomial c).degreeOf i ≤ 1 := by
  rcases subsingleton_or_nontrivial R with _ | _
  · simp [Subsingleton.elim (properFacePolynomial c) 0]
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun s _ ↦ ?_)
  refine (degreeOf_C_mul_le _ _ _).trans ((degreeOf_prod_le _ _ _).trans ?_)
  simp only [degreeOf_X]
  rw [sum_ite_eq]
  split_ifs <;> omega

end TauCeti
