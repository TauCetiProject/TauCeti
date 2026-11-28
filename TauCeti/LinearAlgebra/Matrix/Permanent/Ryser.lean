/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permanent
import TauCeti.Data.Finset.Basic

/-!
# Ryser's formula for the permanent

Ryser's formula writes the permanent of a square matrix `A` over a commutative ring, with
`n` indices, as an alternating sum over the subsets `S` of the column indices:
`perm A = ∑_S (-1) ^ (n - |S|) ∏_i ∑_{j ∈ S} A i j`. Each of the `2 ^ n` terms is a product of
row sums, while the definition of the permanent has `n!` terms.

The proof expands each product of row sums as a sum over all maps `φ` of the index type to
itself. By inclusion-exclusion, the coefficient of `φ` is `1` if `φ` is surjective and `0`
otherwise, and a surjective self-map of a finite type is a permutation.

## Main declarations

* `Matrix.permanent_eq_sum_surjective`: the permanent is the sum of `∏ i, A i (φ i)` over the
  surjective maps `φ`.
* `Matrix.permanent_eq_sum_powerset_compl`: the permanent is `∑_T (-1) ^ |T| ∏_i ∑_{j ∉ T} A i j`.
* `Matrix.permanent_eq_sum_powerset`: Ryser's formula.

## References

* H. J. Ryser, *Combinatorial Mathematics*.
* P. Bürgisser, *Completeness classes in algebraic complexity theory*, arXiv:2406.06217v1
  (2024), (2.3), p. 12, states the formula with complements.
* A. Shpilka and A. Yehudayoff, *Arithmetic circuits: a survey of recent results and open
  questions*, Foundations and Trends in Theoretical Computer Science 5 (2010), Fact 1.1, p. 4.
-/

public section

open Finset

namespace Matrix

variable {R n : Type*} [Fintype n] [DecidableEq n]

/-- The permanent is the sum of `∏ i, A i (φ i)` over the surjective maps `φ` of the index type
to itself. These maps are exactly the permutations. -/
theorem permanent_eq_sum_surjective [CommSemiring R] (A : Matrix n n R) :
    A.permanent = ∑ φ : n → n with Function.Surjective φ, ∏ i, A i (φ i) := by
  rw [← permanent_transpose, permanent, sum_subtype (p := Function.Surjective) _ (by simp)]
  exact Fintype.sum_equiv ((Equiv.subtypeEquivRight fun φ : n → n ↦
    Finite.surjective_iff_bijective).trans Equiv.bijectiveEquiv).symm
    (fun σ : Equiv.Perm n ↦ ∏ i, Aᵀ (σ i) i) (fun φ ↦ ∏ i, A i (φ.val i)) fun σ ↦ by simp

/-- The permanent as an alternating sum over the subsets `T` of the column indices, with the
row sums taken over the complement of `T`: `perm A = ∑_T (-1) ^ |T| ∏_i ∑_{j ∉ T} A i j`. -/
theorem permanent_eq_sum_powerset_compl [CommRing R] (A : Matrix n n R) :
    A.permanent = ∑ T : Finset n, (-1) ^ #T * ∏ i, ∑ j ∈ Tᶜ, A i j := by
  have hrow (T : Finset n) (i : n) :
      ∑ j ∈ Tᶜ, A i j = ∑ j, if j ∉ T then A i j else 0 := by
    rw [← sum_filter]
    congr 1
    ext
    simp
  -- The coefficient of a map `φ` after the expansion of the products of row sums.
  have hcoeff (φ : n → n) : ∑ T : Finset n, (if ∀ i, φ i ∉ T then (-1 : R) ^ #T else 0) =
      if Function.Surjective φ then 1 else 0 := by
    have hT : univ.filter (fun T : Finset n ↦ ∀ i, φ i ∉ T) = (univ.image φ)ᶜ.powerset := by
      ext T
      simp only [mem_filter, mem_univ, true_and, mem_powerset, subset_iff, mem_compl, mem_image,
        not_exists]
      exact ⟨fun h a ha x hx ↦ h x (hx ▸ ha), fun h i hi ↦ h hi i rfl⟩
    rw [← sum_filter, hT, sum_powerset_neg_one_pow_card_of_ring]
    exact if_congr (by simp [compl_eq_empty_iff, eq_univ_iff_forall, Function.Surjective]) rfl rfl
  simp_rw [hrow, Fintype.prod_sum, Fintype.prod_ite_zero, mul_sum]
  rw [sum_comm, permanent_eq_sum_surjective, sum_filter]
  refine sum_congr rfl fun φ _ ↦ ?_
  trans (if Function.Surjective φ then (1 : R) else 0) * ∏ i, A i (φ i)
  · simp [ite_mul]
  rw [← hcoeff, sum_mul]
  refine sum_congr rfl fun T _ ↦ ?_
  split_ifs <;> simp

/-- **Ryser's formula**: for a square matrix `A` over a commutative ring with `n` indices,
`perm A = ∑_S (-1) ^ (n - |S|) ∏_i ∑_{j ∈ S} A i j`. -/
theorem permanent_eq_sum_powerset [CommRing R] (A : Matrix n n R) :
    A.permanent = ∑ S : Finset n, (-1) ^ (Fintype.card n - #S) * ∏ i, ∑ j ∈ S, A i j := by
  rw [permanent_eq_sum_powerset_compl, ← Equiv.sum_comp (compl_involutive.toPerm _)]
  simp [card_compl, compl_compl]

end Matrix
