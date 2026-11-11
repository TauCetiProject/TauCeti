/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Identifying polynomials in the elementary symmetric functions

Mathlib's fundamental theorem of symmetric polynomials, `MvPolynomial.esymmAlgHom_injective`,
says that substituting the elementary symmetric polynomials `e₁, …, eₙ` of the variables of `σ`
into polynomials in `n` variables is injective when `n ≤ card σ`. This file restates it with the
elementary symmetric polynomials written as `Multiset.esymm` of the multiset of variables. In this
form, an identity between polynomials in `e₁, …, eₙ` follows from the same identity between
values at the elementary symmetric functions of a multiset of roots, specialized to the
variables. It also restates the theorem as the algebraic independence of `e₁, …, eₙ`, the form in
which it combines with other algebraically independent families.

Over an infinite integral domain a polynomial is moreover determined by its values, so a
polynomial `P` in variables `X 1, …, X n` vanishes as soon as it vanishes at the elementary
symmetric functions `e₁(p), …, eₙ(p)` of every family `p : Fin n → K`.

## Main results

* `MvPolynomial.aeval_multiset_esymm_X_injective`: substituting the elementary symmetric
  functions of the multiset of variables is injective.
* `MvPolynomial.eq_zero_of_aeval_esymm_eq_zero`: a polynomial in the variables `X 1, …, X n` that
  vanishes at the elementary symmetric functions of every `n`-tuple is zero.
* `MvPolynomial.algebraicIndependent_esymm`: the elementary symmetric polynomials `e₁, …, eₙ` are
  algebraically independent when `n ≤ card σ`.
-/

public section

open Finset

namespace MvPolynomial

/-- **Fundamental theorem of symmetric polynomials**, root form: if `n ≤ card σ`, a polynomial in
`n` variables is determined by its value at the elementary symmetric functions
`e₁, …, eₙ` of the multiset of variables of `σ`. -/
theorem aeval_multiset_esymm_X_injective (R : Type*) [CommRing R] {σ : Type*} [Fintype σ]
    {n : ℕ} (hn : n ≤ Fintype.card σ) :
    Function.Injective
      (aeval (R := R) fun j : Fin n => (univ.val.map (X (R := R) (σ := σ))).esymm (j + 1)) := by
  intro p q h
  refine esymmAlgHom_injective R hn (Subtype.ext ?_)
  simpa [esymmAlgHom_apply, esymm_eq_multiset_esymm] using h

/-- A polynomial in the variables `X 1, …, X n` over an infinite domain vanishes as soon as it
vanishes after substituting, for every `p : Fin n → K`, the elementary symmetric functions of the
`p i` for the variables. -/
theorem eq_zero_of_aeval_esymm_eq_zero {K : Type*} [CommRing K] [IsDomain K] [Infinite K]
    {n : ℕ} {P : MvPolynomial ℕ K} (hP : P ∈ supported K (Set.Icc 1 n))
    (h : ∀ p : Fin n → K, aeval (fun k ↦ (univ.val.map p).esymm k) P = 0) : P = 0 := by
  obtain ⟨P', rfl⟩ := exists_rename_eq_of_vars_subset_range P (fun i : Fin n ↦ (i : ℕ) + 1)
    (fun i j hij ↦ Fin.ext (by simpa using hij)) fun k hk ↦ by
      obtain ⟨hk₁, hk₂⟩ := mem_supported.mp hP hk
      exact ⟨⟨k - 1, by omega⟩, by simp only; omega⟩
  -- Substituting the elementary symmetric polynomials gives the zero polynomial.
  have hzero : (esymmAlgHom (Fin n) K n P' : MvPolynomial (Fin n) K) = 0 := by
    rw [esymmAlgHom_apply]
    refine MvPolynomial.funext fun p ↦ ?_
    rw [map_zero, ← h p, aeval_rename, ← aeval_eq_eval, ← AlgHom.comp_apply, comp_aeval]
    simp [Function.comp_def, aeval_esymm_eq_multiset_esymm]
  rw [(map_eq_zero_iff _ (esymmAlgHom_fin_injective K le_rfl)).mp
    (ZeroMemClass.coe_eq_zero.mp hzero), map_zero]

/-- **The elementary symmetric polynomials are algebraically independent**: if `n ≤ card σ`, the
elementary symmetric polynomials `e₁, …, eₙ` of the variables of `σ` are algebraically independent
over the coefficient ring. -/
theorem algebraicIndependent_esymm (R : Type*) [CommRing R] {σ : Type*} [Fintype σ] {n : ℕ}
    (hn : n ≤ Fintype.card σ) :
    AlgebraicIndependent R fun i : Fin n => esymm σ R ((i : ℕ) + 1) := by
  rw [algebraicIndependent_iff_injective_aeval]
  have h : (aeval fun i : Fin n => esymm σ R ((i : ℕ) + 1) :
      MvPolynomial (Fin n) R → MvPolynomial σ R) = Subtype.val ∘ esymmAlgHom σ R n :=
    funext fun p => (esymmAlgHom_apply p).symm
  rw [h]
  exact Subtype.val_injective.comp (esymmAlgHom_injective R hn)

end MvPolynomial
