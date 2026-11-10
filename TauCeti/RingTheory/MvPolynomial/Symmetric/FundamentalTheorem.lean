/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Polynomials in the elementary symmetric functions are determined by their values

By the fundamental theorem of symmetric polynomials, the elementary symmetric polynomials
`e₁, …, eₙ` in `n` variables are algebraically independent. Over an infinite integral domain a
polynomial is determined by its values, so a polynomial `P` in variables `X 1, …, X n` vanishes as
soon as it vanishes at the elementary symmetric functions `e₁(p), …, eₙ(p)` of every family
`p : Fin n → K`.

## Main results

* `MvPolynomial.eq_zero_of_aeval_esymm_eq_zero`: a polynomial in the variables `X 1, …, X n` that
  vanishes at the elementary symmetric functions of every `n`-tuple is zero.
-/

public section

open Finset

namespace MvPolynomial

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

end MvPolynomial
