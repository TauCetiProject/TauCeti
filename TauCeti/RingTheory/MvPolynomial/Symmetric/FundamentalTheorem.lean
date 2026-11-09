/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem

/-!
# Identifying polynomials in the elementary symmetric functions of the variables

Mathlib's fundamental theorem of symmetric polynomials, `MvPolynomial.esymmAlgHom_injective`,
says that substituting the elementary symmetric polynomials `e₁, …, eₙ` of the variables of `σ`
into polynomials in `n` variables is injective when `n ≤ card σ`. This file restates it with the
elementary symmetric polynomials written as `Multiset.esymm` of the multiset of variables. In this
form, an identity between polynomials in `e₁, …, eₙ` follows from the same identity between
values at the elementary symmetric functions of a multiset of roots, specialized to the
variables.

## Main results

* `MvPolynomial.aeval_multiset_esymm_X_injective`: substituting the elementary symmetric
  functions of the multiset of variables is injective.
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

end MvPolynomial
