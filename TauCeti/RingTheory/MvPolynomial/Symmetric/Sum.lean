/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Basic
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
public import TauCeti.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import TauCeti.RingTheory.PowerSeries.CoeffProd

/-!
# Symmetric polynomials in a disjoint union of two alphabets

The classical symmetric polynomials of the alphabet `σ ⊕ τ` split into the symmetric polynomials
of `σ` and of `τ`: the elementary and complete homogeneous polynomials by a convolution over the
antidiagonal, and the power sums additively. The elementary symmetric polynomials of the two
alphabets are moreover jointly algebraically independent.

These are the alphabet-splitting identities that make the ring of symmetric functions a bialgebra,
with `e_n` and `h_n` going to `∑_{i + j = n} e_i ⊗ e_j` and `∑_{i + j = n} h_i ⊗ h_j`, and the
power sums primitive.

## Main results

* `TauCeti.esymm_sum_type`: `e_n(x, y) = ∑_{i + j = n} e_i(x) e_j(y)`.
* `TauCeti.hsymm_sum_type`: `h_n(x, y) = ∑_{i + j = n} h_i(x) h_j(y)`.
* `TauCeti.psum_sum_type`: `p_n(x, y) = p_n(x) + p_n(y)`.
* `TauCeti.algebraicIndependent_esymm_sum_type`: `e₁(x), …, e_m(x), e₁(y), …, e_n(y)` are
  algebraically independent when `m ≤ card σ` and `n ≤ card τ`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 5, Example 25: the generating functions `E(t)` and `H(t)` of a union of two alphabets.
-/

public section

open Finset MvPolynomial

namespace TauCeti

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

section CommSemiring

variable (R : Type*) [CommSemiring R]

/-- **The elementary symmetric polynomials of a disjoint union of alphabets**:
`e_n(x, y) = ∑_{i + j = n} e_i(x) e_j(y)`. -/
theorem esymm_sum_type (n : ℕ) :
    esymm (σ ⊕ τ) R n = ∑ p ∈ antidiagonal n,
      rename Sum.inl (esymm σ R p.1) * rename Sum.inr (esymm τ R p.2) := by
  have h := PowerSeries.coeff_prod_sum_type (rename Sum.inl).toRingHom (rename Sum.inr).toRingHom
    (fun i : σ => 1 + PowerSeries.C (X i : MvPolynomial σ R) * PowerSeries.X)
    (fun j : τ => 1 + PowerSeries.C (X j : MvPolynomial τ R) * PowerSeries.X)
    (fun k => 1 + PowerSeries.C (X k) * PowerSeries.X) (fun i => by simp) (fun j => by simp) n
  simpa only [← mk_esymm_eq_prod_one_add_X, PowerSeries.coeff_mk, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe] using h

/-- **The complete homogeneous symmetric polynomials of a disjoint union of alphabets**:
`h_n(x, y) = ∑_{i + j = n} h_i(x) h_j(y)`. -/
theorem hsymm_sum_type [DecidableEq σ] [DecidableEq τ] (n : ℕ) :
    hsymm (σ ⊕ τ) R n = ∑ p ∈ antidiagonal n,
      rename Sum.inl (hsymm σ R p.1) * rename Sum.inr (hsymm τ R p.2) := by
  have h := PowerSeries.coeff_prod_sum_type (rename Sum.inl).toRingHom (rename Sum.inr).toRingHom
    (fun i : σ => PowerSeries.mk fun n => (X i : MvPolynomial σ R) ^ n)
    (fun j : τ => PowerSeries.mk fun n => (X j : MvPolynomial τ R) ^ n)
    (fun k => PowerSeries.mk fun n => X k ^ n) (fun i => by ext; simp) (fun j => by ext; simp) n
  simpa only [← mk_hsymm_eq_prod_mk_pow, PowerSeries.coeff_mk, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe] using h

/-- **The power sums of a disjoint union of alphabets**: `p_n(x, y) = p_n(x) + p_n(y)`. -/
theorem psum_sum_type (n : ℕ) :
    psum (σ ⊕ τ) R n = rename Sum.inl (psum σ R n) + rename Sum.inr (psum τ R n) := by
  simp [psum, Fintype.sum_sum_type]

end CommSemiring

/-- **The elementary symmetric polynomials of two disjoint alphabets are jointly algebraically
independent**: if `m ≤ card σ` and `n ≤ card τ`, the polynomials `e₁(x), …, e_m(x)` of the
variables of `σ` and `e₁(y), …, e_n(y)` of the variables of `τ` together form an algebraically
independent family of polynomials on `σ ⊕ τ`. -/
theorem algebraicIndependent_esymm_sum_type (R : Type*) [CommRing R] {m n : ℕ}
    (hm : m ≤ Fintype.card σ) (hn : n ≤ Fintype.card τ) :
    AlgebraicIndependent R (Sum.elim
      (fun i : Fin m => rename (Sum.inl : σ → σ ⊕ τ) (esymm σ R ((i : ℕ) + 1)))
      (fun j : Fin n => rename (Sum.inr : τ → σ ⊕ τ) (esymm τ R ((j : ℕ) + 1)))) := by
  -- move to polynomials in `σ` over polynomials in `τ`, where the inner family is a tower over
  -- the outer one
  refine AlgebraicIndependent.of_comp (sumAlgEquiv R σ τ).toAlgHom ?_
  convert (algebraicIndependent_esymm R hn).sumElim_comp
    (algebraicIndependent_esymm (MvPolynomial τ R) hm) using 1
  funext k
  cases k with
  | inl i =>
    have h := congr($(sumAlgEquiv_comp_rename_inl R σ τ) (esymm σ R ((i : ℕ) + 1)))
    simpa [map_esymm] using h
  | inr j => exact congr($(sumAlgEquiv_comp_rename_inr R σ τ) (esymm τ R ((j : ℕ) + 1)))

end TauCeti
