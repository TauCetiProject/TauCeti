/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant

/-!
# Prepending full columns to a shape

Lengthening every one of the first `N` rows of a Young diagram by the same amount `c` —
equivalently, prepending `c` columns of full height `N` — multiplies its Schur polynomial in `N`
variables by `(x₀ ⋯ x_{N-1})^c`:

`s_ν(x) = (∏ᵢ xᵢ)^c · s_μ(x)` whenever `ν_j = μ_j + c` for every `j < N`.

The reason is visible on the tableau side — the prepended columns of a semistandard tableau in the
alphabet `{0, …, N - 1}` are forced to be `0, 1, …, N - 1` from top to bottom, contributing the
monomial `(x₀ ⋯ x_{N-1})^c` and leaving a tableau of the shorter shape — but the proof here is the
one-line bialternant computation: adding `c` to every row length adds `c` to every beta-number
(`YoungDiagram.betaNumber`), and raising every exponent of an alternant by `c` multiplies it by
`(∏ᵢ xᵢ)^c` (`TauCeti.alternant_add_const`).  Cancelling the Vandermonde alternant, which is
nonzero because the staircase exponents are distinct, gives the identity.

Both row bounds are needed, the hypothesis on the row lengths saying nothing about the rows past
the first `N` of either shape.  A shape taller than `N` has vanishing Schur polynomial in `N`
variables (`TauCeti.diagramSchurPoly_eq_zero_of_lt_colLen`), so dropping either bound lets one side
of the identity vanish while the other does not: without the bound on `ν` the left-hand side can
vanish and the right-hand side not, and without the bound on `μ` the right-hand side can vanish and
the left-hand side not.

This is the polynomial shadow of the determinant twist of a `GL N`-representation: a full column
block contributes a factor of the determinant character, and
`TauCeti.char_rationalWeylRep_weightOfShape_diagonal` reads the identity below that way.

## Main results

* `TauCeti.diagramSchurPoly_eq_prod_X_pow_mul_of_rowLen_eq_add`: **prepending `c` full columns
  multiplies the Schur polynomial by `(∏ᵢ xᵢ)^c`**.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I, Section
  3, Example 1, where the same shift of the bialternant numerator is read off.
-/

public section

open Finset MvPolynomial

namespace TauCeti

variable {N c : ℕ} {μ ν : YoungDiagram}

/-- Adding `c` to the first `N` row lengths adds `c` to the first `N` beta-numbers. -/
private theorem betaNumber_eq_add (h : ∀ j < N, ν.rowLen j = μ.rowLen j + c) :
    (fun j : Fin N => ν.betaNumber N j) = fun j : Fin N => μ.betaNumber N j + c := by
  funext j
  rw [YoungDiagram.betaNumber_def, YoungDiagram.betaNumber_def, h j j.isLt]
  omega

/-- The integer case of `TauCeti.diagramSchurPoly_eq_prod_X_pow_mul_of_rowLen_eq_add`, where the
Vandermonde alternant may be cancelled. -/
private theorem diagramSchurPoly_int_eq_prod_X_pow_mul (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N)
    (h : ∀ j < N, ν.rowLen j = μ.rowLen j + c) :
    diagramSchurPoly N ℤ ν
      = (∏ i, (X i : MvPolynomial (Fin N) ℤ)) ^ c * diagramSchurPoly N ℤ μ := by
  -- Cancel the staircase alternant, whose exponents are pairwise distinct.
  have hδ : Function.Injective fun j : Fin N => N - 1 - (j : ℕ) := fun a b hab => by
    have := a.isLt
    have := b.isLt
    exact Fin.ext (by simp only at hab; omega)
  refine mul_right_cancel₀ (alternant_ne_zero_of_injective hδ) ?_
  rw [diagramSchurPoly_mul_alternant N ν hν, betaNumber_eq_add h, alternant_add_const,
    mul_assoc, diagramSchurPoly_mul_alternant N μ hμ]

/-- **Prepending `c` columns of full height `N` multiplies a Schur polynomial by `(∏ᵢ xᵢ)^c`.**  If
`ν` and `μ` both have at most `N` rows and `ν_j = μ_j + c` for every `j < N`, then
`s_ν = (x₀ ⋯ x_{N-1})^c · s_μ` in `N` variables. -/
theorem diagramSchurPoly_eq_prod_X_pow_mul_of_rowLen_eq_add (R : Type*) [CommSemiring R]
    (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N) (h : ∀ j < N, ν.rowLen j = μ.rowLen j + c) :
    diagramSchurPoly N R ν
      = (∏ i, (X i : MvPolynomial (Fin N) R)) ^ c * diagramSchurPoly N R μ := by
  have hnat : diagramSchurPoly N ℕ ν
      = (∏ i, (X i : MvPolynomial (Fin N) ℕ)) ^ c * diagramSchurPoly N ℕ μ := by
    refine MvPolynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective ?_
    simpa only [map_diagramSchurPoly, map_mul, map_pow, map_prod, MvPolynomial.map_X] using
      diagramSchurPoly_int_eq_prod_X_pow_mul hμ hν h
  calc diagramSchurPoly N R ν
      = MvPolynomial.map (Nat.castRingHom R) (diagramSchurPoly N ℕ ν) :=
        (map_diagramSchurPoly (R := ℕ) (Nat.castRingHom R)).symm
    _ = (∏ i, (X i : MvPolynomial (Fin N) R)) ^ c * diagramSchurPoly N R μ := by
        rw [hnat]
        simp only [map_mul, map_pow, map_prod, MvPolynomial.map_X, map_diagramSchurPoly]

end TauCeti
