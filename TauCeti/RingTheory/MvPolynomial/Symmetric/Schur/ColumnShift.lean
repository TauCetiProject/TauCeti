/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Schur.Bialternant

/-!
# Prepending full columns to the shape of a Schur polynomial

Let `μ` be a Young diagram with at most `N` rows and let `ν` be obtained from it by lengthening
each of those `N` rows by `c`, that is, by prepending `c` columns of full height `N`.  Then

`s_ν = (x₀ ⋯ x_{N-1}) ^ c · s_μ`

in the alphabet `Fin N`, where `x₀ ⋯ x_{N-1}` is the top elementary symmetric polynomial
`e_N`.  This is `TauCeti.diagramSchurPoly_eq_prod_X_pow_mul`, and it is the symmetric-polynomial
shadow of the **determinant twist** of a rational representation of `GL N`: multiplying a character
by `det ^ c` adds `c` to every entry of its highest weight, and a highest weight whose entries are
all at least `c` is the weight of a shape with `c` full columns in front.

The proof is one line of Jacobi's bialternant formula
(`TauCeti.diagramSchurPoly_mul_alternant`).  Lengthening every one of the first `N` rows by `c`
raises every beta-number by `c`, and raising every exponent of an alternant by `c` multiplies it by
`(∏ᵢ xᵢ) ^ c` (`TauCeti.alternant_add_const`); the Vandermonde alternant `a_δ` can then be
cancelled over `ℤ`, and the identity transfers to an arbitrary commutative semiring because both
sides have natural-number coefficients.

Both row bounds are hypotheses, and neither follows from the other: the prescription relates `ν`
and `μ` only on the rows indexed by `Fin N`, and says nothing about the rows beyond them.

## Main results

* `TauCeti.diagramSchurPoly_eq_prod_X_pow_mul`: **prepending `c` full columns to a shape
  multiplies its Schur polynomial by `(x₀ ⋯ x_{N-1}) ^ c`.**

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 3, Example 1 (the effect on `s_λ` of adding a column of full height).
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 6 and
  Lecture 15, where the same identity is the determinant twist on characters of `GL N`.
-/

public section

open Finset MvPolynomial

namespace TauCeti

variable {R : Type*} [CommSemiring R]

/-- **Prepending `c` full columns to a shape multiplies its Schur polynomial by
`(x₀ ⋯ x_{N-1}) ^ c`.**  Here `ν` is the diagram with at most `N` rows whose `i`-th row is `c`
cells longer than the `i`-th row of `μ`, for every `i < N`.

The product `∏ᵢ xᵢ` is the top elementary symmetric polynomial `e_N` of the alphabet, so this is
the classical identity `s_{μ + (1ᴺ)·c} = e_N ^ c · s_μ`. -/
theorem diagramSchurPoly_eq_prod_X_pow_mul {N c : ℕ} {μ ν : YoungDiagram}
    (hμ : μ.colLen 0 ≤ N) (hν : ν.colLen 0 ≤ N) (h : ∀ i : Fin N, ν.rowLen i = μ.rowLen i + c) :
    diagramSchurPoly N R ν =
      (∏ i, (X i : MvPolynomial (Fin N) R)) ^ c * diagramSchurPoly N R μ := by
  -- Prove the identity over `ℤ`, where the nonzero Vandermonde alternant can be cancelled.  Both
  -- sides have natural-number coefficients, so the identity descends along the injection `ℕ → ℤ`
  -- and the resulting identity over `ℕ` maps to any commutative semiring.
  suffices hℤ : diagramSchurPoly N ℤ ν =
      (∏ i, (X i : MvPolynomial (Fin N) ℤ)) ^ c * diagramSchurPoly N ℤ μ by
    have hℕ : diagramSchurPoly N ℕ ν =
        (∏ i, (X i : MvPolynomial (Fin N) ℕ)) ^ c * diagramSchurPoly N ℕ μ :=
      MvPolynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective <| by
        simpa [map_diagramSchurPoly] using hℤ
    simpa [map_diagramSchurPoly] using congrArg (MvPolynomial.map (Nat.castRingHom R)) hℕ
  have hδ : Function.Injective fun j : Fin N => N - 1 - (j : ℕ) := fun i j hij => by
    have := i.isLt
    have := j.isLt
    exact Fin.ext (by simp only at hij; omega)
  have hbeta : (fun j : Fin N => ν.betaNumber N j) = fun j : Fin N => μ.betaNumber N j + c := by
    funext j
    rw [YoungDiagram.betaNumber_def, YoungDiagram.betaNumber_def, h j]
    omega
  refine mul_right_cancel₀ (alternant_ne_zero_of_injective hδ) ?_
  rw [diagramSchurPoly_mul_alternant N ν hν, hbeta, alternant_add_const, mul_assoc,
    diagramSchurPoly_mul_alternant N μ hμ]

end TauCeti
