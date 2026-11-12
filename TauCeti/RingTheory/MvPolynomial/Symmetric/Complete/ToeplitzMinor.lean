/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Determinant.ComplementaryMinor
public import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Elementary

/-!
# Complementary minors of the `h` and `e` Toeplitz matrices

The Toeplitz matrix `(h_{j - i})` of complete homogeneous symmetric polynomials and the signed
Toeplitz matrix `((-1)^{j - i} e_{j - i})` of elementary ones are inverse to each other
(`TauCeti.hsymmToeplitz_mul_esymmToeplitz`), and both are upper unitriangular, so both have
determinant `1`. Jacobi's complementary-minor identity
(`Matrix.det_submatrix_comp_inr_eq_sign_mul_det_submatrix_comp_inl_of_det_eq_one`) therefore
reads every minor of the first off the complementary minor of the second, with no factor beyond
the sign of the two permutations that cut the indices in two.

This is the determinantal half of the passage from the Jacobi--Trudi identity
`TauCeti.diagramSchurPoly_eq_det_hsymmInt`, a determinant of complete homogeneous symmetric
polynomials of size the number of rows of a shape, to its dual (transpose) form, a determinant of
elementary ones of size the number of columns: the two matrices are complementary minors of the
two Toeplitz matrices, for the permutations that read off the beta-numbers of a partition and of
its conjugate.

Combined with `TauCeti.det_submatrix_esymmToeplitz`, which pulls the signs out of a minor of the
signed Toeplitz matrix, this expresses the minor of the `h` Toeplitz matrix through a minor of the
unsigned integer-indexed family `TauCeti.esymmInt`, the shape a dual Jacobi--Trudi determinant
has.

## Main results

* `TauCeti.det_submatrix_hsymmToeplitz`: **a minor of the `h` Toeplitz matrix is the
  complementary minor of the signed `e` Toeplitz matrix**, up to the sign of the two
  permutations.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 2, Example 3, and Section 3, formula (3.5).
-/

public section

namespace TauCeti

variable (σ : Type*) [Fintype σ] [DecidableEq σ] (R : Type*) [CommRing R]

/-- **Jacobi's complementary-minor identity for the two Toeplitz matrices of symmetric
polynomials.** A minor of `(h_{j - i})` on the rows `ρ (p)` and the columns `π (p)` is the
complementary minor of `((-1)^{j - i} e_{j - i})`, on the rows `π (m)` and the columns `ρ (m)`,
signed by `π` and `ρ`. -/
theorem det_submatrix_hsymmToeplitz {m p : Type*} [Fintype m] [Fintype p] [DecidableEq m]
    [DecidableEq p] (N : ℕ) (e : m ⊕ p ≃ Fin N) (π ρ : Equiv.Perm (Fin N)) :
    ((hsymmToeplitz σ R N).submatrix (⇑ρ ∘ ⇑e ∘ Sum.inr) (⇑π ∘ ⇑e ∘ Sum.inr)).det =
      ((Equiv.Perm.sign π : ℤ) : MvPolynomial σ R) *
          ((Equiv.Perm.sign ρ : ℤ) : MvPolynomial σ R) *
        ((esymmToeplitz σ R N).submatrix (⇑π ∘ ⇑e ∘ Sum.inl) (⇑ρ ∘ ⇑e ∘ Sum.inl)).det :=
  Matrix.det_submatrix_comp_inr_eq_sign_mul_det_submatrix_comp_inl_of_det_eq_one _ _
    (hsymmToeplitz_mul_esymmToeplitz σ R N) (det_hsymmToeplitz σ R N) e π ρ

end TauCeti
