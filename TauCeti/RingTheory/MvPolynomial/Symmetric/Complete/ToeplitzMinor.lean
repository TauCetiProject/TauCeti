/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ComplementaryMinor
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

The signs of the entries of the elementary Toeplitz matrix come apart into a row factor and a
column factor, since `(-1)^{j - i}` and `(-1)^i (-1)^j` agree whenever `j ≥ i`, and the entry
vanishes otherwise. So a minor of the signed Toeplitz matrix is an explicit sign times the
corresponding minor of the unsigned integer-indexed family `TauCeti.esymmInt`, which is the shape
a dual Jacobi--Trudi determinant has.

## Main results

* `TauCeti.det_submatrix_hsymmToeplitz`: **a minor of the `h` Toeplitz matrix is the
  complementary minor of the signed `e` Toeplitz matrix**, up to the sign of the two
  permutations.
* `TauCeti.esymmToeplitz_apply_eq_neg_one_pow_mul`: the sign of an entry of the signed `e`
  Toeplitz matrix splits as a row factor times a column factor.
* `TauCeti.det_submatrix_esymmToeplitz`: consequently a minor of the signed `e` Toeplitz matrix is
  a product of signs times the corresponding minor of `TauCeti.esymmInt`.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 2, Example 3, and Section 3, formula (3.5).
-/

public section

open Finset

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

omit [DecidableEq σ] in
/-- The sign carried by an entry of the signed elementary Toeplitz matrix splits as a factor
depending only on the row and a factor depending only on the column. Below the diagonal the
entry vanishes, so the two sides agree there as well. -/
theorem esymmToeplitz_apply_eq_neg_one_pow_mul (N : ℕ) (i j : Fin N) :
    esymmToeplitz σ R N i j =
      (-1 : MvPolynomial σ R) ^ (i : ℕ) *
        ((-1 : MvPolynomial σ R) ^ (j : ℕ) * esymmInt σ R ((j : ℤ) - i)) := by
  rw [esymmToeplitz_apply]
  rcases le_or_gt (i : ℕ) (j : ℕ) with hij | hij
  · have htoNat : ((j : ℤ) - i).toNat = (j : ℕ) - (i : ℕ) := by omega
    have hsum : (i : ℕ) + (j : ℕ) = ((j : ℕ) - (i : ℕ)) + 2 * (i : ℕ) := by omega
    have hpow : (-1 : MvPolynomial σ R) ^ ((j : ℕ) - (i : ℕ)) =
        (-1 : MvPolynomial σ R) ^ (i : ℕ) * (-1 : MvPolynomial σ R) ^ (j : ℕ) := by
      rw [← pow_add, hsum, pow_add, pow_mul]
      simp
    rw [htoNat, hpow, mul_assoc]
  · have hneg : ((j : ℤ) - i) < 0 := by omega
    rw [esymmInt_of_neg hneg, mul_zero, mul_zero, mul_zero]

omit [DecidableEq σ] in
/-- A minor of the signed elementary Toeplitz matrix is a product of signs, one per row and one
per column, times the corresponding minor of the integer-indexed elementary symmetric
polynomials. -/
theorem det_submatrix_esymmToeplitz {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ℕ)
    (f g : ι → Fin N) :
    ((esymmToeplitz σ R N).submatrix f g).det =
      (∏ i, (-1 : MvPolynomial σ R) ^ ((f i : ℕ))) *
        (Matrix.of fun i j : ι => esymmInt σ R ((g j : ℤ) - f i)).det *
          ∏ j, (-1 : MvPolynomial σ R) ^ ((g j : ℕ)) := by
  have hentries : (esymmToeplitz σ R N).submatrix f g =
      Matrix.diagonal (fun i : ι => (-1 : MvPolynomial σ R) ^ ((f i : ℕ))) *
          (Matrix.of fun i j : ι => esymmInt σ R ((g j : ℤ) - f i)) *
        Matrix.diagonal fun j : ι => (-1 : MvPolynomial σ R) ^ ((g j : ℕ)) := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.submatrix_apply, esymmToeplitz_apply_eq_neg_one_pow_mul, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Matrix.of_apply]
    ring
  rw [hentries, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]

end TauCeti
