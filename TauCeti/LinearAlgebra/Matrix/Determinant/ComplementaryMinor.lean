/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Jacobi's complementary-minor identity

Let `A` and `B` be mutually inverse square matrices, `A * B = 1`. Jacobi's theorem says that a
minor of `A` is, up to sign and the factor `det A`, the *complementary* minor of `B`: the one on
the rows and the columns that the minor of `A` leaves out, with the roles of rows and columns
exchanged.

The index bookkeeping is carried here by a splitting of the index type as a sum `m ⊕ p` together
with two permutations `σ` and `τ`: the minor of `A` sits on the rows `τ (p)` and the columns
`σ (p)`, and its complementary minor of `B` on the rows `σ (m)` and the columns `τ (m)`. The sign
of the identity is then exactly the product of the signs of the two permutations, with no further
combinatorial factor, and no pair of index subsets has to be ordered. Choosing the permutations to
enumerate a subset and its complement in increasing order recovers the classical statement for
index sets.

## Why this file

Tau Ceti already has the `h`--`e` duality `TauCeti.hsymmToeplitz_mul_esymmToeplitz`, saying that
the Toeplitz matrices of the complete homogeneous and the signed elementary symmetric polynomials
are inverse to one another. Jacobi's identity is what turns that duality into the dual (transpose)
Jacobi--Trudi formula, by matching a minor of one Toeplitz matrix with the complementary minor of
the other; `TauCeti.det_submatrix_hsymmToeplitz` in
`TauCeti/RingTheory/MvPolynomial/Symmetric/Complete/ToeplitzMinor.lean` is that match.

The identity is independent of `TauCeti.Matrix.det_sumElim_eq_det_mul` in
`TauCeti/LinearAlgebra/Matrix/Determinant/SumElim.lean`, which compares the determinant of a fixed
family of rows followed by a varying one with a determinant of pairings; that statement is about
the Plücker coordinates of a subspace and of its orthogonal complement, and has no inverse pair of
matrices in it.

## Main results

* `Matrix.det_submatrix_inr_eq_sign_mul_det_mul_det_submatrix_inl`: **Jacobi's
  complementary-minor identity**, for an index type presented as a sum.
* `Matrix.det_submatrix_comp_inr_eq_sign_mul_det_mul_det_submatrix_comp_inl`: the same identity
  for an arbitrary index type, split by a chosen equivalence with a sum.
* `Matrix.det_submatrix_comp_inr_eq_sign_mul_det_submatrix_comp_inl_of_det_eq_one`: the form the
  identity takes for a pair of inverse matrices of determinant one.
* `Matrix.det_submatrix_comp_inr_eq_sign_mul_det_mul_det_submatrix_comp_inl_nonsing_inv`: the
  form it takes for a matrix and its nonsingular inverse.

## References

* C. G. J. Jacobi, *De formatione et proprietatibus determinantium*, Journal fuer die reine und
  angewandte Mathematik 22 (1841), 285-318.
* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995], Chapter I,
  Section 2, Example 3, and Section 3, formula (3.5), where the identity is applied to the
  Toeplitz matrices of `h` and `e`.
-/

public section

open Equiv

namespace Matrix

variable {m p n R : Type*} [CommRing R] [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]

/-- **Jacobi's complementary-minor identity.** For mutually inverse matrices `A` and `B` indexed
by `m ⊕ p`, and permutations `σ`, `τ` of that index type, the minor of `A` on the rows `τ (p)` and
the columns `σ (p)` is `det A` times the complementary minor of `B`, the one on the rows `σ (m)`
and the columns `τ (m)`, signed by `σ` and `τ`.

For `p` empty both sides read `det A * det B = 1`, and for `m` empty they read `det A = det A`;
the content is in between. -/
theorem det_submatrix_inr_eq_sign_mul_det_mul_det_submatrix_inl
    (A B : Matrix (m ⊕ p) (m ⊕ p) R) (hAB : A * B = 1) (σ τ : Perm (m ⊕ p)) :
    (A.submatrix (⇑τ ∘ Sum.inr) (⇑σ ∘ Sum.inr)).det =
      ((Perm.sign σ : ℤ) : R) * ((Perm.sign τ : ℤ) : R) * A.det *
        (B.submatrix (⇑σ ∘ Sum.inl) (⇑τ ∘ Sum.inl)).det := by
  -- Everything comes from one auxiliary matrix `Q`. In the columns that `τ` takes from `m` it
  -- repeats the corresponding columns of `B`; in the columns that `τ` takes from `p` it carries
  -- the standard basis vector at the matching `σ`-image. Read through `σ` and `τ`, the matrix `Q`
  -- is block triangular with an identity block, so its determinant is the minor of `B` on the
  -- rows `σ (m)` and the columns `τ (m)`, up to the two signs. Multiplying by `A` collapses the
  -- first group of columns, because `A * B = 1` there, and turns the second group into columns
  -- of `A`: read through `τ` on both sides, `A * Q` is block triangular the other way round, with
  -- determinant the complementary minor of `A` on the rows `τ (p)` and the columns `σ (p)`.
  -- Comparing the two evaluations of `det (A * Q) = det A * det Q` is the identity.
  classical
  set Q : Matrix (m ⊕ p) (m ⊕ p) R := of fun x y =>
    Sum.elim (fun _ : m => B x y) (fun i : p => if x = σ (Sum.inr i) then 1 else 0) (τ.symm y)
    with hQ
  -- Read through `σ` and `τ`, the matrix `Q` is block lower triangular.
  have hQblocks : Q.submatrix σ τ =
      fromBlocks (B.submatrix (⇑σ ∘ Sum.inl) (⇑τ ∘ Sum.inl)) 0
        (B.submatrix (⇑σ ∘ Sum.inr) (⇑τ ∘ Sum.inl)) 1 := by
    ext u v
    rcases u with u | u <;> rcases v with v | v <;> simp [hQ, Matrix.one_apply]
  have hdetQ : Q.det = ((Perm.sign τ : ℤ) : R) *
      (((Perm.sign σ : ℤ) : R) * (B.submatrix (⇑σ ∘ Sum.inl) (⇑τ ∘ Sum.inl)).det) := by
    have hback : Q = ((Q.submatrix σ τ).submatrix ⇑σ.symm id).submatrix id ⇑τ.symm := by
      simp [Matrix.submatrix_submatrix]
    rw [hback, Matrix.det_permute', Matrix.det_permute, hQblocks,
      Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one, Perm.sign_symm, Perm.sign_symm]
  -- Multiplying by `A` collapses the columns carrying `B` and exposes columns of `A`.
  have hcol₁ : ∀ (x : m ⊕ p) (j : m),
      (A * Q) x (τ (Sum.inl j)) = if x = τ (Sum.inl j) then 1 else 0 := by
    intro x j
    have hcolQ : ∀ z : m ⊕ p, Q z (τ (Sum.inl j)) = B z (τ (Sum.inl j)) := by
      intro z; simp [hQ]
    simp only [Matrix.mul_apply, hcolQ]
    rw [← Matrix.mul_apply, hAB, Matrix.one_apply]
  have hcol₂ : ∀ (x : m ⊕ p) (i : p), (A * Q) x (τ (Sum.inr i)) = A x (σ (Sum.inr i)) := by
    intro x i
    have hcolQ : ∀ z : m ⊕ p, Q z (τ (Sum.inr i)) = if z = σ (Sum.inr i) then 1 else 0 := by
      intro z; simp [hQ]
    simp [Matrix.mul_apply, hcolQ]
  have hAQblocks : (A * Q).submatrix τ τ =
      fromBlocks 1 (A.submatrix (⇑τ ∘ Sum.inl) (⇑σ ∘ Sum.inr)) 0
        (A.submatrix (⇑τ ∘ Sum.inr) (⇑σ ∘ Sum.inr)) := by
    ext u v
    rcases u with u | u <;> rcases v with v | v <;> simp [hcol₁, hcol₂, Matrix.one_apply]
  have hdetA : (A.submatrix (⇑τ ∘ Sum.inr) (⇑σ ∘ Sum.inr)).det = A.det * Q.det := by
    have hdet := congrArg Matrix.det hAQblocks
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, one_mul] at hdet
    exact hdet.symm
  -- The two evaluations of `det (A * Q)` meet.
  rw [hdetA, hdetQ]
  ring

/-- **Jacobi's complementary-minor identity** for an arbitrary index type `n`, split into two
groups of indices by an equivalence `e : m ⊕ p ≃ n`. -/
theorem det_submatrix_comp_inr_eq_sign_mul_det_mul_det_submatrix_comp_inl
    [Fintype n] [DecidableEq n] (A B : Matrix n n R) (hAB : A * B = 1) (e : m ⊕ p ≃ n)
    (σ τ : Perm n) :
    (A.submatrix (⇑τ ∘ ⇑e ∘ Sum.inr) (⇑σ ∘ ⇑e ∘ Sum.inr)).det =
      ((Perm.sign σ : ℤ) : R) * ((Perm.sign τ : ℤ) : R) * A.det *
        (B.submatrix (⇑σ ∘ ⇑e ∘ Sum.inl) (⇑τ ∘ ⇑e ∘ Sum.inl)).det := by
  have hAB' : A.submatrix e e * B.submatrix e e = 1 := by
    rw [Matrix.submatrix_mul_equiv A B _ e _, hAB, Matrix.submatrix_one_equiv]
  have key := det_submatrix_inr_eq_sign_mul_det_mul_det_submatrix_inl (A.submatrix e e)
    (B.submatrix e e) hAB' (e.symm.permCongr σ) (e.symm.permCongr τ)
  simpa [Matrix.submatrix_submatrix, Function.comp_def, Equiv.permCongr_apply] using key

/-- Jacobi's complementary-minor identity for a pair of inverse matrices of determinant one: a
minor of `A` and the complementary minor of `B` agree up to the signs of the two permutations. -/
theorem det_submatrix_comp_inr_eq_sign_mul_det_submatrix_comp_inl_of_det_eq_one
    [Fintype n] [DecidableEq n] (A B : Matrix n n R) (hAB : A * B = 1) (hA : A.det = 1)
    (e : m ⊕ p ≃ n) (σ τ : Perm n) :
    (A.submatrix (⇑τ ∘ ⇑e ∘ Sum.inr) (⇑σ ∘ ⇑e ∘ Sum.inr)).det =
      ((Perm.sign σ : ℤ) : R) * ((Perm.sign τ : ℤ) : R) *
        (B.submatrix (⇑σ ∘ ⇑e ∘ Sum.inl) (⇑τ ∘ ⇑e ∘ Sum.inl)).det := by
  rw [det_submatrix_comp_inr_eq_sign_mul_det_mul_det_submatrix_comp_inl A B hAB e σ τ, hA, mul_one]

/-- Jacobi's complementary-minor identity written with the nonsingular inverse: for a matrix with
invertible determinant, a minor of the matrix is read off the complementary minor of its
inverse. -/
theorem det_submatrix_comp_inr_eq_sign_mul_det_mul_det_submatrix_comp_inl_nonsing_inv
    [Fintype n] [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) (e : m ⊕ p ≃ n)
    (σ τ : Perm n) :
    (A.submatrix (⇑τ ∘ ⇑e ∘ Sum.inr) (⇑σ ∘ ⇑e ∘ Sum.inr)).det =
      ((Perm.sign σ : ℤ) : R) * ((Perm.sign τ : ℤ) : R) * A.det *
        (A⁻¹.submatrix (⇑σ ∘ ⇑e ∘ Sum.inl) (⇑τ ∘ ⇑e ∘ Sum.inl)).det :=
  det_submatrix_comp_inr_eq_sign_mul_det_mul_det_submatrix_comp_inl A A⁻¹
    (Matrix.mul_nonsing_inv A hA) e σ τ

end Matrix
