/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.FieldTheory.Separable
import TauCeti.LinearAlgebra.Matrix.Charpoly.Diagonal
import TauCeti.LinearAlgebra.Matrix.Charpoly.Separable
import TauCeti.LinearAlgebra.Matrix.Polynomial

/-!
# Similitudes of a sesquilinear form with distinct eigenvalues

Let `R` be a commutative semiring with an involution `star` and `β` a square matrix over `R`, the
Gram matrix of the sesquilinear form `(u, v) ↦ star u ⬝ᵥ β *ᵥ v`. A matrix `y` is a *similitude*
of `β` with multiplier `ν` if `yᴴ * β * y = ν • β`. If `u` and `v` are eigenvectors of `y` with
eigenvalues `r` and `s`, then `star r * s * (star u ⬝ᵥ β *ᵥ v) = ν * (star u ⬝ᵥ β *ᵥ v)`. When
nonzero elements of `R` can be cancelled on the right (`IsRightCancelMulZero`, for instance when
`R` is a commutative ring without zero divisors), it follows that `u` and `v` are orthogonal for
`β` unless `star r * s = ν`. This file records the consequences of this for the Gram matrix of `β`
in a family of eigenvectors of `y`.

Over a field, when the eigenvalues `r` of `y` are distinct and all satisfy `star r * r = ν`, the
condition `star r * s = ν` for two eigenvalues forces `r = s`. So the Gram matrix of `β` in an
eigenbasis of `y` is diagonal
(`Matrix.exists_mul_eq_mul_diagonal_and_conjTranspose_mul_mul_eq_diagonal`). For every polynomial
`p`, the same basis diagonalises `β * p(y)`, with diagonal entries `b i * p (d i)`, where `b` is
the diagonal of the Gram matrix of `β` and `d` the eigenvalues. Over a nontrivial commutative ring
without zero divisors with a partial order compatible with the involution (a `StarOrderedRing`),
such as `ℂ`, this computes the positive definiteness of `β * p(y)` (`Matrix.posDef_mul_aeval_iff`):
it holds exactly when every `b i * p (d i)` is positive. The matrix `β * δ(y)` is again a form of
which `y` is a similitude with multiplier `ν` (`Matrix.conjTranspose_mul_mul_aeval_mul_eq_smul`),
with diagonal entries `b i * δ (d i)`: passing from `β` to `β * δ(y)` multiplies the diagonal
entries by the `δ (d i)`. When these are real, as for a Hermitian `β` and real-valued `δ (d i)`,
this multiplies their signs.

This is the linear algebra behind the change of signs of an elliptic similitude at the infinite
places of a CM field (`Matrix.IsEllipticSimilitude`), where `y` has irreducible characteristic
polynomial and its complex eigenvalues all have absolute value `√ν`.

## Main results

* `Matrix.isDiag_of_conjTranspose_diagonal_mul_mul_diagonal_eq_smul`: over a commutative semiring
  with right cancellation of nonzero elements, a matrix `B` with
  `(diagonal d)ᴴ * B * diagonal d = ν • B` is diagonal when `star (d i) * d j ≠ ν` for `i ≠ j`.
* `Matrix.isDiag_conjTranspose_mul_mul_of_mul_eq_mul_diagonal`: under the same cancellation
  hypothesis, the Gram matrix of a form in a family of eigenvectors of a similitude is diagonal
  under the same condition on the eigenvalues.
* `Matrix.exists_mul_eq_mul_diagonal_and_conjTranspose_mul_mul_eq_diagonal`: over a field, a
  similitude with split separable characteristic polynomial whose eigenvalues all satisfy
  `star r * r = ν` has an eigenbasis in which the form is diagonal.
* `Matrix.conjTranspose_mul_mul_aeval_mul_eq_diagonal`, `Matrix.posDef_mul_aeval_iff`: in such a
  basis, `β * p(y)` is diagonal with entries `b i * p (d i)`, and, over a nontrivial star-ordered
  commutative ring without zero divisors, it is positive definite iff these are positive.
* `Matrix.conjTranspose_mul_mul_aeval_mul_eq_smul`: `y` is a similitude of `β * δ(y)`.
-/

public section

open Polynomial

namespace Matrix

variable {n m R : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

section CommSemiring

variable [CommSemiring R]

/-- Over a commutative semiring in which nonzero elements cancel on the right, a matrix `B` with
`(diagonal d)ᴴ * B * diagonal d = ν • B` is diagonal as soon as `star (d i) * d j ≠ ν` for all
`i ≠ j`: its off-diagonal entries satisfy `star (d i) * d j * B i j = ν * B i j`. -/
theorem isDiag_of_conjTranspose_diagonal_mul_mul_diagonal_eq_smul [StarAddMonoid R]
    [IsRightCancelMulZero R] {B : Matrix n n R} {d : n → R} {ν : R}
    (h : (diagonal d)ᴴ * B * diagonal d = ν • B) (hd : Pairwise fun i j ↦ star (d i) * d j ≠ ν) :
    B.IsDiag := by
  intro i j hij
  have hij' : star (d i) * B i j * d j = ν * B i j := by
    simpa [diagonal_conjTranspose] using congrFun (congrFun h i) j
  by_contra hB
  exact hd hij (mul_right_cancel₀ hB (by rwa [mul_right_comm]))

omit [DecidableEq n] in
/-- **The form is diagonal in a family of eigenvectors of a similitude.** Over a commutative
semiring in which nonzero elements cancel on the right, if `y` is a similitude of `β` with
multiplier `ν`, `y * P = P * diagonal d`, and `star (d i) * d j ≠ ν` for `i ≠ j`, then the Gram
matrix `Pᴴ * β * P` of `β` in the columns of `P` is diagonal. -/
theorem isDiag_conjTranspose_mul_mul_of_mul_eq_mul_diagonal [StarRing R] [IsRightCancelMulZero R]
    {y β : Matrix n n R} {P : Matrix n m R} {d : m → R} {ν : R} (hβ : yᴴ * β * y = ν • β)
    (hP : y * P = P * diagonal d) (hd : Pairwise fun i j ↦ star (d i) * d j ≠ ν) :
    (Pᴴ * β * P).IsDiag := by
  refine isDiag_of_conjTranspose_diagonal_mul_mul_diagonal_eq_smul ?_ hd
  -- `diagonal d` is a similitude of the Gram matrix `Pᴴ * β * P`, since `P * diagonal d = y * P`.
  calc (diagonal d)ᴴ * (Pᴴ * β * P) * diagonal d
      = (P * diagonal d)ᴴ * β * (P * diagonal d) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * (yᴴ * β * y) * P := by
        simp only [← hP, conjTranspose_mul, Matrix.mul_assoc]
    _ = ν • (Pᴴ * β * P) := by
        rw [hβ, Matrix.mul_smul, Matrix.smul_mul]

variable [Star R]

/-- If `y` is a similitude of `β` with multiplier `ν`, then it is also a similitude of
`β * p(y)` with multiplier `ν`, for every polynomial `p`. -/
theorem conjTranspose_mul_mul_aeval_mul_eq_smul {y β : Matrix n n R} {ν : R}
    (hβ : yᴴ * β * y = ν • β) (p : R[X]) :
    yᴴ * (β * aeval y p) * y = ν • (β * aeval y p) := by
  have hc : aeval y p * y = y * aeval y p := by
    simpa only [map_mul, aeval_X] using congrArg (aeval y) (mul_comm p X)
  calc yᴴ * (β * aeval y p) * y = yᴴ * β * (aeval y p * y) := by
        simp only [Matrix.mul_assoc]
    _ = (yᴴ * β * y) * aeval y p := by
        rw [hc]
        simp only [Matrix.mul_assoc]
    _ = ν • (β * aeval y p) := by
        rw [hβ, Matrix.smul_mul]

/-- In a family of eigenvectors of `y` in which the form `β` is diagonal, the form `β * p(y)` is
diagonal with entries `b i * p (d i)`. -/
theorem conjTranspose_mul_mul_aeval_mul_eq_diagonal {y β : Matrix n n R} {P : Matrix n m R}
    {d b : m → R} (hP : y * P = P * diagonal d) (hb : Pᴴ * β * P = diagonal b) (p : R[X]) :
    Pᴴ * (β * aeval y p) * P = diagonal fun i ↦ b i * p.eval (d i) := by
  calc Pᴴ * (β * aeval y p) * P = Pᴴ * β * (aeval y p * P) := by
        simp only [Matrix.mul_assoc]
    _ = diagonal fun i ↦ b i * p.eval (d i) := by
        rw [aeval_mul_eq_mul_aeval hP, aeval_diagonal, ← Matrix.mul_assoc, hb,
          diagonal_mul_diagonal]

end CommSemiring

/-- **Positivity of `β * p(y)` in an eigenbasis.** Over a nontrivial star-ordered commutative ring
without zero divisors, if `P` is invertible with `y * P = P * diagonal d` and
`Pᴴ * β * P = diagonal b`, then `β * p(y)` is positive definite if and only if
`0 < b i * p (d i)` for every `i`. -/
theorem posDef_mul_aeval_iff [CommRing R] [StarRing R] [PartialOrder R] [StarOrderedRing R]
    [NoZeroDivisors R] [Nontrivial R] {y β : Matrix n n R} {P : GL n R} {d b : n → R}
    (hP : y * P = P * diagonal d) (hb : (P : Matrix n n R)ᴴ * β * P = diagonal b) (p : R[X]) :
    (β * aeval y p).PosDef ↔ ∀ i, 0 < b i * p.eval (d i) := by
  rw [← IsUnit.posDef_star_left_conjugate_iff (Units.isUnit P), star_eq_conjTranspose,
    conjTranspose_mul_mul_aeval_mul_eq_diagonal hP hb, posDef_diagonal_iff]

section Field

variable {F : Type*} [Field F] [StarRing F]

/-- **A similitude with distinct eigenvalues of norm `ν` is diagonal in an eigenbasis.** Let `y` be
a similitude over a field of `β` with multiplier `ν` whose characteristic polynomial splits with
distinct roots, each root `r` satisfying `star r * r = ν`. Then there are an invertible `P` and
`d`, `b` with `y * P = P * diagonal d`, `Pᴴ * β * P = diagonal b`, and `star (d i) * d i = ν` for
all `i`. -/
theorem exists_mul_eq_mul_diagonal_and_conjTranspose_mul_mul_eq_diagonal {y β : Matrix n n F}
    {ν : F} (hβ : yᴴ * β * y = ν • β) (hs : y.charpoly.Splits) (hsep : y.charpoly.Separable)
    (hroots : ∀ r ∈ y.charpoly.roots, star r * r = ν) :
    ∃ (P : GL n F) (d b : n → F), y * P = P * diagonal d ∧
      (P : Matrix n n F)ᴴ * β * P = diagonal b ∧ ∀ i, star (d i) * d i = ν := by
  obtain ⟨P, d, hP⟩ := exists_mul_eq_mul_diagonal_of_separable y hs hsep
  have hd i : star (d i) * d i = ν := hroots _ (mem_roots_charpoly_of_mul_eq_mul_diagonal hP i)
  -- Two distinct eigenvalues `d i ≠ d j` have `star (d i) * d j ≠ ν = star (d i) * d i`: cancel
  -- `star (d i)` if it is nonzero; if `d i = 0`, then `ν = 0` forces `d j = 0` too.
  have hne : Pairwise fun i j ↦ star (d i) * d j ≠ ν := by
    intro i j hij h
    have hdij := (injective_of_separable_of_mul_eq_mul_diagonal hsep hP).ne hij
    by_cases hi : d i = 0
    · rw [hi, star_zero, zero_mul] at h
      have hj := hd j
      rw [← h, mul_eq_zero, star_eq_zero, or_self] at hj
      exact hdij (hi.trans hj.symm)
    · exact hdij (mul_left_cancel₀ (star_ne_zero.2 hi) ((hd i).trans h.symm))
  have hdiag := isDiag_conjTranspose_mul_mul_of_mul_eq_mul_diagonal hβ hP hne
  exact ⟨P, d, _, hP, hdiag.diagonal_diag.symm, hd⟩

end Field

end Matrix
