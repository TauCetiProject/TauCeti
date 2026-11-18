/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.Jordan.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import TauCeti.Data.Matrix.Basis

/-!
# Transpose as a Jordan star automorphism

Matrix transposition preserves adjoints and squares, although it reverses multiplication.
Matrix units distinguish Jordan star automorphisms from algebra automorphisms.
-/

public section

namespace TauCeti.JordanStarEquiv

/-- Matrix transposition is a complex Jordan star automorphism. -/
def transpose (n R : Type*) [Fintype n] [NonUnitalNonAssocCommSemiring R]
    [Star R] [Module ℂ R] : JordanStarEquiv (Matrix n n R) (Matrix n n R) where
  toLinearEquiv := Matrix.transposeLinearEquiv n n ℂ R
  map_star' x := by ext i j; rfl
  map_mul_self_of_isSelfAdjoint' x _ := Matrix.transpose_mul x x

@[simp] theorem transpose_apply (n R : Type*) [Fintype n]
    [NonUnitalNonAssocCommSemiring R] [Star R] [Module ℂ R]
    (x : Matrix n n R) : transpose n R x = x.transpose := (rfl)

@[simp] theorem transpose_symm (n R : Type*) [Fintype n]
    [NonUnitalNonAssocCommSemiring R] [Star R] [Module ℂ R] :
    (transpose n R).symm = transpose n R := by
  apply ext
  intro x
  apply EquivLike.injective (transpose n R)
  simp only [apply_symm_apply, transpose_apply, Matrix.transpose_transpose]

@[simp] theorem toLinearEquiv_transpose (n R : Type*) [Fintype n]
    [NonUnitalNonAssocCommSemiring R] [Star R] [Module ℂ R] :
    (transpose n R).toLinearEquiv = Matrix.transposeLinearEquiv n n ℂ R := (rfl)

-- Transposition fixes the identity matrix.
example : transpose (Fin 2) ℂ 1 = 1 := map_one _

/-- Transposition of square matrices over a nontrivial commutative semiring, indexed by a
type with at least two elements, is not multiplicative. -/
theorem not_forall_transpose_mul (n R : Type*) [Fintype n] [Nontrivial n]
    [NonAssocCommSemiring R] [Star R] [Module ℂ R] [Nontrivial R] :
    ¬ ∀ x y : Matrix n n R, transpose n R (x * y) = transpose n R x * transpose n R y :=
  fun h ↦ Matrix.not_forall_transpose_mul n R fun x y ↦ by
    simpa only [transpose_apply] using h x y

-- The two by two complex instance.
example : ¬ ∀ x y : Matrix (Fin 2) (Fin 2) ℂ,
    transpose (Fin 2) ℂ (x * y) = transpose (Fin 2) ℂ x * transpose (Fin 2) ℂ y :=
  not_forall_transpose_mul (Fin 2) ℂ

end TauCeti.JordanStarEquiv
