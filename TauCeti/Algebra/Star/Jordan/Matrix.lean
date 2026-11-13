/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.Jordan.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-!
# Transpose as a Jordan star automorphism

Matrix transposition preserves adjoints and squares, although it reverses multiplication.
The two by two matrix units distinguish Jordan star automorphisms from algebra automorphisms.
-/

public section

namespace TauCeti.JordanStarEquiv

/-- Matrix transposition is a complex Jordan star automorphism. -/
def transpose (n : Type*) [Fintype n] [DecidableEq n] :
    JordanStarEquiv (Matrix n n ℂ) (Matrix n n ℂ) where
  toLinearEquiv := Matrix.transposeLinearEquiv n n ℂ ℂ
  map_star' x := by ext i j; rfl
  map_sq' x _ := Matrix.transpose_mul x x

@[simp] theorem transpose_apply (n : Type*) [Fintype n] [DecidableEq n]
    (x : Matrix n n ℂ) : transpose n x = x.transpose := (rfl)

-- Transposition fixes the identity matrix.
example : transpose (Fin 2) 1 = 1 := map_one _

/-- The matrix units `e₁₂` and `e₂₁` witness failure of multiplicativity. -/
theorem transpose_not_multiplicative :
    ¬ ∀ x y : Matrix (Fin 2) (Fin 2) ℂ,
      transpose (Fin 2) (x * y) = transpose (Fin 2) x * transpose (Fin 2) y := by
  intro h
  have h00 := congrArg (fun m : Matrix (Fin 2) (Fin 2) ℂ ↦ m 0 0)
    (h !![0, 1; 0, 0] !![0, 0; 1, 0])
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, transpose_apply] at h00

end TauCeti.JordanStarEquiv
