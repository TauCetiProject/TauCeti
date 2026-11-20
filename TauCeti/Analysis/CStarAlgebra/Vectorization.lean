/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Choi matrices of individual Kraus summands

The Choi matrix uses output-input pairs as indices. A single Kraus operator gives
an outer product of its uncurried entries, with conjugation on the second factor.
The outer product and the vectorization use Mathlib's existing combinators.

Reference: Choi, Completely Positive Linear Maps on Complex Matrices (1975).

M.-D. Choi, *Completely positive linear maps on complex matrices*, 1975, Theorem 2 proof.
-/

public section

open Matrix

namespace TauCeti

/-- The Choi matrix of a map on complex matrices, with output-input coordinate order. -/
def choiMatrix {m n : Type*} [DecidableEq n]
    (Φ : Matrix n n ℂ → Matrix m m ℂ) : Matrix (m × n) (m × n) ℂ :=
  fun p q => Φ (Matrix.single p.snd q.snd (1 : ℂ)) p.fst q.fst

/-- An entry of the Choi matrix is the corresponding image of a matrix unit. -/
@[simp]
theorem choiMatrix_apply {m n : Type*} [DecidableEq n]
    (Φ : Matrix n n ℂ → Matrix m m ℂ) (p q : m × n) :
    choiMatrix Φ p q = Φ (Matrix.single p.snd q.snd (1 : ℂ)) p.fst q.fst := (rfl)

/-- The Choi matrix of a Kraus summand is the outer product of its vectorized entries. -/
theorem choiMatrix_kraus {m n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix m n ℂ) :
    choiMatrix (fun X : Matrix n n ℂ => K * X * Kᴴ) =
      Matrix.vecMulVec (Function.uncurry K) (star (Function.uncurry K)) := by
  ext p q
  simp only [choiMatrix, Matrix.vecMulVec, Function.uncurry, Pi.star_apply]
  rw [Matrix.mul_apply, Finset.sum_eq_single q.snd]
  · rw [Matrix.mul_single_apply_same, Matrix.conjTranspose_apply]
    simp
  · intro b _ hb
    rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hb]
    simp
  · intro h
    exact absurd (Finset.mem_univ q.snd) h

end TauCeti
