/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.diagonal`, `Matrix.single`, and matrix multiplication occur in the statement below.
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# Products of diagonal matrices and matrix units

This file records a generic matrix identity for multiplying a rectangular matrix unit on both
sides by diagonal matrices of the corresponding row and column sizes.

## Main results

* `TauCeti.diagonal_mul_single_mul_diagonal`: multiplying `Eᵢⱼ(c)` on the left and right by
  diagonal matrices rescales its entry by the corresponding diagonal coefficients.
* `Matrix.diagonal_mul_mul_diagonal`: a matrix is fixed by two-sided multiplication with
  diagonal matrices exactly when those rescale each of its entries back to itself, with
  `Matrix.diagonal_entry_eq_of_mul_eq_one` supplying that entry condition from coefficients
  inverse to one another along every nonzero entry and
  `Matrix.diagonal_entry_eq_of_mul_eq_one_map` supplying it for the image of such a matrix under a
  zero-preserving map.
-/

public section

open Matrix

namespace TauCeti

variable {m n : Type*} [DecidableEq m] [Fintype m] [DecidableEq n] [Fintype n]
variable {A : Type*} [Semiring A] {i : m} {j : n}

/-- Multiplying a matrix unit on the left and right by diagonal matrices rescales its nonzero
entry by the corresponding diagonal entries. -/
@[simp]
theorem diagonal_mul_single_mul_diagonal {v : m → A} {w : n → A} (c : A) :
    diagonal v * single i j c * diagonal w = single i j (v i * c * w j) := by
  ext a b
  rw [Matrix.mul_assoc]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp [mul_assoc]
  · simp [h]

end TauCeti

namespace Matrix

variable {n : Type*} [DecidableEq n] [Fintype n]

/-- **A matrix is fixed by two-sided multiplication with diagonal matrices** when those rescale
each of its entries back to itself. A congruence `D M Dᵀ = M` by a diagonal matrix is this
statement after `Matrix.diagonal_transpose`. -/
theorem diagonal_mul_mul_diagonal {A : Type*} [Semiring A] {v w : n → A} (M : Matrix n n A)
    (h : ∀ r c, v r * M r c * w c = M r c) :
    diagonal v * M * diagonal w = M := by
  ext r c
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact h r c

/-- **Coefficients inverse to one another along every nonzero entry rescale each entry back to
itself.** This is the entry condition of `Matrix.diagonal_mul_mul_diagonal` for a single family of
coefficients. -/
theorem diagonal_entry_eq_of_mul_eq_one {m : Type*} {A : Type*} [CommMonoidWithZero A]
    {v : m → A} {M : Matrix m m A} (h : ∀ r c, M r c ≠ 0 → v r * v c = 1) (r c : m) :
    v r * M r c * v c = M r c := by
  by_cases hz : M r c = 0
  · rw [hz, mul_zero, zero_mul]
  · calc v r * M r c * v c = v r * v c * M r c := by rw [mul_right_comm]
      _ = M r c := by rw [h r c hz, one_mul]

/-- **The entry condition for a transported matrix**: coefficients inverse to one another along
every nonzero entry of a matrix rescale each entry of its image under a zero-preserving map back
to itself, a vanishing entry being carried to a vanishing entry. -/
theorem diagonal_entry_eq_of_mul_eq_one_map {m : Type*} {S T : Type*} [Zero S]
    [CommMonoidWithZero T] {F : Type*} [FunLike F S T] [ZeroHomClass F S T] (f : F) {v : m → T}
    {M : Matrix m m S} (h : ∀ r c, M r c ≠ 0 → v r * v c = 1) (r c : m) :
    v r * (M.map f) r c * v c = (M.map f) r c :=
  diagonal_entry_eq_of_mul_eq_one
    (fun r c hne => h r c fun hz => hne (by rw [Matrix.map_apply, hz, map_zero])) r c

end Matrix
