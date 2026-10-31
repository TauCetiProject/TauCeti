/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.Algebra.BigOperators.Fin

/-!
# Adding multiples of rows to the last row

`TauCeti.lastRowTransvection d b` is the lower unitriangular `(d + 1) × (d + 1)` matrix which
agrees with the identity except in its last row, where it is `(b 0, …, b (d - 1), 1)`.
Multiplying by it on the left adds `b k` times row `k` to the last row, for every `k < d`. These
matrices compose by adding their multipliers, so each is a unit.

## Main results

* `TauCeti.lastRowTransvection_mul_lastRowTransvection`: the matrices compose additively.
* `TauCeti.isUnit_lastRowTransvection`: each `lastRowTransvection d b` is a unit.
* `TauCeti.lastRowTransvection_mul_diagonal`: right multiplication by `diagonal (1, …, 1, x)`
  scales the last column by `x`.
-/

public section

open Matrix

namespace TauCeti

variable {A : Type*} {d : ℕ}

section ZeroOne

variable [Zero A] [One A]

/-- The lower unitriangular matrix of size `d + 1` which agrees with the identity except in its
last row, where it is `(b 0, …, b (d - 1), 1)`. Multiplying by it on the left adds `b k` times
row `k` to the last row, for every `k < d`. -/
def lastRowTransvection (d : ℕ) (b : Fin d → A) : Matrix (Fin (d + 1)) (Fin (d + 1)) A :=
  (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) A).updateRow (Fin.last d) (Fin.snoc b 1)

/-- `lastRowTransvection d b` is the identity with its last row replaced by `(b, 1)`. -/
theorem lastRowTransvection_def (b : Fin d → A) :
    lastRowTransvection d b =
      (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) A).updateRow (Fin.last d) (Fin.snoc b 1) := by
  rfl

/-- The entries of `lastRowTransvection d b`. -/
theorem lastRowTransvection_apply (b : Fin d → A) (i j : Fin (d + 1)) :
    lastRowTransvection d b i j =
      if i = Fin.last d then Fin.snoc (α := fun _ ↦ A) b 1 j else (1 : Matrix _ _ A) i j := by
  simp [lastRowTransvection, updateRow_apply]

/-- With all multipliers zero, `lastRowTransvection` is the identity. -/
@[simp]
theorem lastRowTransvection_zero : lastRowTransvection d (0 : Fin d → A) = 1 := by
  ext i j
  rw [lastRowTransvection_apply]
  split_ifs with hi
  · subst hi
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp [one_apply, (Fin.castSucc_lt_last j).ne']
  · rfl

end ZeroOne

section Semiring

variable [Semiring A]

/-- The row operations `lastRowTransvection` compose by adding their multipliers. -/
theorem lastRowTransvection_mul_lastRowTransvection (b b' : Fin d → A) :
    lastRowTransvection d b * lastRowTransvection d b' = lastRowTransvection d (b + b') := by
  rw [lastRowTransvection, updateRow_mul, one_mul]
  ext i j
  rw [updateRow_apply]
  split_ifs with hi
  · subst hi
    simp only [vecMul, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      one_mul, lastRowTransvection_apply, Fin.castSucc_ne_last, ↓reduceIte]
    induction j using Fin.lastCases with
    | last => simp [one_apply, Fin.castSucc_ne_last]
    | cast j => simp [one_apply]
  · simp [lastRowTransvection_apply, hi]

/-- Right multiplication by `diagonal (1, …, 1, x)` scales the last column by `x`. -/
theorem lastRowTransvection_mul_diagonal (b : Fin d → A) (x : A) :
    lastRowTransvection d b * diagonal (Fin.snoc (α := fun _ ↦ A) 1 x) =
      (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) A).updateRow (Fin.last d)
        (Fin.snoc (α := fun _ ↦ A) b x) := by
  rw [lastRowTransvection, updateRow_mul, one_mul]
  ext i j
  rw [updateRow_apply, updateRow_apply]
  split_ifs with hi
  · rw [vecMul_diagonal]
    induction j using Fin.lastCases with
    | last => simp
    | cast j => simp
  · induction i using Fin.lastCases with
    | last => exact absurd rfl hi
    | cast i => simp [diagonal_apply, one_apply]

end Semiring

/-- The elementary matrices `lastRowTransvection d b` are units, with inverse
`lastRowTransvection d (-b)`. -/
theorem isUnit_lastRowTransvection [Ring A] (b : Fin d → A) : IsUnit (lastRowTransvection d b) :=
  isUnit_iff_exists.2 ⟨lastRowTransvection d (-b), by
    simp [lastRowTransvection_mul_lastRowTransvection]⟩

end TauCeti
