/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.BigOperators

/-!
# Adding multiples of rows to the last row

`TauCeti.lastRowTransvection d b` is the lower unitriangular `(d + 1) × (d + 1)` matrix which
agrees with the identity except in its last row, where it is `(b 0, …, b (d - 1), 1)`.
Multiplying by it on the left adds `b k` times row `k` to the last row, for every `k < d`. These
matrices compose by adding their multipliers, so each is a unit. Transposing produces the
corresponding column operation `(lastRowTransvection d b)ᵀ`, which updates the last column of a
matrix `N` on the right to `N *ᵥ Fin.snoc b 1` (`mul_transpose_lastRowTransvection`) and shears a
module-valued tuple `(x₀, …, x_d)` to `(x₀ + b₀ • x_d, …, x_{d-1} + b_{d-1} • x_d, x_d)`
(`sum_mul_transpose_lastRowTransvection_smul`).

## Main results

* `TauCeti.lastRowTransvection_mul_lastRowTransvection`: the matrices compose additively.
* `TauCeti.isUnit_lastRowTransvection`: each `lastRowTransvection d b` is a unit.
* `TauCeti.lastRowTransvection_mul_diagonal`: right multiplication by `diagonal (1, …, 1, x)`
  scales the last column by `x`.
* `TauCeti.transpose_lastRowTransvection`, `TauCeti.mul_transpose_lastRowTransvection`,
  `TauCeti.sum_mul_transpose_lastRowTransvection_smul`: transpose column operation and its linear
  action on module-valued coordinate tuples.
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
    | cast j => simp [(Fin.castSucc_lt_last j).ne']
  · rfl

/-- The transpose of `lastRowTransvection d b` is the identity matrix with its last column replaced
by `Fin.snoc b 1`. -/
theorem transpose_lastRowTransvection (b : Fin d → A) :
    (lastRowTransvection d b)ᵀ =
      (1 : Matrix (Fin (d + 1)) (Fin (d + 1)) A).updateCol (Fin.last d) (Fin.snoc b 1) := by
  rw [lastRowTransvection, ← updateCol_transpose, transpose_one]

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
    | last => simp [Fin.castSucc_ne_last]
    | cast j => simp [Matrix.one_apply]
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
    | cast i => simp [diagonal_apply, Matrix.one_apply]

/-- Right multiplication by `(lastRowTransvection d b)ᵀ` replaces the last column of `N` with
`N *ᵥ Fin.snoc b 1`. -/
theorem mul_transpose_lastRowTransvection {ι : Type*} (N : Matrix ι (Fin (d + 1)) A)
    (b : Fin d → A) :
    N * (lastRowTransvection d b)ᵀ = N.updateCol (Fin.last d) (N *ᵥ Fin.snoc b 1) := by
  rw [transpose_lastRowTransvection, mul_updateCol, Matrix.mul_one]

/-- Acting by row `i` of `N * (lastRowTransvection d b)ᵀ` on a module-valued tuple
`x : Fin (d + 1) → M` evaluates row `i` of `N` against the sheared coordinates
`l ↦ x l.castSucc + b l • x (Fin.last d)` together with `x (Fin.last d)`. -/
theorem sum_mul_transpose_lastRowTransvection_smul {ι M : Type*} [AddCommMonoid M] [Module A M]
    (N : Matrix ι (Fin (d + 1)) A) (b : Fin d → A) (x : Fin (d + 1) → M) (i : ι) :
    ∑ m : Fin (d + 1), (N * (lastRowTransvection d b)ᵀ) i m • x m =
      (∑ l : Fin d, N i l.castSucc • (x l.castSucc + b l • x (Fin.last d))) +
        N i (Fin.last d) • x (Fin.last d) := by
  rw [mul_transpose_lastRowTransvection, Fin.sum_univ_castSucc]
  simp [mulVec, dotProduct, Fin.sum_univ_castSucc, smul_add, add_smul, Finset.sum_add_distrib,
    Finset.sum_smul, mul_smul, add_assoc]

end Semiring

/-- The elementary matrices `lastRowTransvection d b` are units, with inverse
`lastRowTransvection d (-b)`. -/
theorem isUnit_lastRowTransvection [Ring A] (b : Fin d → A) : IsUnit (lastRowTransvection d b) :=
  isUnit_iff_exists.2 ⟨lastRowTransvection d (-b), by
    simp [lastRowTransvection_mul_lastRowTransvection]⟩

end TauCeti
