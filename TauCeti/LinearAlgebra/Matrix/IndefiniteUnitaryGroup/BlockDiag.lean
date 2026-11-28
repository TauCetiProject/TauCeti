/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Block-diagonal matrices and unitary matrices preserving an involution

For a sign function `ε : n → ℤˣ`, let `J = diagonal (fun i ↦ (ε i : R))`. This file defines the
block-diagonal projection `TauCeti.Matrix.blockDiagPart ε x`, proves its algebraic formula
`(⅟2) • (x + J * x * J)`, characterizes matrices commuting with `J` as block-diagonal matrices
(`x i j = 0` whenever `ε i ≠ ε j`), and proves that a matrix preserving an involution `J` is unitary
(`Aᴴ * A = 1`) if and only if it commutes with `J`.

## Main definitions and results

* `TauCeti.Matrix.blockDiagPart`: zeroing out entries `(i, j)` with `ε i ≠ ε j`.
* `TauCeti.Matrix.blockDiagPart_eq_invOf_two_smul`:
  `blockDiagPart ε x = (⅟(2 : R)) • (x + J * x * J)` for `J = diagonal (fun i ↦ ((ε i : ℤ) : R))`.
* `TauCeti.Matrix.commute_diagonal_units_iff_blockDiag`:
  `Commute J x ↔ ∀ i j, ε i ≠ ε j → x i j = 0`.
* `TauCeti.Matrix.conjTranspose_mul_self_eq_one_iff_commute_of_invol`: if `J * J = 1` and
  `Aᴴ * J * A = J`, then `Aᴴ * A = 1 ↔ Commute J A`.

## Provenance

Generalized from `New.blockDiagPart_eq`, `New.mem_blockDiagAlg`, and
`New.conjTranspose_mul_self_eq_one_iff_commute` in
`src/Lib/DiscreteSeries/Holomorphic/MaximalCompactMinors.lean` of
[grh-lean](https://github.com/lsernau/grh-lean) at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open scoped Matrix

namespace TauCeti.Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The block-diagonal part of `x` with respect to a labelling `ε`: keeps entries `(i, j)` with
`ε i = ε j` and zeros out all other entries. -/
def blockDiagPart {R β : Type*} [Zero R] [DecidableEq β] (ε : n → β) (x : _root_.Matrix n n R) :
    _root_.Matrix n n R :=
  _root_.Matrix.of fun i j ↦ if ε i = ε j then x i j else 0

/-- For a sign function `ε : n → ℤˣ` and `J = diagonal (fun i ↦ ((ε i : ℤ) : R))`, the
block-diagonal part of `x` equals `(⅟2) • (x + J * x * J)`. -/
theorem blockDiagPart_eq_invOf_two_smul {R : Type*} [CommRing R] [Invertible (2 : R)]
    (ε : n → ℤˣ) (x : _root_.Matrix n n R) :
    blockDiagPart ε x =
      (⅟(2 : R)) • (x + _root_.Matrix.diagonal (fun i ↦ ((ε i : ℤ) : R)) * x *
        _root_.Matrix.diagonal (fun i ↦ ((ε i : ℤ) : R))) := by
  ext i j
  have h_entry :
      (_root_.Matrix.diagonal (fun k ↦ ((ε k : ℤ) : R)) * x *
        _root_.Matrix.diagonal (fun k ↦ ((ε k : ℤ) : R))) i j =
      ((ε i : ℤ) : R) * ((ε j : ℤ) : R) * x i j := by
    simp [_root_.Matrix.mul_diagonal, _root_.Matrix.diagonal_mul, mul_right_comm]
  rw [_root_.Matrix.smul_apply, _root_.Matrix.add_apply, h_entry, smul_eq_mul]
  obtain hi | hi := Int.units_eq_one_or (ε i) <;> obtain hj | hj := Int.units_eq_one_or (ε j) <;>
    simp [blockDiagPart, hi, hj, ← two_mul, ← mul_assoc]

/-- Over a ring with no zero divisors and `2 ≠ 0`, a matrix commutes with the sign matrix
`diagonal (fun i ↦ ((ε i : ℤ) : R))` if and only if its entries `(i, j)` vanish whenever
`ε i ≠ ε j`. -/
theorem commute_diagonal_units_iff_blockDiag {R : Type*} [Ring R] [NoZeroDivisors R]
    (h2 : (2 : R) ≠ 0) (ε : n → ℤˣ) (x : _root_.Matrix n n R) :
    Commute (_root_.Matrix.diagonal (fun i ↦ ((ε i : ℤ) : R))) x ↔
      ∀ i j : n, ε i ≠ ε j → x i j = 0 := by
  rw [commute_iff_eq, ← _root_.Matrix.ext_iff]
  constructor
  · intro h i j hij
    have h_eq := h i j
    simp only [_root_.Matrix.diagonal_mul, _root_.Matrix.mul_diagonal] at h_eq
    obtain hi | hi := Int.units_eq_one_or (ε i) <;> obtain hj | hj := Int.units_eq_one_or (ε j)
    · exact absurd (hi.trans hj.symm) hij
    · have : (2 : R) * x i j = 0 := by
        rw [two_mul]
        simp only [hi, hj, Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, one_mul,
          mul_neg, mul_one] at h_eq
        exact eq_neg_iff_add_eq_zero.mp h_eq
      exact (mul_eq_zero.mp this).resolve_left h2
    · have : (2 : R) * x i j = 0 := by
        rw [two_mul]
        simp only [hi, hj, Units.val_one, Units.val_neg, Int.cast_one, Int.cast_neg, neg_one_mul,
          mul_one] at h_eq
        exact eq_neg_iff_add_eq_zero.mp (neg_eq_iff_eq_neg.mp h_eq)
      exact (mul_eq_zero.mp this).resolve_left h2
    · exact absurd (hi.trans hj.symm) hij
  · intro h i j
    simp only [_root_.Matrix.diagonal_mul, _root_.Matrix.mul_diagonal]
    by_cases hij : ε i = ε j
    · obtain hi | hi := Int.units_eq_one_or (ε i) <;> simp [← hij, hi]
    · simp [h i j hij]

/-- If `J` is a matrix involution (`J * J = 1`) over a commutative star ring and `A` preserves the
form of `J` (`Aᴴ * J * A = J`), then `A` is unitary (`Aᴴ * A = 1`) if and only if `A` commutes with
`J`. -/
theorem conjTranspose_mul_self_eq_one_iff_commute_of_invol {R : Type*} [CommRing R] [StarRing R]
    {J A : _root_.Matrix n n R} (h_invol : J * J = 1) (h_form : Aᴴ * J * A = J) :
    Aᴴ * A = 1 ↔ Commute J A := by
  constructor
  · intro h_left
    calc J * A = A * Aᴴ * (J * A) := by
          rw [mul_eq_one_comm.mp h_left, _root_.Matrix.one_mul]
      _ = A * (Aᴴ * J * A) := by simp only [_root_.Matrix.mul_assoc]
      _ = A * J := by rw [h_form]
  · intro h_comm
    calc Aᴴ * A = Aᴴ * (A * J) * J := by
          simp only [_root_.Matrix.mul_assoc, h_invol, _root_.Matrix.mul_one]
      _ = Aᴴ * J * A * J := by rw [← h_comm.eq, ← _root_.Matrix.mul_assoc]
      _ = 1 := by rw [h_form, h_invol]

end TauCeti.Matrix
