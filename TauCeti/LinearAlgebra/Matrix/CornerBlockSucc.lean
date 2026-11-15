/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import TauCeti.LinearAlgebra.Matrix.Defs

/-!
# The block-diagonal matrix `diag(c, B)` of size `m + 1`

A scalar `c` and a square matrix `B` of size `m` give the block-diagonal matrix `diag(c, B)` of
size `m + 1`, with `c` in the corner indexed by `0` and `B` on the indices `Fin.succ`. This file
builds it and shows that it multiplies blockwise and commutes with the star operation. No
commutativity is assumed, so the construction applies to quaternionic matrices.

`TauCeti/LinearAlgebra/Matrix/UnitaryGroup/CornerBlock.lean` deduces from this the block-diagonal
embedding `U(1) × U(m) → U(m + 1)`.

## Main definitions

* `Matrix.cornerBlockSucc`: the block-diagonal matrix `diag(c, B)` of size `m + 1`, with the scalar
  `c` in the corner indexed by `0`.

## Main results

* `Matrix.cornerBlockSucc_inj`: `diag(c, B)` determines `c` and `B`.
* `Matrix.cornerBlockSucc_mul_cornerBlockSucc`, `Matrix.cornerBlockSucc_one`,
  `Matrix.star_cornerBlockSucc`: `diag(c, B)` is multiplicative and unital, and commutes with the
  star operation, blockwise.
-/

public section

open scoped Matrix

namespace Matrix

variable {α : Type*} {m : ℕ}

section Zero

variable [Zero α]

/-- The block-diagonal matrix `diag(c, B)` of size `m + 1`, with `c` in the corner indexed by `0`
and `B` on the indices `Fin.succ`. -/
def cornerBlockSucc (c : α) (B : Matrix (Fin m) (Fin m) α) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) α :=
  of (Fin.cons (Fin.cons c 0) fun i ↦ Fin.cons 0 (B i))

@[simp]
theorem cornerBlockSucc_zero_zero (c : α) (B : Matrix (Fin m) (Fin m) α) :
    cornerBlockSucc c B 0 0 = c :=
  (rfl)

@[simp]
theorem cornerBlockSucc_zero_succ (c : α) (B : Matrix (Fin m) (Fin m) α) (j : Fin m) :
    cornerBlockSucc c B 0 j.succ = 0 :=
  (rfl)

@[simp]
theorem cornerBlockSucc_succ_zero (c : α) (B : Matrix (Fin m) (Fin m) α) (i : Fin m) :
    cornerBlockSucc c B i.succ 0 = 0 :=
  (rfl)

@[simp]
theorem cornerBlockSucc_succ_succ (c : α) (B : Matrix (Fin m) (Fin m) α) (i j : Fin m) :
    cornerBlockSucc c B i.succ j.succ = B i j :=
  (rfl)

/-- The block-diagonal matrix `diag(c, B)` determines its blocks `c` and `B`. -/
@[simp]
theorem cornerBlockSucc_inj {c c' : α} {B B' : Matrix (Fin m) (Fin m) α} :
    cornerBlockSucc c B = cornerBlockSucc c' B' ↔ c = c' ∧ B = B' := by
  refine ⟨fun h ↦ ⟨?_, Matrix.ext fun i j ↦ ?_⟩, fun h ↦ h.1 ▸ h.2 ▸ rfl⟩
  · simpa using congrFun (congrFun h 0) 0
  · simpa using congrFun (congrFun h i.succ) j.succ

end Zero

/-- Block-diagonal matrices `diag(c, B)` multiply blockwise. -/
@[simp]
theorem cornerBlockSucc_mul_cornerBlockSucc [NonUnitalNonAssocSemiring α] (c c' : α)
    (B B' : Matrix (Fin m) (Fin m) α) :
    cornerBlockSucc c B * cornerBlockSucc c' B' = cornerBlockSucc (c * c') (B * B') := by
  refine ext_fin_succ ?_ (fun j ↦ ?_) (fun i ↦ ?_) (fun i j ↦ ?_) <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

/-- The block-diagonal matrix `diag(1, 1)` is the identity matrix. -/
@[simp]
theorem cornerBlockSucc_one [Zero α] [One α] :
    cornerBlockSucc (1 : α) (1 : Matrix (Fin m) (Fin m) α) = 1 := by
  refine ext_fin_succ ?_ (fun j ↦ ?_) (fun i ↦ ?_) (fun i j ↦ ?_) <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

/-- The conjugate transpose of `diag(c, B)` is `diag(star c, star B)`. -/
@[simp]
theorem star_cornerBlockSucc [AddMonoid α] [StarAddMonoid α] (c : α)
    (B : Matrix (Fin m) (Fin m) α) :
    star (cornerBlockSucc c B) = cornerBlockSucc (star c) (star B) := by
  refine ext_fin_succ ?_ (fun j ↦ ?_) (fun i ↦ ?_) (fun i j ↦ ?_) <;>
    simp [star_eq_conjTranspose, conjTranspose_apply]

end Matrix
