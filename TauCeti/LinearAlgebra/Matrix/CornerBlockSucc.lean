/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.LinearAlgebra.Matrix.Defs

/-!
# The block-diagonal matrix `diag(c, B)` of size `m + 1`

A scalar `c` and a square matrix `B` of size `m` give the block-diagonal matrix `diag(c, B)` of
size `m + 1`, with `c` in the corner indexed by `0` and `B` on the indices `Fin.succ`. This file
builds it and shows that it multiplies blockwise, commutes with transpose, entrywise maps, and the
star operation, and has determinant `c * B.det` over a commutative ring. No commutativity is
assumed for the blockwise multiplication and star identities, so those apply to quaternionic
matrices.

`TauCeti/LinearAlgebra/Matrix/UnitaryGroup/CornerBlock.lean` deduces from this the block-diagonal
embedding `U(1) × U(m) → U(m + 1)`.

## Main definitions

* `Matrix.cornerBlockSucc`: the block-diagonal matrix `diag(c, B)` of size `m + 1`, with the scalar
  `c` in the corner indexed by `0`.

## Main results

* `Matrix.cornerBlockSucc_inj`: `diag(c, B)` determines `c` and `B`;
  `Matrix.submatrix_succ_succ_cornerBlockSucc`: removing its first row and column leaves `B`.
* `Matrix.transpose_cornerBlockSucc`, `Matrix.map_cornerBlockSucc`, `Matrix.star_cornerBlockSucc`:
  `diag(c, B)` commutes with transpose, entrywise maps preserving `0`, and `star`.
* `Matrix.cornerBlockSucc_mul_cornerBlockSucc`, `Matrix.cornerBlockSucc_one`: `diag(c, B)` is
  multiplicative and unital blockwise.
* `Matrix.cornerBlockSucc_diagonal`, `Matrix.det_cornerBlockSucc`: `diag(c, diag(d))` is diagonal,
  and over a commutative ring `diag(c, B)` has determinant `c * det B`.
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

/-- Defining formula for `Matrix.cornerBlockSucc` in terms of `Fin.cons`. -/
theorem cornerBlockSucc_def (c : α) (B : Matrix (Fin m) (Fin m) α) :
    cornerBlockSucc c B = of (Fin.cons (Fin.cons c 0) fun i ↦ Fin.cons 0 (B i)) :=
  (rfl)

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

/-- The transpose of `diag(c, B)` is `diag(c, Bᵀ)`. -/
@[simp]
theorem transpose_cornerBlockSucc (c : α) (B : Matrix (Fin m) (Fin m) α) :
    (cornerBlockSucc c B)ᵀ = cornerBlockSucc c Bᵀ := by
  refine ext_fin_succ ?_ (fun j ↦ ?_) (fun i ↦ ?_) (fun i j ↦ ?_) <;> simp

/-- Mapping a zero-preserving function over `diag(c, B)` gives `diag(f c, B.map f)`. -/
@[simp]
theorem map_cornerBlockSucc {β F : Type*} [Zero β] [FunLike F α β] [ZeroHomClass F α β]
    (f : F) (c : α) (B : Matrix (Fin m) (Fin m) α) :
    (cornerBlockSucc c B).map f = cornerBlockSucc (f c) (B.map f) := by
  refine ext_fin_succ ?_ (fun j ↦ ?_) (fun i ↦ ?_) (fun i j ↦ ?_) <;> simp

/-- Removing the row and the column indexed by `0` from `diag(c, B)` leaves `B`. -/
@[simp]
theorem submatrix_succ_succ_cornerBlockSucc (c : α) (B : Matrix (Fin m) (Fin m) α) :
    (cornerBlockSucc c B).submatrix Fin.succ Fin.succ = B := by
  ext i j
  simp

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

/-- The block-diagonal matrix `diag(c, diag(d))` is the diagonal matrix with entries
`c, d₀, d₁, …`. -/
theorem cornerBlockSucc_diagonal [Zero α] (c : α) (d : Fin m → α) :
    cornerBlockSucc c (diagonal d) = diagonal (Fin.cons c d) := by
  refine ext_fin_succ ?_ (fun j ↦ ?_) (fun i ↦ ?_) (fun i j ↦ ?_) <;>
    simp [diagonal_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

/-- Over a commutative ring, the block-diagonal matrix `diag(c, B)` has determinant `c * det B`. -/
@[simp]
theorem det_cornerBlockSucc [CommRing α] (c : α) (B : Matrix (Fin m) (Fin m) α) :
    (cornerBlockSucc c B).det = c * B.det := by
  rw [det_succ_row_zero, Fin.sum_univ_succ]
  simp [submatrix_succ_succ_cornerBlockSucc]

end Matrix
