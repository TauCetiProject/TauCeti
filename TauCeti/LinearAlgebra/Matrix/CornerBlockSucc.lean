/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import TauCeti.LinearAlgebra.Matrix.Defs
public import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# The block-diagonal matrix `diag(c, B)` and upper-bordered matrices of size `m + 1`

A scalar `c` and a square matrix `B` of size `m` give the block-diagonal matrix `diag(c, B)` of
size `m + 1`, with `c` in the corner indexed by `0` and `B` on the indices `Fin.succ`. This file
builds it and shows that it multiplies blockwise and commutes with the star operation. No
commutativity is assumed, so the construction applies to quaternionic matrices.

Alongside it, `Matrix.upperBorder w M` builds the upper-bordered matrix `[[1, w], [0, M]]` of size
`m + 1`, together with its unit constructor `Matrix.upperBorderUnit w g` for invertible `g`,
characterizing multiplication, mapping, upper unitriangularity, action on `Pi.single 0 1`, and
congruence of `cornerBlockSucc d₀ B`.

`TauCeti/LinearAlgebra/Matrix/UnitaryGroup/CornerBlock.lean` deduces from `cornerBlockSucc` the
block-diagonal embedding `U(1) × U(m) → U(m + 1)`.

## Main definitions

* `Matrix.cornerBlockSucc`: the block-diagonal matrix `diag(c, B)` of size `m + 1`, with the scalar
  `c` in the corner indexed by `0`.
* `Matrix.upperBorder`: the upper-bordered matrix `[[1, w], [0, M]]` of size `m + 1`.
* `Matrix.upperBorderUnit`: `upperBorder w g` as a unit of `Matrix (Fin (m + 1)) (Fin (m + 1)) R`.

## Main results

* `Matrix.cornerBlockSucc_inj`, `Matrix.cornerBlockSucc_diagonal`: injectivity and compatibility
  with `Matrix.diagonal`.
* `Matrix.cornerBlockSucc_mul_cornerBlockSucc`, `Matrix.cornerBlockSucc_one`,
  `Matrix.star_cornerBlockSucc`: `diag(c, B)` is multiplicative and unital, and commutes with the
  star operation, blockwise.
* `Matrix.upperBorder_inj`, `Matrix.col_upperBorder_zero`, `Matrix.upperBorder_zero_one`,
  `Matrix.upperBorder_mul_upperBorder`, `Matrix.upperBorder_map`,
  `Matrix.isUpperUnitriangular_upperBorder_iff`,
  `Matrix.transpose_upperBorder_mul_cornerBlockSucc_mul`: algebraic and congruence laws for
  `upperBorder`.
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

/-- Placing `c` in the corner of a diagonal matrix yields the diagonal matrix of `Fin.cons c d`. -/
@[simp] theorem cornerBlockSucc_diagonal (c : α) (d : Fin m → α) :
    cornerBlockSucc c (diagonal d) = diagonal (Fin.cons c d) := by
  refine ext_fin_succ ?_ (fun _ ↦ ?_) (fun _ ↦ ?_) (fun _ _ ↦ ?_) <;>
    simp [diagonal_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

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

section UpperBorder

section ZeroOne
variable [Zero α] [One α]

/-- The upper-bordered matrix `[[1, w], [0, M]]` of size `m + 1`, with top row `(1, w)`,
first column `(1, 0)`, and lower-right block `M`. -/
def upperBorder (w : Fin m → α) (M : Matrix (Fin m) (Fin m) α) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) α :=
  of (Fin.cons (Fin.cons 1 w) fun i ↦ Fin.cons 0 (M i))

@[simp] theorem upperBorder_zero_zero (w : Fin m → α) (M : Matrix (Fin m) (Fin m) α) :
    upperBorder w M 0 0 = 1 := (rfl)

@[simp] theorem upperBorder_zero_succ (w : Fin m → α) (M : Matrix (Fin m) (Fin m) α) (j : Fin m) :
    upperBorder w M 0 j.succ = w j := (rfl)

@[simp] theorem upperBorder_succ_zero (w : Fin m → α) (M : Matrix (Fin m) (Fin m) α) (i : Fin m) :
    upperBorder w M i.succ 0 = 0 := (rfl)

@[simp] theorem upperBorder_succ_succ (w : Fin m → α) (M : Matrix (Fin m) (Fin m) α) (i j : Fin m) :
    upperBorder w M i.succ j.succ = M i j := (rfl)

/-- The upper-bordered matrix `[[1, w], [0, M]]` determines its row `w` and block `M`. -/
@[simp] theorem upperBorder_inj {w w' : Fin m → α} {M M' : Matrix (Fin m) (Fin m) α} :
    upperBorder w M = upperBorder w' M' ↔ w = w' ∧ M = M' :=
  ⟨fun h ↦ ⟨funext fun j ↦ by simpa using congrFun (congrFun h 0) j.succ,
    Matrix.ext fun i j ↦ by simpa using congrFun (congrFun h i.succ) j.succ⟩,
    fun h ↦ h.1 ▸ h.2 ▸ rfl⟩

/-- The zeroth column of `upperBorder w M` is `Pi.single 0 1`. -/
@[simp] theorem col_upperBorder_zero (w : Fin m → α) (M : Matrix (Fin m) (Fin m) α) :
    (upperBorder w M).col 0 = Pi.single 0 1 := by
  ext p; refine Fin.cases ?_ (fun _ ↦ ?_) p <;> simp [Fin.succ_ne_zero]

/-- Bordering the identity matrix with zero gives the identity matrix. -/
@[simp] theorem upperBorder_zero_one :
    upperBorder (0 : Fin m → α) (1 : Matrix (Fin m) (Fin m) α) = 1 := by
  refine ext_fin_succ ?_ (fun _ ↦ ?_) (fun _ ↦ ?_) (fun _ _ ↦ ?_) <;>
    simp [Matrix.one_apply, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

/-- `upperBorder w M` is upper unitriangular if and only if `M` is. -/
@[simp] theorem isUpperUnitriangular_upperBorder_iff (w : Fin m → α)
    (M : Matrix (Fin m) (Fin m) α) :
    (upperBorder w M).IsUpperUnitriangular ↔ M.IsUpperUnitriangular :=
  ⟨fun h ↦ (isUpperUnitriangular_def M).mpr ⟨fun _ _ hji ↦
      h.isUpperTriangular (Fin.succ_lt_succ_iff.mpr hji), fun i ↦ h.apply_diag i.succ⟩,
    fun hM ↦ (isUpperUnitriangular_def _).mpr ⟨fun i j hji ↦ Fin.cases
      (fun h : j < 0 ↦ (Fin.not_lt_zero j h).elim) (fun _ hji' ↦ Fin.cases (fun _ ↦ rfl)
        (fun _ h ↦ hM.isUpperTriangular (Fin.succ_lt_succ_iff.mp h)) j hji') i hji,
      Fin.cases rfl hM.apply_diag⟩⟩

/-- Applying a zero- and one-preserving map entrywise preserves `upperBorder`. -/
theorem upperBorder_map {β F : Type*} [Zero β] [One β] [FunLike F α β] [ZeroHomClass F α β]
    [OneHomClass F α β] (f : F) (w : Fin m → α) (M : Matrix (Fin m) (Fin m) α) :
    (upperBorder w M).map f = upperBorder (f ∘ w) (M.map f) := by
  refine ext_fin_succ ?_ (fun _ ↦ ?_) (fun _ ↦ ?_) (fun _ _ ↦ ?_) <;> simp

end ZeroOne

/-- Block multiplication of upper-bordered matrices. -/
@[simp] theorem upperBorder_mul_upperBorder [Semiring α] (w₁ w₂ : Fin m → α)
    (M₁ M₂ : Matrix (Fin m) (Fin m) α) :
    upperBorder w₁ M₁ * upperBorder w₂ M₂ = upperBorder (w₂ + w₁ ᵥ* M₂) (M₁ * M₂) := by
  refine ext_fin_succ ?_ (fun _ ↦ ?_) (fun _ ↦ ?_) (fun _ _ ↦ ?_) <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, vecMul, dotProduct]

/-- Congruence of `cornerBlockSucc d₀ B` by `upperBorder w M`. -/
theorem transpose_upperBorder_mul_cornerBlockSucc_mul [CommSemiring α] (d₀ : α)
    (B : Matrix (Fin m) (Fin m) α) (w : Fin m → α) (M : Matrix (Fin m) (Fin m) α) :
    (upperBorder w M)ᵀ * cornerBlockSucc d₀ B * upperBorder w M =
      of (Fin.cons (Fin.cons d₀ (fun j ↦ d₀ * w j))
        fun i ↦ Fin.cons (w i * d₀) (fun j ↦ d₀ * w i * w j + (Mᵀ * B * M) i j)) := by
  refine ext_fin_succ ?_ (fun _ ↦ ?_) (fun _ ↦ ?_) (fun i j ↦ ?_) <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, mul_comm (w _)]

/-- Package `upperBorder w g` as a unit of `Matrix (Fin (m + 1)) (Fin (m + 1)) α` when `g` is a
unit of `Matrix (Fin m) (Fin m) α`. -/
def upperBorderUnit [Ring α] (w : Fin m → α) (g : (Matrix (Fin m) (Fin m) α)ˣ) :
    (Matrix (Fin (m + 1)) (Fin (m + 1)) α)ˣ where
  val := upperBorder w g.val
  inv := upperBorder (-(w ᵥ* (g⁻¹).val)) (g⁻¹).val
  val_inv := by
    rw [upperBorder_mul_upperBorder, Units.mul_inv, neg_add_cancel, upperBorder_zero_one]
  inv_val := by rw [upperBorder_mul_upperBorder, Units.inv_mul, neg_vecMul, vecMul_vecMul,
    Units.inv_mul, vecMul_one, add_neg_cancel, upperBorder_zero_one]

/-- The underlying matrix of `upperBorderUnit w g` is `upperBorder w g`. -/
@[simp] theorem coe_upperBorderUnit [Ring α] (w : Fin m → α) (g : (Matrix (Fin m) (Fin m) α)ˣ) :
    (upperBorderUnit w g : Matrix (Fin (m + 1)) (Fin (m + 1)) α) = upperBorder w g.val := (rfl)

/-- The inverse of `upperBorderUnit w g` has row `-(w ᵥ* g⁻¹)` and lower-right block `g⁻¹`. -/
@[simp] theorem upperBorderUnit_inv [Ring α] (w : Fin m → α) (g : (Matrix (Fin m) (Fin m) α)ˣ) :
    (upperBorderUnit w g)⁻¹ = upperBorderUnit (-(w ᵥ* (g⁻¹).val)) g⁻¹ := Units.ext (rfl)

end UpperBorder

end Matrix
