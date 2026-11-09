/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Block-diagonal embeddings of unitary and special orthogonal groups

For natural numbers `r` and `m`, a matrix `B` of size `m` gives the block-diagonal matrix
`diag(1_r, B)` of size `r + m`, the identity block occupying the first `r` coordinates of
`Fin (r + m)` (through `finSumFinEquiv`). This is a block matrix `Matrix.fromBlocks 1 0 0 B`,
and it is unitary, respectively special orthogonal, exactly when `B` is. So it embeds `U(m)` in
`U(r + m)` and `SO(m)` in `SO(r + m)`.

Its image is the subgroup fixing the first `r` standard basis vectors
(`Matrix.UnitaryGroup.mem_range_fromBlocksOne_iff`,
`Matrix.SpecialOrthogonalGroup.mem_range_fromBlocksOne_iff`): a unitary matrix whose first `r`
columns are standard basis vectors also has those standard basis vectors as its first `r` rows,
since its inverse is its conjugate transpose. This identifies the stabilizer of an orthonormal
`r`-frame, the subgroup by which the unitary and special orthogonal groups are divided to obtain
the manifolds of orthonormal frames.

## Main definitions

* `Matrix.UnitaryGroup.fromBlocksOne`: the embedding `B ↦ diag(1_r, B)` of `U(m)` in `U(r + m)`.
* `Matrix.SpecialOrthogonalGroup.fromBlocksOne`: the embedding of `SO(m)` in `SO(r + m)`.

## Main results

* `Matrix.fromBlocks_one_zero_zero_mem_unitaryGroup_iff`: `diag(1, B)` is unitary exactly when
  `B` is.
* `Matrix.UnitaryGroup.mem_range_fromBlocksOne_iff`,
  `Matrix.SpecialOrthogonalGroup.mem_range_fromBlocksOne_iff`: the image of the embedding is the
  subgroup fixing the first `r` standard basis vectors.
-/

public section

open Fin

namespace Matrix

section Unitary

variable {α : Type*} [CommRing α] [StarRing α]

/-- The block-diagonal matrix `diag(1, B)` is unitary exactly when `B` is unitary. -/
theorem fromBlocks_one_zero_zero_mem_unitaryGroup_iff {l n : Type*} [Fintype l] [DecidableEq l]
    [Fintype n] [DecidableEq n] {B : Matrix n n α} :
    fromBlocks (1 : Matrix l l α) 0 0 B ∈ unitaryGroup (l ⊕ n) α ↔ B ∈ unitaryGroup n α := by
  simp only [mem_unitaryGroup_iff', star_eq_conjTranspose, fromBlocks_conjTranspose,
    conjTranspose_one, conjTranspose_zero, fromBlocks_multiply, Matrix.mul_one, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, ← fromBlocks_one, fromBlocks_inj, true_and]

namespace UnitaryGroup

variable (α) (r : ℕ) {m : ℕ}

variable (m) in
/-- The **block-diagonal embedding** `B ↦ diag(1_r, B)` of the unitary group `U(m)` in
`U(r + m)`: the identity block occupies the first `r` coordinates of `Fin (r + m)`. -/
def fromBlocksOne : unitaryGroup (Fin m) α →* unitaryGroup (Fin (r + m)) α where
  toFun B := ⟨reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 0 (B : Matrix _ _ α)),
    submatrix_equiv_mem_unitary.2 (fromBlocks_one_zero_zero_mem_unitaryGroup_iff.2 B.2)⟩
  map_one' := Subtype.ext <| by simp [fromBlocks_one]
  map_mul' A B := Subtype.ext <| by
    simp only [reindex_apply, Submonoid.coe_mul, submatrix_mul_equiv, fromBlocks_multiply,
      Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem coe_fromBlocksOne (B : unitaryGroup (Fin m) α) :
    (fromBlocksOne α r m B : Matrix (Fin (r + m)) (Fin (r + m)) α) =
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 0 (B : Matrix _ _ α)) :=
  (rfl)

@[simp]
theorem fromBlocksOne_apply_castAdd_castAdd (B : unitaryGroup (Fin m) α) (i j : Fin r) :
    (fromBlocksOne α r m B : Matrix (Fin (r + m)) (Fin (r + m)) α) (castAdd m i) (castAdd m j) =
      if i = j then 1 else 0 := by
  simp [coe_fromBlocksOne, Matrix.one_apply]

@[simp]
theorem fromBlocksOne_apply_castAdd_natAdd (B : unitaryGroup (Fin m) α) (i : Fin r) (k : Fin m) :
    (fromBlocksOne α r m B : Matrix (Fin (r + m)) (Fin (r + m)) α) (castAdd m i) (natAdd r k) =
      0 := by
  simp [coe_fromBlocksOne]

@[simp]
theorem fromBlocksOne_apply_natAdd_castAdd (B : unitaryGroup (Fin m) α) (k : Fin m) (i : Fin r) :
    (fromBlocksOne α r m B : Matrix (Fin (r + m)) (Fin (r + m)) α) (natAdd r k) (castAdd m i) =
      0 := by
  simp [coe_fromBlocksOne]

@[simp]
theorem fromBlocksOne_apply_natAdd_natAdd (B : unitaryGroup (Fin m) α) (k l : Fin m) :
    (fromBlocksOne α r m B : Matrix (Fin (r + m)) (Fin (r + m)) α) (natAdd r k) (natAdd r l) =
      (B : Matrix (Fin m) (Fin m) α) k l := by
  simp [coe_fromBlocksOne]

/-- The block-diagonal embedding of unitary groups is injective. -/
theorem fromBlocksOne_injective : Function.Injective (fromBlocksOne α r m) := fun A B h ↦
  UnitaryGroup.ext A B fun k l ↦ by
    simpa using congrFun (congrFun (congrArg Subtype.val h) (natAdd r k)) (natAdd r l)

variable {α r}

/-- **The block-diagonal unitary matrices are the stabilizer of the first `r` basis vectors**:
a unitary matrix of size `r + m` lies in the image of `U(m)` exactly when it fixes the standard
basis vectors `e₀, …, e_{r-1}`. -/
theorem mem_range_fromBlocksOne_iff {A : unitaryGroup (Fin (r + m)) α} :
    A ∈ (fromBlocksOne α r m).range ↔
      ∀ i : Fin r, A.1 *ᵥ Pi.single (castAdd m i) 1 = Pi.single (castAdd m i) 1 := by
  refine ⟨?_, fun hA ↦ ?_⟩
  · rintro ⟨B, rfl⟩ i
    ext p
    refine Fin.addCases (fun j ↦ ?_) (fun k ↦ ?_) p
    · simp [Pi.single_apply, eq_comm]
    · have hk : natAdd r k ≠ castAdd m i := fun h ↦ by
        have := congrArg Fin.val h
        simp only [val_natAdd, val_castAdd] at this
        omega
      simp [hk]
  -- The first `r` columns are standard basis vectors.
  have hcol : ∀ (p : Fin (r + m)) (i : Fin r),
      A.1 p (castAdd m i) = (Pi.single (castAdd m i) 1 : Fin (r + m) → α) p :=
    fun p i ↦ by simpa using congrFun (hA i) p
  -- Since `star A * A = 1`, so are the first `r` rows.
  have hrow : ∀ (i : Fin r) (q : Fin (r + m)),
      A.1 (castAdd m i) q = (1 : Matrix (Fin (r + m)) (Fin (r + m)) α) (castAdd m i) q :=
    fun i q ↦ by
      have h := congrFun (congrFun (mem_unitaryGroup_iff'.1 A.2) (castAdd m i)) q
      rw [star_eq_conjTranspose, Matrix.mul_apply] at h
      simpa [conjTranspose_apply, hcol, Pi.single_apply, apply_ite (star : α → α), ite_mul] using h
  let B : Matrix (Fin m) (Fin m) α := fun k l ↦ A.1 (natAdd r k) (natAdd r l)
  have hAB : A.1 = reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 0 B) := by
    ext p q
    refine Fin.addCases (fun i ↦ ?_) (fun k ↦ ?_) p <;>
      refine Fin.addCases (fun j ↦ ?_) (fun l ↦ ?_) q
    · simpa [Pi.single_apply, Matrix.one_apply, eq_comm] using hcol (castAdd m i) j
    · have hl : castAdd m i ≠ natAdd r l := fun h ↦ by
        have := congrArg Fin.val h
        simp only [val_natAdd, val_castAdd] at this
        omega
      simpa [Matrix.one_apply, hl] using hrow i (natAdd r l)
    · have hk : natAdd r k ≠ castAdd m j := fun h ↦ by
        have := congrArg Fin.val h
        simp only [val_natAdd, val_castAdd] at this
        omega
      simpa [Pi.single_apply, hk] using hcol (natAdd r k) j
    · simp only [reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_natAdd]
      rfl
  have hB : B ∈ unitaryGroup (Fin m) α := by
    rw [← fromBlocks_one_zero_zero_mem_unitaryGroup_iff (l := Fin r),
      ← submatrix_equiv_mem_unitary (e₁ := finSumFinEquiv.symm) (e₂ := finSumFinEquiv.symm)]
    simpa only [hAB, reindex_apply] using A.2
  exact ⟨⟨B, hB⟩, Subtype.ext hAB.symm⟩

end UnitaryGroup

end Unitary

namespace SpecialOrthogonalGroup

attribute [local instance] starRingOfComm

variable (R : Type*) [CommRing R] (r : ℕ) {m : ℕ}

variable (m) in
/-- The **block-diagonal embedding** `B ↦ diag(1_r, B)` of the special orthogonal group `SO(m)`
in `SO(r + m)`: the identity block occupies the first `r` coordinates of `Fin (r + m)`. -/
def fromBlocksOne : specialOrthogonalGroup (Fin m) R →* specialOrthogonalGroup (Fin (r + m)) R where
  toFun B := ⟨reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 0 (B : Matrix _ _ R)),
    submatrix_equiv_mem_unitary.2 (fromBlocks_one_zero_zero_mem_unitaryGroup_iff.2 B.2.1),
    by simpa [det_fromBlocks_zero₂₁] using B.2.2⟩
  map_one' := Subtype.ext <| by simp [fromBlocks_one]
  map_mul' A B := Subtype.ext <| by
    simp only [reindex_apply, Submonoid.coe_mul, submatrix_mul_equiv, fromBlocks_multiply,
      Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem coe_fromBlocksOne (B : specialOrthogonalGroup (Fin m) R) :
    (fromBlocksOne R r m B : Matrix (Fin (r + m)) (Fin (r + m)) R) =
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 0 (B : Matrix _ _ R)) :=
  (rfl)

@[simp]
theorem fromBlocksOne_apply_castAdd_castAdd (B : specialOrthogonalGroup (Fin m) R) (i j : Fin r) :
    (fromBlocksOne R r m B : Matrix (Fin (r + m)) (Fin (r + m)) R) (castAdd m i) (castAdd m j) =
      if i = j then 1 else 0 := by
  simp [coe_fromBlocksOne, Matrix.one_apply]

@[simp]
theorem fromBlocksOne_apply_castAdd_natAdd (B : specialOrthogonalGroup (Fin m) R) (i : Fin r)
    (k : Fin m) :
    (fromBlocksOne R r m B : Matrix (Fin (r + m)) (Fin (r + m)) R) (castAdd m i) (natAdd r k) =
      0 := by
  simp [coe_fromBlocksOne]

@[simp]
theorem fromBlocksOne_apply_natAdd_castAdd (B : specialOrthogonalGroup (Fin m) R) (k : Fin m)
    (i : Fin r) :
    (fromBlocksOne R r m B : Matrix (Fin (r + m)) (Fin (r + m)) R) (natAdd r k) (castAdd m i) =
      0 := by
  simp [coe_fromBlocksOne]

@[simp]
theorem fromBlocksOne_apply_natAdd_natAdd (B : specialOrthogonalGroup (Fin m) R) (k l : Fin m) :
    (fromBlocksOne R r m B : Matrix (Fin (r + m)) (Fin (r + m)) R) (natAdd r k) (natAdd r l) =
      (B : Matrix (Fin m) (Fin m) R) k l := by
  simp [coe_fromBlocksOne]

/-- The block-diagonal embedding of special orthogonal groups is injective. -/
theorem fromBlocksOne_injective : Function.Injective (fromBlocksOne R r m) := fun A B h ↦
  Subtype.ext <| funext fun k ↦ funext fun l ↦ by
    simpa [coe_fromBlocksOne] using
      congrFun (congrFun (congrArg Subtype.val h) (natAdd r k)) (natAdd r l)

variable {R r}

/-- **The block-diagonal special orthogonal matrices are the stabilizer of the first `r` basis
vectors**: a special orthogonal matrix of size `r + m` lies in the image of `SO(m)` exactly when
it fixes the standard basis vectors `e₀, …, e_{r-1}`. -/
theorem mem_range_fromBlocksOne_iff {A : specialOrthogonalGroup (Fin (r + m)) R} :
    A ∈ (fromBlocksOne R r m).range ↔
      ∀ i : Fin r, A.1 *ᵥ Pi.single (castAdd m i) 1 = Pi.single (castAdd m i) 1 := by
  refine ⟨?_, fun hA ↦ ?_⟩
  · rintro ⟨B, rfl⟩
    intro i
    ext p
    refine Fin.addCases (fun j ↦ ?_) (fun k ↦ ?_) p
    · simp [coe_fromBlocksOne, Pi.single_apply, Matrix.one_apply, eq_comm]
    · have hk : natAdd r k ≠ castAdd m i := fun h ↦ by
        have := congrArg Fin.val h
        simp only [val_natAdd, val_castAdd] at this
        omega
      simp [coe_fromBlocksOne, hk]
  obtain ⟨B, hB⟩ := (UnitaryGroup.mem_range_fromBlocksOne_iff
    (A := (⟨A.1, A.2.1⟩ : unitaryGroup (Fin (r + m)) R))).2 hA
  have hdet : (B : Matrix (Fin m) (Fin m) R).det = 1 := by
    have h := A.2.2
    rw [← congrArg Subtype.val hB] at h
    simpa [UnitaryGroup.coe_fromBlocksOne, det_fromBlocks_zero₂₁] using h
  exact ⟨⟨B, B.2, hdet⟩, Subtype.ext <| (coe_fromBlocksOne R r _).trans <|
    (UnitaryGroup.coe_fromBlocksOne R r B).symm.trans (congrArg Subtype.val hB)⟩

end SpecialOrthogonalGroup

end Matrix
