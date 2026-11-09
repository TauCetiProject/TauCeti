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

Similarly, a unitary scalar `c` and a unitary matrix `B` of size `m` give the block-diagonal
unitary matrix `diag(c, B)` of size `m + 1`, with `c` in the corner indexed by `0`. This embeds
`U(1) × U(m)` in `U(m + 1)`, and its image consists of the unitary matrices whose column `0` is a
multiple of `e₀` (`Matrix.UnitaryGroup.mem_range_prodBlockSucc_iff`): the stabilizer of the line
spanned by `e₀`.

## Main definitions

* `Matrix.UnitaryGroup.fromBlocksOne`: the embedding `B ↦ diag(1_r, B)` of `U(m)` in `U(r + m)`.
* `Matrix.SpecialOrthogonalGroup.fromBlocksOne`: the embedding of `SO(m)` in `SO(r + m)`.
* `Matrix.UnitaryGroup.prodBlockSucc`: the embedding `(c, B) ↦ diag(c, B)` of `U(1) × U(m)` in
  `U(m + 1)`.

## Main results

* `Matrix.fromBlocks_zero_zero_mem_unitaryGroup_iff`: `diag(A, B)` is unitary exactly when both
  `A` and `B` are.
* `Matrix.UnitaryGroup.mem_range_fromBlocksOne_iff`,
  `Matrix.SpecialOrthogonalGroup.mem_range_fromBlocksOne_iff`: the image of the embedding is the
  subgroup fixing the first `r` standard basis vectors.
* `Matrix.UnitaryGroup.mem_range_prodBlockSucc_iff`: the image of `U(1) × U(m)` is the subgroup of
  unitary matrices whose column `0` vanishes below the corner.
-/

public section

open Fin

namespace Matrix

section Unitary

variable {α : Type*} [CommRing α] [StarRing α]

/-- The block-diagonal matrix `diag(A, B)` is unitary exactly when both blocks are unitary. -/
theorem fromBlocks_zero_zero_mem_unitaryGroup_iff {l n : Type*} [Fintype l] [DecidableEq l]
    [Fintype n] [DecidableEq n] {A : Matrix l l α} {B : Matrix n n α} :
    fromBlocks A 0 0 B ∈ unitaryGroup (l ⊕ n) α ↔
      A ∈ unitaryGroup l α ∧ B ∈ unitaryGroup n α := by
  simp only [mem_unitaryGroup_iff', star_eq_conjTranspose, fromBlocks_conjTranspose,
    conjTranspose_zero, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    ← fromBlocks_one, fromBlocks_inj, true_and]

namespace UnitaryGroup

variable (α) (r : ℕ) {m : ℕ}

variable (m) in
/-- The **block-diagonal embedding** `B ↦ diag(1_r, B)` of the unitary group `U(m)` in
`U(r + m)`: the identity block occupies the first `r` coordinates of `Fin (r + m)`. -/
def fromBlocksOne : unitaryGroup (Fin m) α →* unitaryGroup (Fin (r + m)) α where
  toFun B := ⟨reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 0 (B : Matrix _ _ α)),
    submatrix_equiv_mem_unitary.2 (fromBlocks_zero_zero_mem_unitaryGroup_iff.2 ⟨one_mem _, B.2⟩)⟩
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
    have h := A.2
    rw [hAB, reindex_apply, submatrix_equiv_mem_unitary,
      fromBlocks_zero_zero_mem_unitaryGroup_iff] at h
    exact h.2
  exact ⟨⟨B, hB⟩, Subtype.ext hAB.symm⟩

section Succ

variable {m : ℕ}

private theorem finSumFinEquiv_trans_finCongr_symm_zero :
    (finSumFinEquiv.trans (finCongr (add_comm 1 m))).symm 0 = Sum.inl 0 := by
  rw [Equiv.symm_apply_eq]
  ext
  simp

private theorem finSumFinEquiv_trans_finCongr_symm_succ (j : Fin m) :
    (finSumFinEquiv.trans (finCongr (add_comm 1 m))).symm j.succ = Sum.inr j := by
  rw [Equiv.symm_apply_eq]
  ext
  simp

variable (α m) in
/-- The **block-diagonal embedding** `(c, B) ↦ diag(c, B)` of `U(1) × U(m)` in `U(m + 1)`: the
unitary scalar `c` occupies the corner indexed by `0`, and `B` the indices `Fin.succ`. It is the
block matrix `Matrix.fromBlocks c 0 0 B`, reindexed along `Fin 1 ⊕ Fin m ≃ Fin (m + 1)`. -/
def prodBlockSucc : unitary α × unitaryGroup (Fin m) α →* unitaryGroup (Fin (m + 1)) α where
  toFun cB := ⟨reindex (finSumFinEquiv.trans (finCongr (add_comm 1 m)))
      (finSumFinEquiv.trans (finCongr (add_comm 1 m)))
      (fromBlocks (diagonal fun _ ↦ (cB.1 : α)) 0 0 (cB.2 : Matrix _ _ α)),
    submatrix_equiv_mem_unitary.2 (fromBlocks_zero_zero_mem_unitaryGroup_iff.2
      ⟨diagonal_mem_unitary.2 (Pi.const_mem_unitary_iff.2 cB.1.2), cB.2.2⟩)⟩
  map_one' := Subtype.ext <| by
    simp only [Prod.fst_one, Prod.snd_one, OneMemClass.coe_one, diagonal_one, fromBlocks_one,
      reindex_apply, submatrix_one_equiv]
  map_mul' _ _ := Subtype.ext <| by
    simp only [reindex_apply, Submonoid.coe_mul, submatrix_mul_equiv, fromBlocks_multiply,
      Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, diagonal_mul_diagonal, Prod.fst_mul,
      Prod.snd_mul]

theorem coe_prodBlockSucc (cB : unitary α × unitaryGroup (Fin m) α) :
    (prodBlockSucc α m cB : Matrix (Fin (m + 1)) (Fin (m + 1)) α) =
      reindex (finSumFinEquiv.trans (finCongr (add_comm 1 m)))
        (finSumFinEquiv.trans (finCongr (add_comm 1 m)))
        (fromBlocks (diagonal fun _ ↦ (cB.1 : α)) 0 0 (cB.2 : Matrix _ _ α)) :=
  (rfl)

@[simp]
theorem prodBlockSucc_apply_zero_zero (cB : unitary α × unitaryGroup (Fin m) α) :
    (prodBlockSucc α m cB : Matrix (Fin (m + 1)) (Fin (m + 1)) α) 0 0 = cB.1 := by
  rw [coe_prodBlockSucc, reindex_apply, submatrix_apply, finSumFinEquiv_trans_finCongr_symm_zero,
    fromBlocks_apply₁₁, diagonal_apply_eq]

@[simp]
theorem prodBlockSucc_apply_zero_succ (cB : unitary α × unitaryGroup (Fin m) α) (j : Fin m) :
    (prodBlockSucc α m cB : Matrix (Fin (m + 1)) (Fin (m + 1)) α) 0 j.succ = 0 := by
  rw [coe_prodBlockSucc, reindex_apply, submatrix_apply, finSumFinEquiv_trans_finCongr_symm_zero,
    finSumFinEquiv_trans_finCongr_symm_succ, fromBlocks_apply₁₂]
  rfl

@[simp]
theorem prodBlockSucc_apply_succ_zero (cB : unitary α × unitaryGroup (Fin m) α) (i : Fin m) :
    (prodBlockSucc α m cB : Matrix (Fin (m + 1)) (Fin (m + 1)) α) i.succ 0 = 0 := by
  rw [coe_prodBlockSucc, reindex_apply, submatrix_apply, finSumFinEquiv_trans_finCongr_symm_zero,
    finSumFinEquiv_trans_finCongr_symm_succ, fromBlocks_apply₂₁]
  rfl

@[simp]
theorem prodBlockSucc_apply_succ_succ (cB : unitary α × unitaryGroup (Fin m) α) (i j : Fin m) :
    (prodBlockSucc α m cB : Matrix (Fin (m + 1)) (Fin (m + 1)) α) i.succ j.succ =
      (cB.2 : Matrix (Fin m) (Fin m) α) i j := by
  rw [coe_prodBlockSucc, reindex_apply, submatrix_apply, finSumFinEquiv_trans_finCongr_symm_succ,
    finSumFinEquiv_trans_finCongr_symm_succ, fromBlocks_apply₂₂]

/-- The block-diagonal embedding of `U(1) × U(m)` in `U(m + 1)` is injective. -/
theorem prodBlockSucc_injective : Function.Injective (prodBlockSucc α m) := by
  rintro ⟨c, B⟩ ⟨c', B'⟩ h
  have h' := congrArg Subtype.val h
  refine Prod.ext (Subtype.ext ?_) (UnitaryGroup.ext B B' fun i j ↦ ?_)
  · simpa using congrFun (congrFun h' 0) 0
  · simpa using congrFun (congrFun h' i.succ) j.succ

/-- **The block-diagonal unitary matrices `diag(c, B)` are those whose first column is a multiple
of `e₀`**: a unitary matrix of size `m + 1` lies in the image of `U(1) × U(m)` exactly when its
entries below the corner in the column `0` vanish. The entries to the right of the corner then
vanish too, since the inverse of a unitary matrix is its conjugate transpose. -/
theorem mem_range_prodBlockSucc_iff {A : unitaryGroup (Fin (m + 1)) α} :
    A ∈ (prodBlockSucc α m).range ↔
      ∀ i : Fin m, (A : Matrix (Fin (m + 1)) (Fin (m + 1)) α) i.succ 0 = 0 := by
  refine ⟨?_, fun hA ↦ ?_⟩
  · rintro ⟨cB, rfl⟩ i
    exact prodBlockSucc_apply_succ_zero cB i
  have hentry (p q : Fin (m + 1)) : ∑ k, star (A.1 k p) * A.1 k q = if p = q then 1 else 0 := by
    simpa [Matrix.mul_apply, star_eq_conjTranspose, Matrix.one_apply] using
      congrFun (congrFun (mem_unitaryGroup_iff'.1 A.2) p) q
  -- The corner is a unitary scalar.
  have hc : star (A.1 0 0) * A.1 0 0 = 1 := by simpa [Fin.sum_univ_succ, hA] using hentry 0 0
  -- The row `0` vanishes off the corner.
  have hrow (j : Fin m) : A.1 0 j.succ = 0 := by
    have h := hentry 0 j.succ
    simp only [Fin.sum_univ_succ, hA, star_zero, zero_mul, Finset.sum_const_zero, add_zero,
      (Fin.succ_ne_zero j).symm, ite_false] at h
    calc A.1 0 j.succ = A.1 0 0 * star (A.1 0 0) * A.1 0 j.succ := by
          rw [mul_comm (A.1 0 0), hc, one_mul]
      _ = 0 := by rw [mul_assoc, h, mul_zero]
  let B : Matrix (Fin m) (Fin m) α := fun i j ↦ A.1 i.succ j.succ
  have hAB : A.1 = reindex (finSumFinEquiv.trans (finCongr (add_comm 1 m)))
      (finSumFinEquiv.trans (finCongr (add_comm 1 m)))
      (fromBlocks (diagonal fun _ ↦ A.1 0 0) 0 0 B) := by
    ext p q
    refine Fin.cases ?_ (fun i ↦ ?_) p <;> refine Fin.cases ?_ (fun j ↦ ?_) q <;>
      simp only [reindex_apply, submatrix_apply, finSumFinEquiv_trans_finCongr_symm_zero,
        finSumFinEquiv_trans_finCongr_symm_succ, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        fromBlocks_apply₂₁, fromBlocks_apply₂₂, diagonal_apply_eq] <;>
      first | rfl | exact hrow j | exact hA i
  have hB : B ∈ unitaryGroup (Fin m) α := by
    have h := A.2
    rw [hAB, reindex_apply, submatrix_equiv_mem_unitary,
      fromBlocks_zero_zero_mem_unitaryGroup_iff] at h
    exact h.2
  exact ⟨(⟨A.1 0 0, Unitary.mem_iff_star_mul_self.2 hc⟩, ⟨B, hB⟩), Subtype.ext hAB.symm⟩

end Succ

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
    submatrix_equiv_mem_unitary.2
      (fromBlocks_zero_zero_mem_unitaryGroup_iff.2 ⟨one_mem _, B.2.1⟩),
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
