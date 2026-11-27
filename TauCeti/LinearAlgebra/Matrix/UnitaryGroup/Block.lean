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
import TauCeti.Data.Fin.Basic

/-!
# Block-diagonal embeddings of unitary, special unitary and special orthogonal groups

For natural numbers `r` and `m`, a matrix `B` of size `m` gives the block-diagonal matrix
`diag(1_r, B)` of size `r + m`, the identity block occupying the first `r` coordinates of
`Fin (r + m)` (through `finSumFinEquiv`). This is a block matrix `Matrix.fromBlocks 1 0 0 B`,
and it is unitary, respectively special unitary or special orthogonal, exactly when `B` is, since
its determinant is that of `B`. So it embeds `U(m)` in `U(r + m)`, `SU(m)` in `SU(r + m)` and
`SO(m)` in `SO(r + m)`.

Its image is the subgroup fixing the first `r` standard basis vectors
(`Matrix.UnitaryGroup.mem_range_fromBlocksOne_iff`,
`Matrix.specialUnitaryGroup.mem_range_fromBlocksOne_iff`,
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
* `Matrix.specialUnitaryGroup.fromBlocksOne`: the embedding of `SU(m)` in `SU(r + m)`.
* `Matrix.SpecialOrthogonalGroup.fromBlocksOne`: the embedding of `SO(m)` in `SO(r + m)`, which is
  `Matrix.specialUnitaryGroup.fromBlocksOne` for the trivial star.
* `Matrix.UnitaryGroup.sum`: the block-diagonal sum `diag(U, V)` of two unitary matrices, as a
  group morphism `U(n) × U(m) →* U(n + m)`.
* `Matrix.UnitaryGroup.prodBlockSucc`: the embedding `(c, B) ↦ diag(c, B)` of `U(1) × U(m)` in
  `U(m + 1)`.

## Main results

* `Matrix.fromBlocks_zero_zero_mem_unitary_iff`,
  `Matrix.reindex_fromBlocks_zero_zero_mem_unitary_iff`: `diag(A, B)`, possibly reindexed,
  is unitary exactly when both `A` and `B` are.
* `Matrix.UnitaryGroup.mem_range_fromBlocksOne_iff`,
  `Matrix.specialUnitaryGroup.mem_range_fromBlocksOne_iff`,
  `Matrix.SpecialOrthogonalGroup.mem_range_fromBlocksOne_iff`: the image of the embedding is the
  subgroup fixing the first `r` standard basis vectors.
* `Matrix.UnitaryGroup.mem_range_prodBlockSucc_iff`: the image of `U(1) × U(m)` is the subgroup of
  unitary matrices whose column `0` vanishes below the corner.
-/

public section

open Fin

namespace Matrix

section Unitary

section Ring

variable {α : Type*} [Ring α] [StarRing α]

/-- The block-diagonal matrix `diag(A, B)` is unitary exactly when both blocks are unitary. -/
theorem fromBlocks_zero_zero_mem_unitary_iff {l n : Type*} [Fintype l] [DecidableEq l]
    [Fintype n] [DecidableEq n] {A : Matrix l l α} {B : Matrix n n α} :
    fromBlocks A 0 0 B ∈ unitary (Matrix (l ⊕ n) (l ⊕ n) α) ↔
      A ∈ unitary (Matrix l l α) ∧ B ∈ unitary (Matrix n n α) := by
  simp only [Unitary.mem_iff, star_eq_conjTranspose, fromBlocks_conjTranspose,
    conjTranspose_zero, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    ← fromBlocks_one, fromBlocks_inj, true_and]
  exact and_and_and_comm

/-- A reindexed block-diagonal matrix `diag(A, B)` is unitary exactly when both blocks are
unitary. -/
theorem reindex_fromBlocks_zero_zero_mem_unitary_iff {l n p : Type*} [Fintype l]
    [DecidableEq l] [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p] (e : l ⊕ n ≃ p)
    {A : Matrix l l α} {B : Matrix n n α} :
    reindex e e (fromBlocks A 0 0 B) ∈ unitary (Matrix p p α) ↔
      A ∈ unitary (Matrix l l α) ∧ B ∈ unitary (Matrix n n α) := by
  rw [reindex_apply, submatrix_equiv_mem_unitary, fromBlocks_zero_zero_mem_unitary_iff]

end Ring

variable {α : Type*} [CommRing α] [StarRing α]

namespace UnitaryGroup

variable (α) (r : ℕ) {m : ℕ}

variable (m) in
/-- The **block-diagonal embedding** `B ↦ diag(1_r, B)` of the unitary group `U(m)` in
`U(r + m)`: the identity block occupies the first `r` coordinates of `Fin (r + m)`. -/
def fromBlocksOne : unitaryGroup (Fin m) α →* unitaryGroup (Fin (r + m)) α where
  toFun B := ⟨reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 0 (B : Matrix _ _ α)),
    submatrix_equiv_mem_unitary.2 (fromBlocks_zero_zero_mem_unitary_iff.2 ⟨one_mem _,
        B.property⟩)⟩
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

/-- The block-diagonal embedding preserves determinants: `det (diag(1_r, B)) = det B`. -/
@[simp]
theorem det_fromBlocksOne (B : unitaryGroup (Fin m) α) :
    (fromBlocksOne α r m B : Matrix (Fin (r + m)) (Fin (r + m)) α).det =
      (B : Matrix (Fin m) (Fin m) α).det := by
  rw [coe_fromBlocksOne, det_reindex_self, det_fromBlocks_zero₂₁, det_one, one_mul]

variable {α r}

/-- **The block-diagonal unitary matrices are the stabilizer of the first `r` basis vectors**:
a unitary matrix of size `r + m` lies in the image of `U(m)` exactly when it fixes the standard
basis vectors `e₀, …, e_{r-1}`. -/
theorem mem_range_fromBlocksOne_iff {A : unitaryGroup (Fin (r + m)) α} :
    A ∈ (fromBlocksOne α r m).range ↔
      ∀ i : Fin r, A.val *ᵥ Pi.single (castAdd m i) 1 = Pi.single (castAdd m i) 1 := by
  refine ⟨?_, fun hA ↦ ?_⟩
  · rintro ⟨B, rfl⟩ i
    ext p
    refine Fin.addCases (fun j ↦ ?_) (fun k ↦ ?_) p
    · simp [Pi.single_apply, eq_comm]
    · simp
  -- The first `r` columns are standard basis vectors.
  have hcol : ∀ (p : Fin (r + m)) (i : Fin r),
      A.val p (castAdd m i) = (Pi.single (castAdd m i) 1 : Fin (r + m) → α) p :=
    fun p i ↦ by simpa using congrFun (hA i) p
  -- Since `star A * A = 1`, so are the first `r` rows.
  have hrow : ∀ (i : Fin r) (q : Fin (r + m)),
      A.val (castAdd m i) q = (1 : Matrix (Fin (r + m)) (Fin (r + m)) α) (castAdd m i) q :=
    fun i q ↦ by
      have h := congrFun (congrFun (mem_unitaryGroup_iff'.1 A.property) (castAdd m i)) q
      rw [star_eq_conjTranspose, Matrix.mul_apply] at h
      simpa [conjTranspose_apply, hcol, Pi.single_apply, apply_ite (star : α → α), ite_mul] using h
  let B : Matrix (Fin m) (Fin m) α := fun k l ↦ A.val (natAdd r k) (natAdd r l)
  have hAB : A.val = reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 0 B) := by
    ext p q
    refine Fin.addCases (fun i ↦ ?_) (fun k ↦ ?_) p <;>
      refine Fin.addCases (fun j ↦ ?_) (fun l ↦ ?_) q
    · simpa [Pi.single_apply, Matrix.one_apply, eq_comm] using hcol (castAdd m i) j
    · simpa [Matrix.one_apply] using hrow i (natAdd r l)
    · simpa [Pi.single_apply] using hcol (natAdd r k) j
    · simp only [reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_natAdd]
      rfl
  have hB : B ∈ unitaryGroup (Fin m) α :=
    ((reindex_fromBlocks_zero_zero_mem_unitary_iff _).1 (hAB ▸ A.property)).2
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
    submatrix_equiv_mem_unitary.2 (fromBlocks_zero_zero_mem_unitary_iff.2
      ⟨diagonal_mem_unitary.2 (Pi.const_mem_unitary_iff.2 cB.1.property), cB.2.property⟩)⟩
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
  have hentry (p q : Fin (m + 1)) : ∑ k, star (A.val k p) * A.val k q = if p = q then 1 else 0 := by
    simpa [Matrix.mul_apply, star_eq_conjTranspose, Matrix.one_apply] using
      congrFun (congrFun (mem_unitaryGroup_iff'.1 A.property) p) q
  -- The corner is a unitary scalar.
  have hc : star (A.val 0 0) * A.val 0 0 = 1 := by simpa [Fin.sum_univ_succ, hA] using hentry 0 0
  -- The row `0` vanishes off the corner.
  have hrow (j : Fin m) : A.val 0 j.succ = 0 := by
    have h := hentry 0 j.succ
    simp only [Fin.sum_univ_succ, hA, star_zero, zero_mul, Finset.sum_const_zero, add_zero,
      (Fin.succ_ne_zero j).symm, ite_false] at h
    calc A.val 0 j.succ = A.val 0 0 * star (A.val 0 0) * A.val 0 j.succ := by
          rw [mul_comm (A.val 0 0), hc, one_mul]
      _ = 0 := by rw [mul_assoc, h, mul_zero]
  let B : Matrix (Fin m) (Fin m) α := fun i j ↦ A.val i.succ j.succ
  have hAB : A.val = reindex (finSumFinEquiv.trans (finCongr (add_comm 1 m)))
      (finSumFinEquiv.trans (finCongr (add_comm 1 m)))
      (fromBlocks (diagonal fun _ ↦ A.val 0 0) 0 0 B) := by
    ext p q
    refine Fin.cases ?_ (fun i ↦ ?_) p <;> refine Fin.cases ?_ (fun j ↦ ?_) q <;>
      simp only [reindex_apply, submatrix_apply, finSumFinEquiv_trans_finCongr_symm_zero,
        finSumFinEquiv_trans_finCongr_symm_succ, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        fromBlocks_apply₂₁, fromBlocks_apply₂₂, diagonal_apply_eq] <;>
      first | rfl | exact hrow j | exact hA i
  have hB : B ∈ unitaryGroup (Fin m) α :=
    ((reindex_fromBlocks_zero_zero_mem_unitary_iff _).1 (hAB ▸ A.property)).2
  exact ⟨(⟨A.val 0 0, Unitary.mem_iff_star_mul_self.2 hc⟩, ⟨B, hB⟩), Subtype.ext hAB.symm⟩

end Succ

end UnitaryGroup

namespace UnitaryGroup

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The **block-diagonal sum** `diag(U, V)` of two unitary matrices, as a group morphism
`U(n) × U(m) →* U(n + m)`. -/
def sum : unitaryGroup n α × unitaryGroup m α →* unitaryGroup (n ⊕ m) α where
  toFun p := ⟨fromBlocks (p.1 : Matrix n n α) 0 0 (p.2 : Matrix m m α), by
    rw [mem_unitaryGroup_iff, star_eq_conjTranspose, fromBlocks_conjTranspose, fromBlocks_multiply,
      ← star_eq_conjTranspose, ← star_eq_conjTranspose, mem_unitaryGroup_iff.1 p.1.property,
      mem_unitaryGroup_iff.1 p.2.property]
    simp⟩
  map_one' := Subtype.ext <| by simp [fromBlocks_one]
  map_mul' p q := Subtype.ext <| by simp [fromBlocks_multiply]

@[simp]
theorem coe_sum (p : unitaryGroup n α × unitaryGroup m α) :
    (sum p : Matrix (n ⊕ m) (n ⊕ m) α) = fromBlocks (p.1 : Matrix n n α) 0 0 p.2 :=
  (rfl)

/-- The block-diagonal sum of unitary matrices is injective. -/
theorem sum_injective : Function.Injective (sum : unitaryGroup n α × unitaryGroup m α →* _) :=
  fun p q h ↦ by
    obtain ⟨h₁, -, -, h₂⟩ := fromBlocks_inj.1 (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext h₁) (Subtype.ext h₂)

end UnitaryGroup

namespace specialUnitaryGroup

variable (α) (r : ℕ) {m : ℕ}

variable (m) in
/-- The **block-diagonal embedding** `B ↦ diag(1_r, B)` of the special unitary group `SU(m)` in
`SU(r + m)`: the identity block occupies the first `r` coordinates of `Fin (r + m)`. -/
def fromBlocksOne : specialUnitaryGroup (Fin m) α →* specialUnitaryGroup (Fin (r + m)) α where
  toFun B := ⟨reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 0 (B : Matrix _ _ α)),
    submatrix_equiv_mem_unitary.2
      (fromBlocks_zero_zero_mem_unitary_iff.2 ⟨one_mem _, B.property.1⟩),
    by simpa [det_fromBlocks_zero₂₁] using B.property.2⟩
  map_one' := Subtype.ext <| by simp [fromBlocks_one]
  map_mul' A B := Subtype.ext <| by
    simp only [reindex_apply, Submonoid.coe_mul, submatrix_mul_equiv, fromBlocks_multiply,
      Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem coe_fromBlocksOne (B : specialUnitaryGroup (Fin m) α) :
    (fromBlocksOne α r m B : Matrix (Fin (r + m)) (Fin (r + m)) α) =
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 0 (B : Matrix _ _ α)) :=
  (rfl)

@[simp]
theorem fromBlocksOne_apply_castAdd_castAdd (B : specialUnitaryGroup (Fin m) α) (i j : Fin r) :
    (fromBlocksOne α r m B : Matrix (Fin (r + m)) (Fin (r + m)) α) (castAdd m i) (castAdd m j) =
      if i = j then 1 else 0 := by
  simp [coe_fromBlocksOne, Matrix.one_apply]

@[simp]
theorem fromBlocksOne_apply_castAdd_natAdd (B : specialUnitaryGroup (Fin m) α) (i : Fin r)
    (k : Fin m) :
    (fromBlocksOne α r m B : Matrix (Fin (r + m)) (Fin (r + m)) α) (castAdd m i) (natAdd r k) =
      0 := by
  simp [coe_fromBlocksOne]

@[simp]
theorem fromBlocksOne_apply_natAdd_castAdd (B : specialUnitaryGroup (Fin m) α) (k : Fin m)
    (i : Fin r) :
    (fromBlocksOne α r m B : Matrix (Fin (r + m)) (Fin (r + m)) α) (natAdd r k) (castAdd m i) =
      0 := by
  simp [coe_fromBlocksOne]

@[simp]
theorem fromBlocksOne_apply_natAdd_natAdd (B : specialUnitaryGroup (Fin m) α) (k l : Fin m) :
    (fromBlocksOne α r m B : Matrix (Fin (r + m)) (Fin (r + m)) α) (natAdd r k) (natAdd r l) =
      (B : Matrix (Fin m) (Fin m) α) k l := by
  simp [coe_fromBlocksOne]

/-- The block-diagonal embedding of special unitary groups is injective. -/
theorem fromBlocksOne_injective : Function.Injective (fromBlocksOne α r m) := fun A B h ↦
  Subtype.ext <| funext fun k ↦ funext fun l ↦ by
    simpa [coe_fromBlocksOne] using
      congrFun (congrFun (congrArg Subtype.val h) (natAdd r k)) (natAdd r l)

variable {α r}

/-- **The block-diagonal special unitary matrices are the stabilizer of the first `r` basis
vectors**: a special unitary matrix of size `r + m` lies in the image of `SU(m)` exactly when it
fixes the standard basis vectors `e₀, …, e_{r-1}`. -/
theorem mem_range_fromBlocksOne_iff {A : specialUnitaryGroup (Fin (r + m)) α} :
    A ∈ (fromBlocksOne α r m).range ↔
      ∀ i : Fin r, A.val *ᵥ Pi.single (castAdd m i) 1 = Pi.single (castAdd m i) 1 := by
  rw [← UnitaryGroup.mem_range_fromBlocksOne_iff (A := ⟨A.val, A.property.1⟩)]
  constructor
  · rintro ⟨B, rfl⟩
    exact ⟨⟨B.val, B.property.1⟩, Subtype.ext <|
      (UnitaryGroup.coe_fromBlocksOne α r _).trans (coe_fromBlocksOne α r B).symm⟩
  · rintro ⟨B, hB⟩
    -- The determinant of `diag(1_r, B)` is that of `B`.
    have hdet : (B : Matrix (Fin m) (Fin m) α).det = 1 := by
      have h := A.property.2
      rw [← congrArg Subtype.val hB] at h
      simpa [UnitaryGroup.coe_fromBlocksOne, det_fromBlocks_zero₂₁] using h
    exact ⟨⟨B, B.property, hdet⟩, Subtype.ext <| (coe_fromBlocksOne α r _).trans <|
      (UnitaryGroup.coe_fromBlocksOne α r B).symm.trans (congrArg Subtype.val hB)⟩

end specialUnitaryGroup

end Unitary

namespace SpecialOrthogonalGroup

attribute [local instance] starRingOfComm

variable (R : Type*) [CommRing R] (r : ℕ) {m : ℕ}

variable (m) in
/-- The **block-diagonal embedding** `B ↦ diag(1_r, B)` of the special orthogonal group `SO(m)`
in `SO(r + m)`: the identity block occupies the first `r` coordinates of `Fin (r + m)`. It is the
special unitary embedding `Matrix.specialUnitaryGroup.fromBlocksOne` for the trivial star. -/
def fromBlocksOne :
    specialOrthogonalGroup (Fin m) R →* specialOrthogonalGroup (Fin (r + m)) R :=
  specialUnitaryGroup.fromBlocksOne R r m

variable (m) in
/-- The special orthogonal block embedding is the special unitary one for the trivial star. -/
theorem fromBlocksOne_eq_specialUnitaryGroup_fromBlocksOne :
    fromBlocksOne R r m = specialUnitaryGroup.fromBlocksOne R r m :=
  (rfl)

theorem coe_fromBlocksOne (B : specialOrthogonalGroup (Fin m) R) :
    (fromBlocksOne R r m B : Matrix (Fin (r + m)) (Fin (r + m)) R) =
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks 1 0 0 (B : Matrix _ _ R)) :=
  specialUnitaryGroup.coe_fromBlocksOne R r B

@[simp]
theorem fromBlocksOne_apply_castAdd_castAdd (B : specialOrthogonalGroup (Fin m) R) (i j : Fin r) :
    (fromBlocksOne R r m B : Matrix (Fin (r + m)) (Fin (r + m)) R) (castAdd m i) (castAdd m j) =
      if i = j then 1 else 0 :=
  specialUnitaryGroup.fromBlocksOne_apply_castAdd_castAdd R r B i j

@[simp]
theorem fromBlocksOne_apply_castAdd_natAdd (B : specialOrthogonalGroup (Fin m) R) (i : Fin r)
    (k : Fin m) :
    (fromBlocksOne R r m B : Matrix (Fin (r + m)) (Fin (r + m)) R) (castAdd m i) (natAdd r k) =
      0 :=
  specialUnitaryGroup.fromBlocksOne_apply_castAdd_natAdd R r B i k

@[simp]
theorem fromBlocksOne_apply_natAdd_castAdd (B : specialOrthogonalGroup (Fin m) R) (k : Fin m)
    (i : Fin r) :
    (fromBlocksOne R r m B : Matrix (Fin (r + m)) (Fin (r + m)) R) (natAdd r k) (castAdd m i) =
      0 :=
  specialUnitaryGroup.fromBlocksOne_apply_natAdd_castAdd R r B k i

@[simp]
theorem fromBlocksOne_apply_natAdd_natAdd (B : specialOrthogonalGroup (Fin m) R) (k l : Fin m) :
    (fromBlocksOne R r m B : Matrix (Fin (r + m)) (Fin (r + m)) R) (natAdd r k) (natAdd r l) =
      (B : Matrix (Fin m) (Fin m) R) k l :=
  specialUnitaryGroup.fromBlocksOne_apply_natAdd_natAdd R r B k l

/-- The block-diagonal embedding of special orthogonal groups is injective. -/
theorem fromBlocksOne_injective : Function.Injective (fromBlocksOne R r m) :=
  specialUnitaryGroup.fromBlocksOne_injective R r

variable {R r}

/-- **The block-diagonal special orthogonal matrices are the stabilizer of the first `r` basis
vectors**: a special orthogonal matrix of size `r + m` lies in the image of `SO(m)` exactly when
it fixes the standard basis vectors `e₀, …, e_{r-1}`. -/
theorem mem_range_fromBlocksOne_iff {A : specialOrthogonalGroup (Fin (r + m)) R} :
    A ∈ (fromBlocksOne R r m).range ↔
      ∀ i : Fin r, A.val *ᵥ Pi.single (castAdd m i) 1 = Pi.single (castAdd m i) 1 :=
  specialUnitaryGroup.mem_range_fromBlocksOne_iff

end SpecialOrthogonalGroup

end Matrix
