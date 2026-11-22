/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.BlockSucc
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Block

/-!
# The upper-left block embedding of a special orthogonal group in the next one

Placing an `n × n` special orthogonal matrix in the upper-left block of an `(n + 1) × (n + 1)`
matrix with `1` in the last diagonal entry and `0` off-diagonal (`Matrix.blockSucc`) preserves
both orthogonality (`Matrix.blockSucc_mem_orthogonalGroup_iff`) and the determinant
(`Matrix.det_blockSucc`). It therefore induces the **block inclusion**
`TauCeti.specialOrthogonalBlockSucc : SO(n, k) →* SO(n + 1, k)`, whose image consists of the
special orthogonal matrices fixing the last standard basis vector
(`TauCeti.exists_specialOrthogonalBlockSucc_eq_iff_mulVec_single`).

Reindexing rows and columns by the canonical permutation `Fin (n + 1) ≃ Fin (1 + n)` moving the
last coordinate to the front identifies `TauCeti.specialOrthogonalBlockSucc` with the lower-right
block-diagonal embedding `Matrix.SpecialOrthogonalGroup.fromBlocksOne` (`r = 1`).

## Main definitions

* `TauCeti.specialOrthogonalBlockSucc`: the induced group homomorphism
  `Matrix.specialOrthogonalGroup (Fin n) k →* Matrix.specialOrthogonalGroup (Fin (n + 1)) k`.

## Main results

* `Matrix.blockSucc_mem_specialOrthogonalGroup_iff`: the extension of a matrix is special
  orthogonal exactly when the matrix is.
* `TauCeti.specialOrthogonalBlockSucc_injective`: the block inclusion is injective.
* `TauCeti.toOrthogonalGroup_specialOrthogonalBlockSucc`: the block inclusion commutes with the
  inclusion into `O(n, k)`.
* `TauCeti.exists_specialOrthogonalBlockSucc_eq_iff_mulVec_single`: a special orthogonal matrix of
  size `n + 1` is an extension exactly when it fixes the last basis vector.
* `TauCeti.reindex_coe_specialOrthogonalBlockSucc_eq_fromBlocksOne`: reindexing identifies
  `specialOrthogonalBlockSucc` with `Matrix.SpecialOrthogonalGroup.fromBlocksOne`.
-/

public section

universe u

namespace Matrix

variable {k : Type u} [CommRing k] {n : ℕ}

attribute [local instance] starRingOfComm

/-- **The extension of a matrix is special orthogonal exactly when the matrix is.** Extending
preserves orthogonality (`Matrix.blockSucc_mem_orthogonalGroup_iff`) and leaves the determinant
unchanged (`Matrix.det_blockSucc`). -/
@[simp]
theorem blockSucc_mem_specialOrthogonalGroup_iff {M : Matrix (Fin n) (Fin n) k} :
    blockSucc M ∈ specialOrthogonalGroup (Fin (n + 1)) k ↔
      M ∈ specialOrthogonalGroup (Fin n) k := by
  rw [mem_specialOrthogonalGroup_iff, mem_specialOrthogonalGroup_iff,
    blockSucc_mem_orthogonalGroup_iff, det_blockSucc]

end Matrix

namespace TauCeti

open Matrix

variable (k : Type u) [CommRing k] (n : ℕ)

attribute [local instance] starRingOfComm

/-- **The special orthogonal block inclusion** `SO(n, k) →* SO(n + 1, k)`: a special orthogonal
matrix is placed in the upper-left block and the last basis vector is fixed. -/
def specialOrthogonalBlockSucc :
    Matrix.specialOrthogonalGroup (Fin n) k →* Matrix.specialOrthogonalGroup (Fin (n + 1)) k where
  toFun g := ⟨blockSucc (g : Matrix (Fin n) (Fin n) k),
    blockSucc_mem_specialOrthogonalGroup_iff.mpr g.property⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp [blockSucc_mul])

/-- The special orthogonal block inclusion has the extended matrix as its underlying matrix. -/
@[simp]
theorem coe_specialOrthogonalBlockSucc (g : Matrix.specialOrthogonalGroup (Fin n) k) :
    (specialOrthogonalBlockSucc k n g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      blockSucc (g : Matrix (Fin n) (Fin n) k) :=
  (rfl)

/-- The special orthogonal block inclusion is injective. -/
theorem specialOrthogonalBlockSucc_injective :
    Function.Injective (specialOrthogonalBlockSucc k n) := by
  intro g h hgh
  refine Subtype.ext (blockSucc_injective ?_)
  rw [← coe_specialOrthogonalBlockSucc k n, ← coe_specialOrthogonalBlockSucc k n]
  exact congrArg
    (fun x : Matrix.specialOrthogonalGroup (Fin (n + 1)) k ↦
      (x : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) hgh

/-- The special orthogonal block inclusion commutes with the inclusion `SO →* O`. -/
@[simp]
theorem toOrthogonalGroup_specialOrthogonalBlockSucc
    (g : Matrix.specialOrthogonalGroup (Fin n) k) :
    Matrix.specialOrthogonalGroup.toOrthogonalGroup (specialOrthogonalBlockSucc k n g) =
      orthogonalBlockSucc k n (Matrix.specialOrthogonalGroup.toOrthogonalGroup g) :=
  Subtype.ext (by simp)

/-- **The image of the special orthogonal block inclusion is the stabilizer of the last basis
vector.** -/
theorem exists_specialOrthogonalBlockSucc_eq_iff_mulVec_single
    (g : Matrix.specialOrthogonalGroup (Fin (n + 1)) k) :
    (∃ h : Matrix.specialOrthogonalGroup (Fin n) k, specialOrthogonalBlockSucc k n h = g) ↔
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single (Fin.last n) 1 =
        Pi.single (Fin.last n) 1 := by
  constructor
  · rintro ⟨h, rfl⟩
    rw [coe_specialOrthogonalBlockSucc, ← Fin.snoc_zero_eq_single, blockSucc_mulVec,
      Fin.init_snoc, Fin.snoc_last, mulVec_zero]
  · intro hfix
    obtain ⟨h, hh⟩ :=
      (exists_orthogonalBlockSucc_eq_iff_mulVec_single k n
        (Matrix.specialOrthogonalGroup.toOrthogonalGroup g)).2 (by simpa using hfix)
    have hh' : blockSucc (h : Matrix (Fin n) (Fin n) k) =
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
      simpa using congrArg Subtype.val hh
    have hdet : (h : Matrix (Fin n) (Fin n) k).det = 1 := by
      rw [← det_blockSucc, hh']
      exact g.property.2
    exact ⟨⟨h, h.property, hdet⟩, Subtype.ext <| by simpa using hh'⟩

/-- Reindexing `Fin (n + 1) ≃ Fin (1 + n)` moving the last coordinate to the front identifies the
underlying matrix of `specialOrthogonalBlockSucc k n g` with that of
`Matrix.SpecialOrthogonalGroup.fromBlocksOne k 1 n g`. -/
theorem reindex_coe_specialOrthogonalBlockSucc_eq_fromBlocksOne
    (g : Matrix.specialOrthogonalGroup (Fin n) k) :
    let e : Fin (n + 1) ≃ Fin (1 + n) :=
      (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin n) (Fin 1))).trans finSumFinEquiv
    Matrix.reindex e e (specialOrthogonalBlockSucc k n g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      (Matrix.SpecialOrthogonalGroup.fromBlocksOne k 1 n g :
        Matrix (Fin (1 + n)) (Fin (1 + n)) k) := by
  intro e
  rw [Matrix.SpecialOrthogonalGroup.coe_fromBlocksOne, coe_specialOrthogonalBlockSucc]
  refine Matrix.ext fun i j ↦ ?_
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply]
  have hi0 : e.symm (Fin.castAdd n (0 : Fin 1)) = Fin.last n :=
    Fin.ext (by dsimp [e]; simp)
  have hik (a : Fin n) : e.symm (Fin.natAdd 1 a) = Fin.castSucc a :=
    Fin.ext (by dsimp [e]; simp)
  rcases i with i | i <;> rcases j with j | j
  · obtain rfl : i = 0 := Subsingleton.elim i 0
    obtain rfl : j = 0 := Subsingleton.elim j 0
    simp [hi0]
  · obtain rfl : i = 0 := Subsingleton.elim i 0
    simp [hi0, hik]
  · obtain rfl : j = 0 := Subsingleton.elim j 0
    simp [hi0, hik]
  · simp [hik]

end TauCeti
