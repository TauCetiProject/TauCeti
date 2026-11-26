/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.BlockSucc

/-!
# The upper-left block embedding of a special orthogonal group in the next one

Placing a square matrix of size `n` in the upper-left block of a matrix of size `n + 1` with the
last row and column of the identity matrix (`Matrix.blockSucc`) preserves both orthogonality
(`Matrix.blockSucc_mem_orthogonalGroup_iff`) and the determinant (`Matrix.det_blockSucc`). It
therefore restricts `TauCeti.orthogonalBlockSucc` to the **special orthogonal block inclusion**
`TauCeti.specialOrthogonalBlockSucc : SO(n, k) →* SO(n + 1, k)`, whose image is again the
stabilizer of the last standard basis vector
(`TauCeti.exists_specialOrthogonalBlockSucc_eq_iff_mulVec_single`).

## Main definitions

* `TauCeti.specialOrthogonalBlockSucc`: the induced group homomorphism
  `Matrix.specialOrthogonalGroup (Fin n) k →* Matrix.specialOrthogonalGroup (Fin (n + 1)) k`.

## Main results

* `Matrix.blockSucc_mem_specialOrthogonalGroup_iff`: the extension of a matrix is special orthogonal
  if and only if the matrix is.
* `TauCeti.specialOrthogonalBlockSucc_injective`: the block inclusion is injective.
* `TauCeti.exists_specialOrthogonalBlockSucc_eq_iff_mulVec_single`: a special orthogonal matrix of
  size `n + 1` lies in the image of `specialOrthogonalBlockSucc` if and only if it fixes the last
  standard basis vector.
-/

public section

universe u

namespace Matrix

variable {k : Type u} [CommRing k] {n : ℕ}

attribute [local instance] starRingOfComm

/-- The upper-left block extension of a matrix is special orthogonal if and only if the matrix
itself is special orthogonal. -/
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
matrix is placed in the upper-left block and the last basis vector is fixed. This is the special
orthogonal counterpart of `TauCeti.orthogonalBlockSucc`. -/
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
    Function.Injective (specialOrthogonalBlockSucc k n) := fun _ _ h ↦
  Subtype.ext (blockSucc_injective (congrArg Subtype.val h))

/-- A special orthogonal matrix of size `n + 1` is the upper-left block extension of one of size
`n` if and only if it fixes the last standard basis vector. -/
theorem exists_specialOrthogonalBlockSucc_eq_iff_mulVec_single
    (g : Matrix.specialOrthogonalGroup (Fin (n + 1)) k) :
    (∃ h : Matrix.specialOrthogonalGroup (Fin n) k, specialOrthogonalBlockSucc k n h = g) ↔
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ Pi.single (Fin.last n) 1 =
        Pi.single (Fin.last n) 1 := by
  rw [← exists_orthogonalBlockSucc_eq_iff_mulVec_single k n ⟨g.val, g.property.1⟩]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨⟨h.val, h.property.1⟩, Subtype.ext (by simp)⟩
  · rintro ⟨h, hh⟩
    have hblock : blockSucc (h : Matrix (Fin n) (Fin n) k) = g := by
      simpa only [coe_orthogonalBlockSucc] using congrArg Subtype.val hh
    refine ⟨⟨h.val, mem_specialOrthogonalGroup_iff.mpr ⟨h.property, ?_⟩⟩, Subtype.ext hblock⟩
    rw [← det_blockSucc, hblock]
    exact (mem_specialOrthogonalGroup_iff.mp g.property).2

end TauCeti
