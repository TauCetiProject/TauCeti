/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Entrywise maps of special orthogonal matrices

A ring homomorphism maps a special orthogonal matrix entrywise to a special orthogonal matrix.
This expresses the functoriality of special orthogonal groups under coefficient-ring maps and
supports their base-change constructions.

## Main declarations

* `Matrix.SpecialOrthogonalGroup.map`: entrywise mapping of special orthogonal matrices.
-/

public section

open Matrix

namespace Matrix.SpecialOrthogonalGroup

universe u v

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type u} [CommRing R]

attribute [local instance] starRingOfComm

/-- A ring homomorphism maps special orthogonal matrices to special orthogonal matrices. -/
theorem map_mem {S : Type v} [CommRing S] (f : R →+* S)
    {M : Matrix n n R} (hM : M ∈ Matrix.specialOrthogonalGroup n R) :
    M.map f ∈ Matrix.specialOrthogonalGroup n S := by
  rw [Matrix.mem_specialOrthogonalGroup_iff] at hM ⊢
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff n S]
    calc
      M.map f * (M.map f)ᵀ = (M * Mᵀ).map f := by
        rw [← Matrix.transpose_map]
        exact Matrix.map_mul.symm
      _ = 1 := by
        rw [(Matrix.mem_orthogonalGroup_iff n R).mp hM.1]
        exact Matrix.map_one f f.map_zero f.map_one
  · calc
      (M.map f).det = f M.det := (RingHom.map_det f M).symm
      _ = 1 := by rw [hM.2, map_one]

/-- A ring homomorphism maps special orthogonal matrices entrywise. -/
def map {S : Type v} [CommRing S] (f : R →+* S) :
    Matrix.specialOrthogonalGroup n R →* Matrix.specialOrthogonalGroup n S where
  toFun M := ⟨M.1.map f, map_mem f M.2⟩
  map_one' := Subtype.ext (Matrix.map_one f f.map_zero f.map_one)
  map_mul' _ _ := Subtype.ext Matrix.map_mul

/-- Entrywise mapping of a special orthogonal matrix has the expected underlying matrix. -/
@[simp]
theorem coe_map {S : Type v} [CommRing S] (f : R →+* S)
    (M : Matrix.specialOrthogonalGroup n R) :
    (map f M : Matrix n n S) = M.1.map f :=
  by simp [map]

end Matrix.SpecialOrthogonalGroup
