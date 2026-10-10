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
supports their base-change constructions. A scalar matrix is orthogonal only when its scalar
squares to one.

## Main declarations

* `Matrix.SpecialOrthogonalGroup.map`: entrywise mapping of special orthogonal matrices.
* `Matrix.sq_eq_one_of_smul_one_mem_orthogonalGroup`: a scalar orthogonal matrix has scalar a
  square root of one.
-/

public section

open Matrix

/-- A scalar matrix preserving the standard symmetric form has scalar a square root of one,
provided the index type is nonempty: the orthogonality relation reads `c ^ 2 • 1 = 1`. -/
theorem Matrix.sq_eq_one_of_smul_one_mem_orthogonalGroup {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {R : Type*} [CommRing R] {c : R}
    (h : c • (1 : Matrix n n R) ∈ Matrix.orthogonalGroup n R) : c ^ 2 = 1 := by
  rw [Matrix.mem_orthogonalGroup_iff] at h
  have hentry := congrFun (congrFun h (Classical.arbitrary n)) (Classical.arbitrary n)
  simpa [sq] using hentry

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

/-- A coefficient-ring map acts entrywise on special orthogonal matrices. -/
theorem map_apply {S : Type v} [CommRing S] (f : R →+* S)
    (M : Matrix.specialOrthogonalGroup n R) (i j : n) :
    (map f M : Matrix n n S) i j = f ((M : Matrix n n R) i j) := by
  rw [coe_map, Matrix.map_apply]

/-- Mapping coefficients along the identity ring homomorphism is the identity. -/
@[simp]
theorem map_id :
    map (n := n) (RingHom.id R) = MonoidHom.id (Matrix.specialOrthogonalGroup n R) := by
  ext M i j
  simp only [map_apply, RingHom.id_apply, MonoidHom.id_apply]

/-- Successive coefficient-ring maps agree with mapping along their composite. -/
@[simp]
theorem map_comp {S T : Type*} [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) :
    map (n := n) (g.comp f) = (map (n := n) g).comp (map (n := n) f) := by
  apply MonoidHom.ext
  intro M
  apply Subtype.ext
  ext i j
  simp only [map_apply, RingHom.coe_comp, Function.comp_apply, MonoidHom.coe_comp]

end Matrix.SpecialOrthogonalGroup
