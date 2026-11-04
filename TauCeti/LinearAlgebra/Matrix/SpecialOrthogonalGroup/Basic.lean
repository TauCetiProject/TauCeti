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
supports their base-change constructions. The construction is modelled on Mathlib's
`Matrix.SpecialLinearGroup.map`.

## Main declarations

* `Matrix.SpecialOrthogonalGroup.map`: entrywise mapping of special orthogonal matrices.
-/

public section

namespace Matrix.SpecialOrthogonalGroup

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R S : Type*} [CommRing R] [CommRing S]

attribute [local instance] starRingOfComm

/-- A ring homomorphism maps special orthogonal matrices to special orthogonal matrices. -/
theorem map_mem (f : R →+* S) {M : Matrix n n R} (hM : M ∈ specialOrthogonalGroup n R) :
    M.map f ∈ specialOrthogonalGroup n S := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff] at hM ⊢
  refine ⟨?_, (f.map_det M).symm.trans <| by rw [hM.2, _root_.map_one]⟩
  rw [← transpose_map, ← Matrix.map_mul, hM.1, Matrix.map_one f f.map_zero f.map_one]

/-- A ring homomorphism maps special orthogonal matrices entrywise. -/
def map (f : R →+* S) : specialOrthogonalGroup n R →* specialOrthogonalGroup n S where
  toFun M := ⟨M.1.map f, map_mem f M.2⟩
  map_one' := Subtype.ext (Matrix.map_one f f.map_zero f.map_one)
  map_mul' _ _ := Subtype.ext Matrix.map_mul

/-- Entrywise mapping of a special orthogonal matrix has the expected underlying matrix. -/
@[simp]
theorem coe_map (f : R →+* S) (M : specialOrthogonalGroup n R) :
    (map f M : Matrix n n S) = M.1.map f :=
  (rfl)

/-- A coefficient-ring map acts entrywise on special orthogonal matrices. -/
theorem map_apply (f : R →+* S) (M : specialOrthogonalGroup n R) (i j : n) :
    (map f M : Matrix n n S) i j = f ((M : Matrix n n R) i j) :=
  (rfl)

/-- Mapping coefficients along the identity ring homomorphism is the identity. -/
@[simp]
theorem map_id : map (n := n) (RingHom.id R) = MonoidHom.id (specialOrthogonalGroup n R) := by
  ext
  simp

/-- Successive coefficient-ring maps agree with mapping along their composite. -/
@[simp]
theorem map_comp {T : Type*} [CommRing T] (f : R →+* S) (g : S →+* T) :
    map (n := n) (g.comp f) = (map (n := n) g).comp (map (n := n) f) := by
  ext
  simp

end Matrix.SpecialOrthogonalGroup
