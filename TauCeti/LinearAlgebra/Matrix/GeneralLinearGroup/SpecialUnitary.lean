/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Units.Hom

import Mathlib.Algebra.Group.Subgroup.Ker

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The special unitary subgroup of the general linear group

Mathlib's `Matrix.specialUnitaryGroup n 𝕜` is a `Submonoid (Matrix n n 𝕜)`: the unitary matrices
of determinant one, carrying its own `Group` structure because a unitary matrix is inverted by its
adjoint.  The constructions that see a matrix group as a group of *units* — the general linear Lie
group and its Lie algebra above all — need the same object as a `Subgroup (GL n 𝕜)` instead, and
that is `TauCeti.GLSpecialUnitary n 𝕜`.

It is defined as the intersection of two subgroups already present: `unitarySubgroup (GL n 𝕜)`,
Mathlib's unitary elements of a group with involution, and the kernel of the determinant
`Matrix.GeneralLinearGroup.det`.  Defining it this way rather than by transporting the submonoid
is what makes it usable: a property of the special unitary group that is the conjunction of a
unitary and a determinant property can be proved one factor at a time, each factor being a group
whose theory is already available.  `TauCeti.GLSpecialUnitary.mem_iff_mem_specialUnitaryGroup`
identifies the carrier with Mathlib's submonoid, so nothing is lost.

This mirrors `TauCeti.GLSymplectic`, the units-level avatar of `Matrix.symplecticGroup`.

## Main definitions

* `TauCeti.GLSpecialUnitary`: the special unitary group as a subgroup of `GL n 𝕜`.

## Main results

* `TauCeti.GLSpecialUnitary.ofSpecialUnitaryGroup`: the canonical matrix-to-units inclusion.
* `TauCeti.GLSpecialUnitary.mulEquivSpecialUnitaryGroup`: the equivalence with the native
  special unitary matrix group.
* `TauCeti.GLSpecialUnitary.coe_ofSpecialUnitaryGroup`: the inclusion keeps the original matrix.
* `TauCeti.GLSpecialUnitary.range_ofSpecialUnitaryGroup`: its image is `GLSpecialUnitary`.
* `TauCeti.GLSpecialUnitary.coe_mulEquivSpecialUnitaryGroup` and
  `TauCeti.GLSpecialUnitary.coe_mulEquivSpecialUnitaryGroup_symm_apply`: the carrier
  computation rules.
* `TauCeti.GLSpecialUnitary.eq_unitarySubgroup_inf_ker_det`: the defining decomposition into a
  unitary and a determinant condition.
* `TauCeti.GLSpecialUnitary.mem_iff_mem_specialUnitaryGroup`: its elements are the units whose
  matrix is special unitary.
* `TauCeti.GLSpecialUnitary.le_unitarySubgroup`: it is contained in the unitary subgroup.
-/

public section

namespace TauCeti

variable (n : Type*) [Fintype n] [DecidableEq n] (𝕜 : Type*) [CommRing 𝕜] [StarRing 𝕜]

/-- **The special unitary subgroup of the general linear group**: the invertible matrices that are
unitary and have determinant one, as a subgroup of `GL n 𝕜`.  It is `Matrix.specialUnitaryGroup`
read on units, and is presented as the intersection of the unitary subgroup with the kernel of the
determinant. -/
def GLSpecialUnitary : Subgroup (GL n 𝕜) :=
  unitarySubgroup (GL n 𝕜) ⊓ MonoidHom.ker Matrix.GeneralLinearGroup.det

namespace GLSpecialUnitary

/-- The special unitary subgroup is by definition cut out by two independent conditions: being
unitary, and having determinant one. -/
theorem eq_unitarySubgroup_inf_ker_det :
    GLSpecialUnitary n 𝕜 =
      unitarySubgroup (GL n 𝕜) ⊓ MonoidHom.ker Matrix.GeneralLinearGroup.det :=
  (rfl)

variable {n 𝕜}

/-- An invertible matrix lies in the special unitary subgroup exactly when its underlying matrix
lies in Mathlib's `Matrix.specialUnitaryGroup`. -/
@[simp]
theorem mem_iff_mem_specialUnitaryGroup {M : GL n 𝕜} :
    M ∈ GLSpecialUnitary n 𝕜 ↔ (M : Matrix n n 𝕜) ∈ Matrix.specialUnitaryGroup n 𝕜 := by
  rw [eq_unitarySubgroup_inf_ker_det, Matrix.mem_specialUnitaryGroup_iff]
  -- Both sides are now a conjunction of a unitary and a determinant condition; what remains is
  -- transporting each across the coercion of units.
  simp [Units.unitary_eq, Units.ext_iff]

/-- The special unitary subgroup is contained in the unitary subgroup. -/
theorem le_unitarySubgroup : GLSpecialUnitary n 𝕜 ≤ unitarySubgroup (GL n 𝕜) :=
  eq_unitarySubgroup_inf_ker_det n 𝕜 ▸ inf_le_left

/-- The carrier of the special unitary subgroup is the preimage of Mathlib's special unitary
submonoid under the coercion of units.  This is the form the closedness of the subgroup is read
from. -/
theorem coe_eq_preimage :
    (GLSpecialUnitary n 𝕜 : Set (GL n 𝕜)) =
      Units.val ⁻¹' (Matrix.specialUnitaryGroup n 𝕜 : Set (Matrix n n 𝕜)) :=
  Set.ext fun _ => mem_iff_mem_specialUnitaryGroup

end GLSpecialUnitary

end TauCeti

namespace TauCeti.GLSpecialUnitary

variable (n : Type*) [Fintype n] [DecidableEq n]
  (R : Type*) [CommRing R] [StarRing R]

/-- The special unitary matrix, viewed as a unit. -/
def ofSpecialUnitaryGroup : Matrix.specialUnitaryGroup n R →* GL n R :=
  (Matrix.specialUnitaryGroup n R).subtype.toHomUnits

/-- The canonical unit has the original matrix as its value. -/
@[simp]
theorem coe_ofSpecialUnitaryGroup (A : Matrix.specialUnitaryGroup n R) :
    (ofSpecialUnitaryGroup n R A : Matrix n n R) = (A : Matrix n n R) :=
  MonoidHom.coe_toHomUnits _ A

/-- The matrix inclusion has range equal to the special unitary subgroup of the units. -/
theorem range_ofSpecialUnitaryGroup : (ofSpecialUnitaryGroup n R).range = GLSpecialUnitary n R := by
  ext A
  rw [MonoidHom.mem_range, mem_iff_mem_specialUnitaryGroup]
  constructor
  · rintro ⟨X, rfl⟩
    simpa only [coe_ofSpecialUnitaryGroup] using X.property
  · intro hA
    exact ⟨⟨(A : Matrix n n R), hA⟩, Units.ext (coe_ofSpecialUnitaryGroup n R _)⟩

/-- Read the special unitary subgroup of the units in its original matrix carrier. -/
noncomputable def mulEquivSpecialUnitaryGroup :
    GLSpecialUnitary n R ≃* Matrix.specialUnitaryGroup n R :=
  ((MonoidHom.ofInjective (fun A B h ↦ Subtype.ext (by
      simpa only [coe_ofSpecialUnitaryGroup] using congrArg Units.val h))).trans
    (MulEquiv.subgroupCongr (range_ofSpecialUnitaryGroup n R))).symm

/-- The inverse equivalence sends a matrix to its canonical unit. -/
@[simp]
theorem coe_mulEquivSpecialUnitaryGroup_symm_apply (A : Matrix.specialUnitaryGroup n R) :
    ((mulEquivSpecialUnitaryGroup n R).symm A : GL n R) = ofSpecialUnitaryGroup n R A := by
  simp only [mulEquivSpecialUnitaryGroup, MulEquiv.symm_symm, MulEquiv.trans_apply,
    MulEquiv.subgroupCongr_apply]
  exact MonoidHom.ofInjective_apply _

/-- The equivalence keeps the underlying matrix of each unit. -/
@[simp]
theorem coe_mulEquivSpecialUnitaryGroup (A : GLSpecialUnitary n R) :
    (mulEquivSpecialUnitaryGroup n R A : Matrix n n R) = (A.val : Matrix n n R) := by
  have h := coe_mulEquivSpecialUnitaryGroup_symm_apply n R (mulEquivSpecialUnitaryGroup n R A)
  rw [MulEquiv.symm_apply_apply] at h
  simpa only [coe_ofSpecialUnitaryGroup] using (congrArg Units.val h).symm

end TauCeti.GLSpecialUnitary
