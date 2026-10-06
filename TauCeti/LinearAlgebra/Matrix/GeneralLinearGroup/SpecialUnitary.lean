/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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
whose theory is already available.  `TauCeti.GLSpecialUnitary.mem_iff` identifies the carrier with
Mathlib's submonoid, so nothing is lost.

This mirrors `TauCeti.GLSymplectic`, the units-level avatar of `Matrix.symplecticGroup`.

## Main definitions

* `TauCeti.GLSpecialUnitary`: the special unitary group as a subgroup of `GL n 𝕜`.

## Main results

* `TauCeti.GLSpecialUnitary.eq_unitarySubgroup_inf_ker_det`: the defining decomposition into a
  unitary and a determinant condition.
* `TauCeti.GLSpecialUnitary.mem_iff`: its elements are the units whose matrix is special unitary.
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
theorem mem_iff {M : GL n 𝕜} :
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
  Set.ext fun _ => mem_iff

end GLSpecialUnitary

end TauCeti
