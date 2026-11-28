/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Inclusion of the special unitary group into `SL(n, α)`

A special unitary matrix has determinant one, so the special unitary group
`Matrix.specialUnitaryGroup n α` embeds as a subgroup of the special linear group `SL(n, α)`
(`Matrix.specialUnitaryGroup.toSL`).

## Main definitions

* `Matrix.specialUnitaryGroup.toSL`: the inclusion `SU(n) →* SL(n)`.

## Main results

* `Matrix.specialUnitaryGroup.coe_toSL`: the underlying matrix of `toSL A` is `A`.
* `Matrix.specialUnitaryGroup.toGL_toSL`: in `GL(n)`, `toSL A` agrees with the unitary units.
* `Matrix.specialUnitaryGroup.toSL_injective`: `toSL` is injective.
* `Matrix.specialUnitaryGroup.mem_range_toSL_iff`: a matrix of `SL(n)` lies in the range of `toSL`
  exactly when it is unitary.
-/

public section

open scoped MatrixGroups

namespace Matrix.specialUnitaryGroup

variable {n : Type*} [DecidableEq n] [Fintype n] {α : Type*} [CommRing α] [StarRing α]

/-- The inclusion of the special unitary group into the special linear group: a special unitary
matrix has determinant one. -/
def toSL : specialUnitaryGroup n α →* SpecialLinearGroup n α where
  toFun A := ⟨A, (mem_specialUnitaryGroup_iff.mp A.property).2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem coe_toSL (A : specialUnitaryGroup n α) :
    ((toSL A : SpecialLinearGroup n α) : Matrix n n α) = A :=
  (rfl)

/-- A special unitary matrix, viewed in `GL(n, α)`, is the unit of the corresponding unitary
matrix. -/
theorem toGL_toSL (A : specialUnitaryGroup n α) :
    SpecialLinearGroup.toGL (toSL A) =
      Unitary.toUnits (Submonoid.inclusion specialUnitaryGroup_le_unitaryGroup A) :=
  Units.ext (rfl)

/-- The inclusion `Matrix.specialUnitaryGroup.toSL` is injective. -/
theorem toSL_injective : Function.Injective (toSL : specialUnitaryGroup n α →* _) :=
  fun A B h => Subtype.ext <| by
    simpa using congrArg (fun M : SpecialLinearGroup n α => (M : Matrix n n α)) h

/-- A matrix of the special linear group comes from the special unitary group exactly when it is
unitary. -/
theorem mem_range_toSL_iff {A : SpecialLinearGroup n α} :
    A ∈ (toSL : specialUnitaryGroup n α →* _).range ↔ (A : Matrix n n α) ∈ unitaryGroup n α := by
  refine ⟨?_, fun hA => ⟨⟨A, hA, A.property⟩, rfl⟩⟩
  rintro ⟨B, rfl⟩
  exact (mem_specialUnitaryGroup_iff.mp B.property).1

end Matrix.specialUnitaryGroup
