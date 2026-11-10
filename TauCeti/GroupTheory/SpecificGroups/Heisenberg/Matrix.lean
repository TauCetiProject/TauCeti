/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Heisenberg.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# The Heisenberg group in the special linear group

The standard upper unitriangular realization of the Heisenberg group has determinant one.
Its lift to `SL₃` lets subgroups defined in Heisenberg coordinates be used as matrix root groups.
-/

public section

namespace TauCeti.HeisenbergGroup

variable {R : Type*} [CommRing R]

/-- The upper unitriangular realization of the Heisenberg group in `SL₃`. -/
def toSpecialLinear : HeisenbergGroup R →* Matrix.SpecialLinearGroup (Fin 3) R where
  toFun a := ⟨toMatrix a, by simp [toMatrix_apply, Matrix.det_fin_three]⟩
  map_one' := Subtype.ext (map_one toMatrix)
  map_mul' a b := Subtype.ext (map_mul toMatrix a b)

@[simp]
theorem coe_toSpecialLinear (a : HeisenbergGroup R) :
    (toSpecialLinear a : Matrix (Fin 3) (Fin 3) R) = toMatrix a := (rfl)

/-- The special linear realization is faithful. -/
theorem toSpecialLinear_injective :
    Function.Injective (toSpecialLinear : HeisenbergGroup R → _) :=
  fun _ _ h ↦ toMatrix_injective (congrArg Subtype.val h)

end TauCeti.HeisenbergGroup
