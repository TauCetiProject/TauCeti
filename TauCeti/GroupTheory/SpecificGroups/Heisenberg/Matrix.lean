/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Heisenberg.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import TauCeti.LinearAlgebra.Matrix.Triangular
import Mathlib.Tactic.FinCases

/-!
# The Heisenberg group in the special linear group

The standard upper unitriangular realization of the Heisenberg group has determinant one.
Its lift to `SL₃` lets subgroups defined in Heisenberg coordinates be used as matrix root groups.
-/

public section

namespace TauCeti.HeisenbergGroup

section MatrixRealization

variable {R S : Type*} [Ring R] [Ring S]

/-- Heisenberg matrices are upper unitriangular. -/
theorem isUpperUnitriangular_toMatrix (a : HeisenbergGroup R) :
    (toMatrix a).IsUpperUnitriangular := by
  rw [Matrix.isUpperUnitriangular_def]
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [toMatrix_apply]
  · intro i
    fin_cases i <;> simp [toMatrix_apply]

/-- The Heisenberg matrices are exactly the upper-unitriangular matrices of size three. -/
theorem mem_range_toMatrix_iff (M : Matrix (Fin 3) (Fin 3) R) :
    M ∈ Set.range (toMatrix : HeisenbergGroup R → Matrix (Fin 3) (Fin 3) R) ↔
      M.IsUpperUnitriangular := by
  constructor
  · rintro ⟨a, rfl⟩
    exact isUpperUnitriangular_toMatrix a
  · intro hM
    refine ⟨⟨M 0 1, M 1 2, M 0 2⟩, ?_⟩
    apply (isUpperUnitriangular_toMatrix _).ext hM
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [toMatrix_apply]

/-- Applying a ring homomorphism to a Heisenberg matrix maps its coordinates. -/
@[simp]
theorem map_toMatrix (f : R →+* S) (a : HeisenbergGroup R) :
    (toMatrix a).map f = toMatrix (map f a) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMatrix_apply, map_apply]

end MatrixRealization

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

/-- The special linear Heisenberg matrices are exactly the upper-unitriangular matrices. -/
theorem mem_range_toSpecialLinear_iff (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    g ∈ (toSpecialLinear : HeisenbergGroup R →* _).range ↔
      (g : Matrix (Fin 3) (Fin 3) R).IsUpperUnitriangular := by
  rw [← mem_range_toMatrix_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

/-- Coefficient extension of the special linear realization maps Heisenberg coordinates. -/
@[simp]
theorem map_toSpecialLinear {S : Type*} [CommRing S] (f : R →+* S)
    (a : HeisenbergGroup R) :
    Matrix.SpecialLinearGroup.map f (toSpecialLinear a) = toSpecialLinear (map f a) := by
  apply Subtype.ext
  exact map_toMatrix f a

end TauCeti.HeisenbergGroup
