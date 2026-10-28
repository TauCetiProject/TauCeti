/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Duals in a monoidal preadditive category

In a monoidal preadditive category the right adjoint mate `f ↦ fᘁ` is additive, because it is
built from whiskering and composition, and the coevaluation of an exact pairing out of a nonzero
object is nonzero, by the zigzag identity.

In a monoidal `k`-linear category the Frobenius reciprocity bijections `tensorLeftHomEquiv` and
`tensorRightHomEquiv` are `k`-linear, so they compare dimensions of morphism spaces, for instance
of the multiplicity spaces of a fusion category.

## Main declarations

* `TauCeti.rightAdjointMate_zero` and `TauCeti.rightAdjointMate_add`: the right adjoint mate is
  additive;
* `TauCeti.coevaluation_ne_zero`: the coevaluation `η_ X Y` is nonzero when `X` is;
* `TauCeti.tensorLeftHomLinearEquiv` and `TauCeti.tensorRightHomLinearEquiv`: Frobenius
  reciprocity as `k`-linear equivalences.
-/

public section

open CategoryTheory Limits MonoidalCategory

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C]

section Mate

variable {X Y : C} [HasRightDual X] [HasRightDual Y]

/-- The right adjoint mate of the zero morphism is zero. -/
@[simp]
theorem rightAdjointMate_zero : (0 : X ⟶ Y)ᘁ = 0 := by
  simp [rightAdjointMate]

/-- The right adjoint mate is additive. -/
@[simp]
theorem rightAdjointMate_add (f g : X ⟶ Y) : (f + g)ᘁ = fᘁ + gᘁ := by
  simp [rightAdjointMate]

end Mate

/-- The coevaluation of an exact pairing of `X` with `Y` is nonzero when `X` is nonzero: otherwise
the zigzag identity would make the identity of `X` zero. -/
theorem coevaluation_ne_zero {X Y : C} [ExactPairing X Y] (hX : ¬IsZero X) : η_ X Y ≠ 0 := by
  intro h
  have hz := ExactPairing.evaluation_coevaluation X Y
  rw [h, MonoidalPreadditive.zero_whiskerRight, zero_comp] at hz
  exact hX ((IsZero.iff_id_eq_zero X).2 (by simpa using (λ_ X).inv ≫= hz.symm =≫ (ρ_ X).hom))

section Linear

variable (k : Type w) [Semiring k] [Linear k C] [MonoidalLinear k C]

/-- Frobenius reciprocity `(Y' ⊗ X ⟶ Z) ≃ (X ⟶ Y ⊗ Z)` for an exact pairing of `Y` and `Y'`
(`CategoryTheory.tensorLeftHomEquiv`) is `k`-linear. -/
noncomputable def tensorLeftHomLinearEquiv (X Y Y' Z : C) [ExactPairing Y Y'] :
    (Y' ⊗ X ⟶ Z) ≃ₗ[k] (X ⟶ Y ⊗ Z) :=
  { tensorLeftHomEquiv X Y Y' Z with
    map_add' f g := by simp [tensorLeftHomEquiv]
    map_smul' r f := by simp [tensorLeftHomEquiv] }

/-- `TauCeti.tensorLeftHomLinearEquiv` acts as `CategoryTheory.tensorLeftHomEquiv`. -/
@[simp]
theorem tensorLeftHomLinearEquiv_apply (X Y Y' Z : C) [ExactPairing Y Y'] (f : Y' ⊗ X ⟶ Z) :
    tensorLeftHomLinearEquiv k X Y Y' Z f = tensorLeftHomEquiv X Y Y' Z f :=
  (rfl)

/-- The inverse of `TauCeti.tensorLeftHomLinearEquiv` acts as that of
`CategoryTheory.tensorLeftHomEquiv`. -/
@[simp]
theorem tensorLeftHomLinearEquiv_symm_apply (X Y Y' Z : C) [ExactPairing Y Y']
    (f : X ⟶ Y ⊗ Z) :
    (tensorLeftHomLinearEquiv k X Y Y' Z).symm f = (tensorLeftHomEquiv X Y Y' Z).symm f :=
  (rfl)

/-- Frobenius reciprocity `(X ⊗ Y ⟶ Z) ≃ (X ⟶ Z ⊗ Y')` for an exact pairing of `Y` and `Y'`
(`CategoryTheory.tensorRightHomEquiv`) is `k`-linear. -/
noncomputable def tensorRightHomLinearEquiv (X Y Y' Z : C) [ExactPairing Y Y'] :
    (X ⊗ Y ⟶ Z) ≃ₗ[k] (X ⟶ Z ⊗ Y') :=
  { tensorRightHomEquiv X Y Y' Z with
    map_add' f g := by simp [tensorRightHomEquiv]
    map_smul' r f := by simp [tensorRightHomEquiv] }

/-- `TauCeti.tensorRightHomLinearEquiv` acts as `CategoryTheory.tensorRightHomEquiv`. -/
@[simp]
theorem tensorRightHomLinearEquiv_apply (X Y Y' Z : C) [ExactPairing Y Y'] (f : X ⊗ Y ⟶ Z) :
    tensorRightHomLinearEquiv k X Y Y' Z f = tensorRightHomEquiv X Y Y' Z f :=
  (rfl)

/-- The inverse of `TauCeti.tensorRightHomLinearEquiv` acts as that of
`CategoryTheory.tensorRightHomEquiv`. -/
@[simp]
theorem tensorRightHomLinearEquiv_symm_apply (X Y Y' Z : C) [ExactPairing Y Y']
    (f : X ⟶ Z ⊗ Y') :
    (tensorRightHomLinearEquiv k X Y Y' Z).symm f = (tensorRightHomEquiv X Y Y' Z).symm f :=
  (rfl)

end Linear

end TauCeti
