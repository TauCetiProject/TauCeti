/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Duals in a monoidal preadditive category

In a monoidal preadditive category the right adjoint mate `f ↦ fᘁ` is additive, because it is
built from whiskering and composition. Consequently the right dual of a binary biproduct is the
biproduct of the right duals, `(X ⊞ Y)ᘁ ≅ Xᘁ ⊞ Yᘁ`: the projections of `(X ⊞ Y)ᘁ` are the mates of
the inclusions of `X ⊞ Y`, and its inclusions are the mates of the projections.

In a monoidal `k`-linear category the Frobenius reciprocity bijections `tensorLeftHomEquiv` and
`tensorRightHomEquiv` are `k`-linear, so they compare dimensions of morphism spaces, for instance
of the multiplicity spaces of a fusion category.

## Main declarations

* `TauCeti.rightAdjointMate_zero` and `TauCeti.rightAdjointMate_add`: the right adjoint mate is
  additive;
* `TauCeti.rightDualBiprodIso`: the right dual of a binary biproduct is the biproduct of the right
  duals;
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

section Biprod

variable (X Y : C) [HasBinaryBiproduct X Y] [HasRightDual X] [HasRightDual Y]
  [HasRightDual (X ⊞ Y)] [HasBinaryBiproduct Xᘁ Yᘁ]

/-- The right dual of `X ⊞ Y` as a binary bicone over `Xᘁ` and `Yᘁ`: its projections are the
mates of the inclusions of `X ⊞ Y`, and its inclusions are the mates of the projections. -/
private noncomputable def rightDualBinaryBicone : BinaryBicone Xᘁ Yᘁ where
  pt := (X ⊞ Y)ᘁ
  fst := (biprod.inl : X ⟶ X ⊞ Y)ᘁ
  snd := (biprod.inr : Y ⟶ X ⊞ Y)ᘁ
  inl := (biprod.fst : X ⊞ Y ⟶ X)ᘁ
  inr := (biprod.snd : X ⊞ Y ⟶ Y)ᘁ
  inl_fst := by rw [← comp_rightAdjointMate, biprod.inl_fst, rightAdjointMate_id]
  inl_snd := by rw [← comp_rightAdjointMate, biprod.inr_fst, rightAdjointMate_zero]
  inr_fst := by rw [← comp_rightAdjointMate, biprod.inl_snd, rightAdjointMate_zero]
  inr_snd := by rw [← comp_rightAdjointMate, biprod.inr_snd, rightAdjointMate_id]

/-- The right dual of a binary biproduct is the biproduct of the right duals. The components of
the isomorphism are the mates of the inclusions of `X ⊞ Y`, and the components of its inverse
are the mates of the projections. -/
noncomputable def rightDualBiprodIso : (X ⊞ Y)ᘁ ≅ Xᘁ ⊞ Yᘁ :=
  biprod.uniqueUpToIso _ _ <| isBinaryBilimitOfTotal (rightDualBinaryBicone X Y) <| by
    -- The total identity of the bicone is the mate of the total identity of `X ⊞ Y`.
    have h := congrArg rightAdjointMate (biprod.total (X := X) (Y := Y))
    rw [rightAdjointMate_add, comp_rightAdjointMate, comp_rightAdjointMate,
      rightAdjointMate_id] at h
    exact h

/-- The first component of `rightDualBiprodIso` is the mate of the first inclusion. -/
@[reassoc (attr := simp)]
theorem rightDualBiprodIso_hom_fst :
    (rightDualBiprodIso X Y).hom ≫ biprod.fst = (biprod.inl : X ⟶ X ⊞ Y)ᘁ := by
  simp [rightDualBiprodIso, rightDualBinaryBicone]

/-- The second component of `rightDualBiprodIso` is the mate of the second inclusion. -/
@[reassoc (attr := simp)]
theorem rightDualBiprodIso_hom_snd :
    (rightDualBiprodIso X Y).hom ≫ biprod.snd = (biprod.inr : Y ⟶ X ⊞ Y)ᘁ := by
  simp [rightDualBiprodIso, rightDualBinaryBicone]

/-- The first component of the inverse of `rightDualBiprodIso` is the mate of the first
projection. -/
@[reassoc (attr := simp)]
theorem inl_rightDualBiprodIso_inv :
    biprod.inl ≫ (rightDualBiprodIso X Y).inv = (biprod.fst : X ⊞ Y ⟶ X)ᘁ := by
  simp [rightDualBiprodIso, rightDualBinaryBicone]

/-- The second component of the inverse of `rightDualBiprodIso` is the mate of the second
projection. -/
@[reassoc (attr := simp)]
theorem inr_rightDualBiprodIso_inv :
    biprod.inr ≫ (rightDualBiprodIso X Y).inv = (biprod.snd : X ⊞ Y ⟶ Y)ᘁ := by
  simp [rightDualBiprodIso, rightDualBinaryBicone]

end Biprod

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
