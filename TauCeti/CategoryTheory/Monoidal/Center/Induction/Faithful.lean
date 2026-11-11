/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Center.Induction

/-!
# Faithfulness of induction into the Drinfeld centre

When the tensor unit is simple, the induction functor into the Drinfeld centre is faithful.
Indeed, its underlying object is the sum of `S ⊗ X ⊗ Sᘁ` over simple classes `S`. The summand
indexed by the class of the unit is canonically isomorphic to `X`, and the unit-to-unit matrix
entry of an induced morphism recovers that morphism.

This argument uses neither a pivotal structure nor a characteristic assumption, and does not
require the induction adjunctions. The recovery formula is an identity in the underlying
category, not a retraction in the centre.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], §7.13
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Limits TauCeti

universe w v u

namespace CategoryTheory.Center

attribute [local instance] Abelian.hasFiniteBiproducts

section UnitSummand

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [HasZeroMorphisms C]
  [RightRigidCategory C] [Simple (𝟙_ C)]

/-- The right dual of the representative of the unit class is isomorphic to the tensor unit. -/
def unitReprDualIso : (SimpleClasses.classOf (𝟙_ C)).reprᘁ ≅ 𝟙_ C :=
  rightDualIso (RightRigidCategory.rightDual _).exact
    (exactPairingCongrLeft (Y := 𝟙_ C) (SimpleClasses.classOfReprIso (𝟙_ C)))

/-- The summand indexed by the class of the tensor unit is canonically isomorphic to `X`.
The dual of the chosen representative is identified with the unit by uniqueness of right duals. -/
def inductionUnitSummandIso (X : C) :
    (SimpleClasses.classOf (𝟙_ C)).repr ⊗ X ⊗ (SimpleClasses.classOf (𝟙_ C)).reprᘁ ≅ X :=
  tensorIso (SimpleClasses.classOfReprIso (𝟙_ C)) (tensorIso (Iso.refl X) unitReprDualIso) ≪≫
    (λ_ _) ≪≫ (ρ_ X)

/-- The unit-summand identification uses the representative's isomorphism to the unit,
uniqueness of its right dual, and the two unitors. -/
theorem inductionUnitSummandIso_hom (X : C) :
    (inductionUnitSummandIso X).hom =
      (SimpleClasses.classOfReprIso (𝟙_ C)).hom ▷
          (X ⊗ (SimpleClasses.classOf (𝟙_ C)).reprᘁ) ≫
        (𝟙_ C) ◁ X ◁ (unitReprDualIso (C := C)).hom ≫
        (λ_ (X ⊗ 𝟙_ C)).hom ≫ (ρ_ X).hom := by
  simp [inductionUnitSummandIso, tensorHom_def]

/-- The identification of the unit summand is natural in `X`. -/
@[reassoc]
theorem inductionUnitSummandIso_hom_naturality {X Y : C} (f : X ⟶ Y) :
    (SimpleClasses.classOf (𝟙_ C)).repr ◁ f ▷ (SimpleClasses.classOf (𝟙_ C)).reprᘁ ≫
        (inductionUnitSummandIso Y).hom = (inductionUnitSummandIso X).hom ≫ f := by
  simp only [inductionUnitSummandIso_hom, Category.assoc]
  rw [whisker_exchange_assoc, ← whiskerLeft_comp_assoc, ← whisker_exchange,
    whiskerLeft_comp_assoc, leftUnitor_naturality_assoc, rightUnitor_naturality]

end UnitSummand

section Recovery

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [Fintype (SimpleClasses C)]

/-- A morphism is recovered from its induced matrix by taking the unit-to-unit entry and
identifying the unit summands with the original source and target.
This is not a simp lemma: biproduct simplification already reduces its left-hand side. -/
theorem inductionMap_unit_component {X Y : C} (f : X ⟶ Y) :
    (inductionUnitSummandIso X).inv ≫
      biproduct.ι (inductionSummand X) (SimpleClasses.classOf (𝟙_ C)) ≫ inductionMap f ≫
      biproduct.π (inductionSummand Y) (SimpleClasses.classOf (𝟙_ C)) ≫
      (inductionUnitSummandIso Y).hom = f := by
  simp only [biproduct.map_π_assoc, biproduct.ι_π_self_assoc]
  rw [inductionUnitSummandIso_hom_naturality, Iso.inv_hom_id_assoc]

end Recovery

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear k C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear k C] [RightRigidCategory C] [LeftRigidCategory C]
  [IsFiniteSemisimpleCategory C] [∀ X Y : C, FiniteDimensional k (X ⟶ Y)]
  [Fintype (SimpleClasses C)] [Simple (𝟙_ C)]

/-- Induction into the Drinfeld centre is faithful when the tensor unit is simple. -/
instance induction_faithful : (induction k C).Faithful where
  map_injective {X Y} f g h := by
    have h' : inductionMap f = inductionMap g := by
      simpa only [induction_map_f, induction_obj, inductionCenterObj_fst] using
        congrArg (fun t ↦ t.f) h
    rw [← inductionMap_unit_component f, h', inductionMap_unit_component]

end CategoryTheory.Center
