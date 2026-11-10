/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Envelope.Quotient.Rigid
public import TauCeti.CategoryTheory.Monoidal.Pivotal.Functor.Basic

/-!
# Pivotal and spherical quotients by tensor ideals

The pivotal isomorphism of a rigid monoidal preadditive category descends to its quotient
by a tensor ideal. With the descended duals, its component is simply the class of the original
component. The quotient functor is pivotal and preserves both traces. Consequently sphericality
also descends. These structures permit taking negligible quotients without losing the trace
and dimension operations.

## References

* J. W. Barrett and B. W. Westbury, *Spherical categories*, Adv. Math. 143 (1999), 357–375.
* F. M. Goodman and H. Wenzl, *Ideals in the Temperley–Lieb category*, Sections 1–3.
-/

public section

universe v u

namespace TauCeti.MonoidalQuotient

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] {I : MonoidalIdeal C}

/-- The dual comparison for the quotient functor is the identity: its chosen duals are
exactly the images of the source duals. -/
@[simp]
theorem mapRightDualIso_eq_refl (X : C) [HasRightDual X] :
    (toMonoidalQuotient I).mapRightDualIso X = Iso.refl _ := by
  apply Iso.ext
  apply ExactPairing.rightHom_ext (X := (toMonoidalQuotient I).obj X)
  simpa using Functor.mapRightDualIso_hom_whiskerRight_evaluation
    (F := toMonoidalQuotient I) X

section RightRigid

variable [RightRigidCategory C]

/-- The tensor comparison of the right dual descends to the quotient. -/
@[simp]
theorem rightDualTensorIso_hom (X Y : C) :
    (rightDualTensorIso ((toMonoidalQuotient I).obj X)
      ((toMonoidalQuotient I).obj Y)).hom =
        (toMonoidalQuotient I).map (rightDualTensorIso X Y).hom := by
  apply ExactPairing.rightHom_ext
    (X := (toMonoidalQuotient I).obj X ⊗ (toMonoidalQuotient I).obj Y)
  rw [TauCeti.rightDualTensorIso_hom_whiskerRight_evaluation]
  have h := congrArg (toMonoidalQuotient I).map
    (TauCeti.rightDualTensorIso_hom_whiskerRight_evaluation (X := X) (Y := Y)).symm
  simp only [ExactPairing.tensor_evaluation, evaluation_rightDual] at h ⊢
  -- Rewriting the tensor or dual objects separately gives an ill-typed motive for the
  -- mapped comparison. Identify the entire composite of classes with its source image.
  change (toMonoidalQuotient I).map (ε_ (X ⊗ Y) (X ⊗ Y)ᘁ) =
    (toMonoidalQuotient I).map ((rightDualTensorIso X Y).hom ▷ (X ⊗ Y) ≫
      (𝟙 _ ⊗≫ Yᘁ ◁ (ε_ X Xᘁ ▷ Y) ⊗≫ ε_ Y Yᘁ))
  exact h

/-- The inverse tensor comparison of the right dual also descends. -/
@[simp]
theorem rightDualTensorIso_inv (X Y : C) :
    (rightDualTensorIso ((toMonoidalQuotient I).obj X)
      ((toMonoidalQuotient I).obj Y)).inv =
        (toMonoidalQuotient I).map (rightDualTensorIso X Y).inv := by
  have h : rightDualTensorIso ((toMonoidalQuotient I).obj X)
      ((toMonoidalQuotient I).obj Y) =
        (toMonoidalQuotient I).mapIso (rightDualTensorIso X Y) :=
    Iso.ext (rightDualTensorIso_hom X Y)
  exact congrArg Iso.inv h

/-- The tensorator of the double right dual is the class of its original tensorator. -/
@[simp]
theorem doubleRightDualFunctor_μ (X Y : C) :
    μ (doubleRightDualFunctor (MonoidalQuotient I))
      ((toMonoidalQuotient I).obj X) ((toMonoidalQuotient I).obj Y) =
        (toMonoidalQuotient I).map (μ (doubleRightDualFunctor C) X Y) := by
  rw [TauCeti.doubleRightDualFunctor_μ, TauCeti.doubleRightDualFunctor_μ,
    rightDualTensorIso_hom]
  -- The dual endpoints are definitionally source images, but rewriting them separately
  -- would abstract them away from the fixed endpoints of the mapped comparison.
  change (rightDualTensorIso ((toMonoidalQuotient I).obj Yᘁ)
    ((toMonoidalQuotient I).obj Xᘁ)).inv ≫
      ((toMonoidalQuotient I).map (rightDualTensorIso X Y).hom)ᘁ = _
  rw [rightDualTensorIso_inv, rightAdjointMate_map, ← Functor.map_comp]
  rfl

/-- The identification of the chosen right dual of the unit with the unit descends. The
rigid category's choice is explicit, since the unit also has a canonical self-duality. -/
@[simp]
theorem rightDualUnitIso_hom :
    (rightDualIso
      (RightRigidCategory.rightDual (𝟙_ (MonoidalQuotient I))).exact
      exactPairingUnit).hom =
    (toMonoidalQuotient I).map (rightDualIso
      (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).hom := by
  apply ExactPairing.rightHom_ext (X := 𝟙_ (MonoidalQuotient I))
  rw [ExactPairing.rightDualIso_hom_whiskerRight_evaluation]
  rw [evaluation_rightDual]
  have h := congrArg (toMonoidalQuotient I).map
    (ExactPairing.rightDualIso_hom_whiskerRight_evaluation
      (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).symm
  -- The unit object is a class, but rewriting it alone would alter the dependent dual.
  -- The unit pairing is defined by unitors, which are themselves classes of the unitors.
  change (toMonoidalQuotient I).map (ε_ (𝟙_ C)
      ((RightRigidCategory.rightDual (𝟙_ C)).rightDual)) =
    (toMonoidalQuotient I).map ((rightDualIso
      (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).hom ▷
        (𝟙_ C) ≫ ε_ (𝟙_ C) (𝟙_ C))
  exact h

/-- The inverse identification of the chosen unit dual descends. -/
@[simp]
theorem rightDualUnitIso_inv :
    (rightDualIso (RightRigidCategory.rightDual (𝟙_ (MonoidalQuotient I))).exact
      exactPairingUnit).inv =
    (toMonoidalQuotient I).map (rightDualIso
      (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit).inv := by
  have h : rightDualIso (RightRigidCategory.rightDual (𝟙_ (MonoidalQuotient I))).exact
      exactPairingUnit = (toMonoidalQuotient I).mapIso
        (rightDualIso (RightRigidCategory.rightDual (𝟙_ C)).exact exactPairingUnit) :=
    Iso.ext rightDualUnitIso_hom
  exact congrArg Iso.inv h

/-- The unit comparison of the double right dual descends, using the rigid structure's
chosen dual of the unit on both sides. -/
@[simp]
theorem doubleRightDualFunctor_ε :
    ε (doubleRightDualFunctor (MonoidalQuotient I)) =
      (toMonoidalQuotient I).map (ε (doubleRightDualFunctor C)) := by
  let : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual _
  rw [TauCeti.doubleRightDualFunctor_ε_eq_rightAdjointMate,
    TauCeti.doubleRightDualFunctor_ε_eq_rightAdjointMate,
    rightDualUnitIso_hom, rightDualUnitIso_inv]
  -- The explicit rigid choices in the unit comparison are exactly the descended choices.
  -- They must be identified together with the mate, rather than rewritten as separate objects.
  change (toMonoidalQuotient I).map _ ≫
    @rightAdjointMate _ _ _ _ _ (instRightRigidCategory.rightDual _)
      (instRightRigidCategory.rightDual _) ((toMonoidalQuotient I).map _) = _
  rw [rightAdjointMate_map, ← Functor.map_comp]
  rfl

end RightRigid

variable [RigidCategory C] [PivotalCategory C]

/-- A pivotal structure descends through any tensor ideal: its components are the classes
of the original pivotal components, for the descended dual choices. -/
noncomputable instance instPivotalCategory : PivotalCategory (MonoidalQuotient I) where
  pivotalIso := NatIso.ofComponents
    (fun X => (toMonoidalQuotient I).mapIso (pivotalIsoApp X.as)) (by
      intro X Y f
      obtain ⟨f, rfl⟩ := (toMonoidalQuotient I).map_surjective f
      simp only [Functor.id_map, doubleRightDualFunctor_map, rightAdjointMate_map]
      exact congrArg (toMonoidalQuotient I).map (pivotalIsoApp_hom_naturality f))
  pivotalIso_isMonoidal := {
    unit := by
      -- Expose the components together with their dependent bidual endpoints.
      change 𝟙 _ ≫ (toMonoidalQuotient I).map (pivotalIsoApp (𝟙_ C)).hom = _
      rw [Category.id_comp, doubleRightDualFunctor_ε]
      exact congrArg (toMonoidalQuotient I).map (pivotalIsoApp_unit_hom (C := C))
    tensor := by
      rintro ⟨X⟩ ⟨Y⟩
      -- Unfolding components alone leaves the bidual functor's object wrappers in their types.
      change 𝟙 _ ≫ (toMonoidalQuotient I).map (pivotalIsoApp (X ⊗ Y)).hom =
        ((toMonoidalQuotient I).map (pivotalIsoApp X).hom ⊗ₘ
          (toMonoidalQuotient I).map (pivotalIsoApp Y).hom) ≫
            μ (doubleRightDualFunctor (MonoidalQuotient I))
              ((toMonoidalQuotient I).obj X) ((toMonoidalQuotient I).obj Y)
      rw [Category.id_comp, doubleRightDualFunctor_μ,
        CategoryTheory.Quotient.map_tensorHom_map]
      exact (congrArg (toMonoidalQuotient I).map (pivotalIsoApp_tensor_hom X Y)).trans
        ((toMonoidalQuotient I).map_comp _ _) }

/-- Each descended pivotal component is the class of the original component. -/
@[simp]
theorem pivotalIsoApp_hom (X : MonoidalQuotient I) :
    (pivotalIsoApp X).hom = (toMonoidalQuotient I).map (pivotalIsoApp X.as).hom := by
  rw [← TauCeti.pivotalIso_hom_app]
  rfl

/-- The inverse pivotal component is the class of the original inverse component. -/
@[simp]
theorem pivotalIsoApp_inv (X : MonoidalQuotient I) :
    (pivotalIsoApp X).inv = (toMonoidalQuotient I).map (pivotalIsoApp X.as).inv := by
  rw [← TauCeti.pivotalIso_inv_app]
  rfl

/-- The quotient functor preserves the pivotal structure, with its descended duals. -/
instance toMonoidalQuotient_isPivotal : (toMonoidalQuotient I).IsPivotal where
  map_pivotalIsoApp_hom X := by
    simp only [pivotalIsoApp_hom, mapRightDualIso_eq_refl, Iso.refl_hom, Iso.refl_inv,
      rightAdjointMate_id]
    -- Normalize the bidual endpoints together; separately simplifying them cannot
    -- rewrite the identities whose domains are fixed by the mapped pivotal component.
    change (toMonoidalQuotient I).map (pivotalIsoApp X).hom =
      (toMonoidalQuotient I).map (pivotalIsoApp X).hom ≫ 𝟙 _ ≫ 𝟙 _
    simp

/-- Sphericality descends through any tensor ideal: both traces of a class are the classes
of the corresponding source traces. -/
instance instSphericalCategory [SphericalCategory C] : SphericalCategory (MonoidalQuotient I) where
  leftTrace_eq_rightTrace := by
    rintro ⟨X⟩ f
    obtain ⟨f, rfl⟩ := (toMonoidalQuotient I).map_surjective f
    rw [Functor.leftTrace_map, Functor.rightTrace_map, SphericalCategory.leftTrace_eq_rightTrace]

-- The general pivotal-functor API gives trace and dimension preservation without extra
-- quotient-specific wrappers or any assumption of nondegeneracy.
example [SphericalCategory C] {X : C} (f : X ⟶ X) :
    trace ((toMonoidalQuotient I).map f) = (toMonoidalQuotient I).map (trace f) := by
  simp [Functor.trace_map]

example [SphericalCategory C] (X : C) :
    quantumDim ((toMonoidalQuotient I).obj X) = (toMonoidalQuotient I).map (quantumDim X) := by
  simp [Functor.quantumDim_map]

end TauCeti.MonoidalQuotient
