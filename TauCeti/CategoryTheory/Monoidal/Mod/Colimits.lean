/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Limits.Creates

/-!
# Colimits of internal module objects

If the action of a fixed monoid object preserves colimits of a given shape, the
forgetful functor from its modules creates these colimits. The action on the
underlying colimit is induced by the actions on the objects of the diagram.
Thus colimits of modules can be computed in the ambient category.

The construction follows `Monad.ForgetCreatesColimits` in Mathlib's
`CategoryTheory/Monad/Limits`, using the native monoidal-action and module APIs.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Mod

open Limits MonoidalCategory MonObj MonoidalLeftAction
open scoped MonoidalLeftAction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalLeftAction C D]
  {A : C} [MonObj A] {J : Type u₃} [Category.{v₃} J]
  (F : J ⥤ Mod D A) [PreservesColimitsOfShape J (actionLeft D A)]

/-- A module cocone is colimiting whenever its underlying cocone is colimiting. -/
noncomputable def isColimitOfForget (c : Cocone F)
    (hc : IsColimit ((forget A).mapCocone c)) : IsColimit c where
  desc s := Hom.mk' (hc.desc ((forget A).mapCocone s)) (by
    let l : c.pt.X ⟶ s.pt.X := hc.desc ((forget A).mapCocone s)
    have hl (j : J) : (c.ι.app j).hom ≫ l = (s.ι.app j).hom :=
      hc.fac ((forget A).mapCocone s) j
    apply (isColimitOfPreserves (actionLeft D A) hc).hom_ext
    intro j
    -- Name the underlying descent to keep the actual module carriers explicit.
    change (A ⊴ₗ (c.ι.app j).hom) ≫ γ ≫ l =
      (A ⊴ₗ (c.ι.app j).hom) ≫ (A ⊴ₗ l) ≫ γ
    rw [← IsModHom.smul_hom_assoc, hl, ← actionHomRight_comp_assoc, hl]
    exact IsModHom.smul_hom)
  fac s j := by
    apply hom_ext
    exact hc.fac ((forget A).mapCocone s) j
  uniq s m hm := by
    apply hom_ext
    apply hc.uniq ((forget A).mapCocone s) m.hom
    intro j
    exact congrArg Hom.hom (hm j)

/-- The universal descent is the descent of the underlying colimiting cocone. -/
theorem isColimitOfForget_desc_hom (c : Cocone F)
    (hc : IsColimit ((forget A).mapCocone c)) (s : Cocone F) :
    ((isColimitOfForget F c hc).desc s).hom = hc.desc ((forget A).mapCocone s) := (rfl)

namespace ColimitConstruction

variable (c : Cocone (F ⋙ forget A)) (hc : IsColimit c)

/-- The cocone whose descent supplies the action on the underlying colimit. -/
private def actionCocone : Cocone ((F ⋙ forget A) ⋙ actionLeft D A) where
  pt := c.pt
  ι :=
    { app := fun j ↦ γ[A, (F.obj j).X] ≫ c.ι.app j
      naturality := fun i j f ↦ by
        let p (j : J) : (F.obj j).X ⟶ c.pt := c.ι.app j
        have hp : (F.map f).hom ≫ p j = p i := c.w f
        -- These are the actual module carriers of the underlying diagram.
        change (A ⊴ₗ (F.map f).hom) ≫ (γ ≫ p j) = (γ ≫ p i) ≫ 𝟙 _
        rw [← IsModHom.smul_hom_assoc, Category.assoc, hp, Category.comp_id] }

/-- The action map induced on the point of an underlying colimiting cocone. -/
private noncomputable def actionMap : A ⊙ₗ c.pt ⟶ c.pt :=
  (isColimitOfPreserves (actionLeft D A) hc).desc (actionCocone F c)

private theorem actionMap_ι (j : J) :
    A ⊴ₗ c.ι.app j ≫ actionMap F c hc = γ[A, (F.obj j).X] ≫ c.ι.app j :=
  (isColimitOfPreserves (actionLeft D A) hc).fac (actionCocone F c) j

/-- The module structure on the point of an underlying colimiting cocone. -/
@[instance_reducible]
noncomputable def action : ModObj A c.pt where
  smul := actionMap F c hc
  one_smul := by
    have : PreservesColimitsOfShape J (actionLeft D (𝟙_ C)) :=
      preservesColimitsOfShape_of_natIso (actionUnitNatIso C D).symm
    apply (isColimitOfPreserves (actionLeft D (𝟙_ C)) hc).hom_ext
    intro j
    let p : (F.obj j).X ⟶ c.pt := c.ι.app j
    have hp : A ⊴ₗ p ≫ actionMap F c hc = γ ≫ p := actionMap_ι F c hc j
    -- Name the injections to retain their actual source and target carriers.
    change (𝟙_ C) ⊴ₗ p ≫ η ⊵ₗ c.pt ≫ actionMap F c hc =
      (𝟙_ C) ⊴ₗ p ≫ (λₗ c.pt).hom
    rw [action_exchange_assoc η[A] p, hp, ← Category.assoc, ModObj.one_smul]
    exact actionUnitIso_hom_naturality _
  mul_smul := by
    let e : actionLeft D (A ⊗ A) ≅ actionLeft D A ⋙ actionLeft D A :=
      (actionAssocNatIso C D).app A |>.app A
    have : PreservesColimitsOfShape J (actionLeft D (A ⊗ A)) :=
      preservesColimitsOfShape_of_natIso e.symm
    apply (isColimitOfPreserves (actionLeft D (A ⊗ A)) hc).hom_ext
    intro j
    let p : (F.obj j).X ⟶ c.pt := c.ι.app j
    have hp : A ⊴ₗ p ≫ actionMap F c hc = γ ≫ p := actionMap_ι F c hc j
    -- The tensor-square action on injections determines the associativity equation.
    change (A ⊗ A) ⊴ₗ p ≫ μ ⊵ₗ c.pt ≫ actionMap F c hc =
      (A ⊗ A) ⊴ₗ p ≫ (αₗ A A c.pt).hom ≫
        A ⊴ₗ actionMap F c hc ≫ actionMap F c hc
    rw [action_exchange_assoc μ[A] p, hp, ← Category.assoc, ModObj.mul_smul]
    simp only [Category.assoc]
    rw [tensor_actionHomRight_assoc]
    simp only [Iso.inv_hom_id_assoc]
    rw [← actionHomRight_comp_assoc, hp, actionHomRight_comp]
    simp [hp]

/-- Each underlying injection is equivariant for the induced action. -/
theorem ι_action_smul (j : J) :
    letI := action F c hc
    A ⊴ₗ c.ι.app j ≫ γ[A, c.pt] = γ[A, (F.obj j).X] ≫ c.ι.app j :=
  actionMap_ι F c hc j

/-- The module cocone lifted from an underlying colimiting cocone. -/
noncomputable def cocone : Cocone F where
  pt := { X := c.pt, mod := action F c hc }
  ι :=
    { app := fun j ↦ Hom.mk' (c.ι.app j) (ι_action_smul F c hc j).symm
      naturality := fun i j f ↦ by
        apply hom_ext
        simpa [Hom.mk', forget] using c.w f }

/-- The underlying object of the lifted cocone is the specified colimit object. -/
theorem cocone_pt_X : (cocone F c hc).pt.X = c.pt := (rfl)

/-- The lifted injections recover the specified injections after carrier transport. -/
theorem cocone_ι_hom (j : J) :
    ((cocone F c hc).ι.app j).hom ≫ eqToHom (cocone_pt_X F c hc) = c.ι.app j := by
  exact Category.comp_id (c.ι.app j)

/-- Forgetting the lifted cocone recovers the specified underlying cocone. -/
noncomputable def forgetCoconeIso : (forget A).mapCocone (cocone F c hc) ≅ c :=
  Cocone.ext (Iso.refl _) (fun _ ↦ by simp [cocone, Hom.mk', forget])

/-- The cocone lifted from an underlying colimit is itself a colimit. -/
noncomputable def isColimit : IsColimit (cocone F c hc) :=
  isColimitOfForget F _ (IsColimit.ofIsoColimit hc (forgetCoconeIso F c hc).symm)

end ColimitConstruction

/-- The forgetful functor creates colimits preserved by the monoid's action. -/
noncomputable instance forgetCreatesColimitsOfShape :
    CreatesColimitsOfShape J (forget (D := D) A) where
  CreatesColimit := fun {F} ↦
    { lifts := fun c hc ↦
        { liftedCocone := ColimitConstruction.cocone F c hc
          validLift := ColimitConstruction.forgetCoconeIso F c hc }
      reflects := fun {c} hc ↦ ⟨isColimitOfForget F c hc⟩ }

/-- Module objects inherit colimits preserved by the monoid's action. -/
noncomputable instance hasColimitsOfShape [HasColimitsOfShape J D] :
    HasColimitsOfShape J (Mod D A) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (forget A)

/-- The forgetful functor creates colimits of any size preserved by the action. -/
noncomputable instance forgetCreatesColimitsOfSize
    [PreservesColimitsOfSize.{v₃, u₃} (actionLeft D A)] :
    CreatesColimitsOfSize.{v₃, u₃} (forget (D := D) A) where
  CreatesColimitsOfShape := inferInstance

/-- Modules inherit colimits of any size existing in the ambient category and preserved
by the monoid's action. -/
noncomputable instance hasColimitsOfSize [HasColimitsOfSize.{v₃, u₃} D]
    [PreservesColimitsOfSize.{v₃, u₃} (actionLeft D A)] :
    HasColimitsOfSize.{v₃, u₃} (Mod D A) :=
  hasColimits_of_hasColimits_createsColimits (forget A)

end CategoryTheory.Mod
