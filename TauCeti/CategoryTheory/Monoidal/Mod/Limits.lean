/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Mod.Basic
public import Mathlib.CategoryTheory.Limits.Creates

/-!
# Limits of internal module objects

For a monoidal category acting on a category `D`, the forgetful functor from modules
over a monoid object creates limits. The action on a limiting object is determined by
its composites with the limit projections. No preservation of limits by the action
functors is required. In particular, this constructs limits of spectra presented as
modules over a sphere monoid in symmetric sequences.

The construction follows `Monad.ForgetCreatesLimits` in Mathlib's
`CategoryTheory/Monad/Limits`: lift the action through the limiting cone, and verify
its laws and the equivariance of cone lifts after composing with each projection.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Mod

open Limits MonoidalCategory MonObj MonoidalLeftAction
open scoped MonoidalLeftAction

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalLeftAction C D]
  {A : C} [MonObj A] {J : Type u₃} [Category.{v₃} J]
  (F : J ⥤ Mod D A)

/-- A cone of module objects is limiting whenever its underlying cone is limiting. -/
def isLimitOfForget (c : Cone F) (hc : IsLimit ((forget A).mapCone c)) : IsLimit c where
  lift s := Hom.mk' (hc.lift ((forget A).mapCone s)) (by
    let l : s.pt.X ⟶ c.pt.X := hc.lift ((forget A).mapCone s)
    have hl (j : J) : l ≫ (c.π.app j).hom = (s.π.app j).hom :=
      hc.fac ((forget A).mapCone s) j
    apply hc.hom_ext
    intro j
    -- Name the lift on module carriers to avoid the forgetful cone's opaque presentation.
    change (γ ≫ l) ≫ (c.π.app j).hom = (A ⊴ₗ l ≫ γ) ≫ (c.π.app j).hom
    rw [Category.assoc, hl, Category.assoc, IsModHom.smul_hom (f := (c.π.app j).hom),
      ← actionHomRight_comp_assoc, hl]
    exact IsModHom.smul_hom)
  fac s j := by
    apply hom_ext
    exact hc.fac ((forget A).mapCone s) j
  uniq s m hm := by
    apply hom_ext
    apply hc.uniq ((forget A).mapCone s) m.hom
    intro j
    exact congrArg Hom.hom (hm j)

/-- The universal lift is the lift of the underlying limiting cone. -/
theorem isLimitOfForget_lift_hom (c : Cone F) (hc : IsLimit ((forget A).mapCone c))
    (s : Cone F) :
    ((isLimitOfForget F c hc).lift s).hom = hc.lift ((forget A).mapCone s) := (rfl)

namespace LimitConstruction

variable (c : Cone (F ⋙ forget A)) (hc : IsLimit c)

/-- The cone whose lift supplies the action on the underlying limit. -/
private def actionCone : Cone (F ⋙ forget A) where
  pt := A ⊙ₗ c.pt
  π :=
    { app := fun j ↦ A ⊴ₗ c.π.app j ≫ γ[A, (F.obj j).X]
      naturality := fun i j f ↦ by
        let p (j : J) : c.pt ⟶ (F.obj j).X := c.π.app j
        have hp : p i ≫ (F.map f).hom = p j := c.w f
        -- The named projections retain the actual module-object carriers during rewriting.
        change 𝟙 _ ≫ (A ⊴ₗ p j ≫ γ) = (A ⊴ₗ p i ≫ γ) ≫ (F.map f).hom
        rw [Category.id_comp, Category.assoc, IsModHom.smul_hom,
          ← actionHomRight_comp_assoc, hp] }

/-- The action on the point of an underlying limiting cone. -/
@[instance_reducible]
def action : ModObj A c.pt where
  smul := hc.lift (actionCone F c)
  one_smul := by
    apply hc.hom_ext
    intro j
    let p : c.pt ⟶ (F.obj j).X := c.π.app j
    let l : A ⊙ₗ c.pt ⟶ c.pt := hc.lift (actionCone F c)
    have hp : l ≫ p = A ⊴ₗ p ≫ γ := hc.fac (actionCone F c) j
    -- Use the explicit module carrier instead of the composite functor's presentation.
    change (η ⊵ₗ c.pt ≫ l) ≫ p = (λₗ c.pt).hom ≫ p
    rw [Category.assoc, hp, ← action_exchange_assoc, ModObj.one_smul]
    exact (actionUnitIso_hom_naturality _).symm
  mul_smul := by
    apply hc.hom_ext
    intro j
    let p : c.pt ⟶ (F.obj j).X := c.π.app j
    let l : A ⊙ₗ c.pt ⟶ c.pt := hc.lift (actionCone F c)
    have hp : l ≫ p = A ⊴ₗ p ≫ γ := hc.fac (actionCone F c) j
    -- Keep the projection's module carrier explicit throughout action naturality.
    change (μ ⊵ₗ c.pt ≫ l) ≫ p = ((αₗ A A c.pt).hom ≫ A ⊴ₗ l ≫ l) ≫ p
    simp only [Category.assoc]
    rw [hp]
    rw [← action_exchange_assoc, ModObj.mul_smul]
    rw [← actionHomRight_comp_assoc, hp, actionHomRight_comp]
    simp

/-- Each underlying projection is equivariant for the lifted action. -/
theorem action_smul_π (j : J) :
    letI := action F c hc
    γ[A, c.pt] ≫ c.π.app j = A ⊴ₗ c.π.app j ≫ γ[A, (F.obj j).X] :=
  hc.fac (actionCone F c) j

/-- The module cone lifted from an underlying limiting cone. -/
def cone : Cone F where
  pt := { X := c.pt, mod := action F c hc }
  π :=
    { app := fun j ↦ Hom.mk' (c.π.app j) (action_smul_π F c hc j)
      naturality := fun i j f ↦ by
        apply hom_ext
        simpa [Hom.mk', forget] using (c.w f).symm }

/-- The underlying object of the lifted cone is the specified limit object. -/
theorem cone_pt_X : (cone F c hc).pt.X = c.pt := (rfl)

/-- The lifted projections agree with the specified projections after carrier transport. -/
theorem cone_π_hom (j : J) :
    eqToHom (cone_pt_X F c hc).symm ≫ ((cone F c hc).π.app j).hom = c.π.app j := by
  exact Category.id_comp (c.π.app j)

/-- Forgetting the lifted cone recovers the specified underlying cone. -/
def forgetConeIso : (forget A).mapCone (cone F c hc) ≅ c :=
  Cone.ext (Iso.refl _) (fun _ ↦ by simp [cone, Hom.mk', forget])

/-- The cone lifted from an underlying limit is itself a limit. -/
def isLimit : IsLimit (cone F c hc) :=
  isLimitOfForget F _ (IsLimit.ofIsoLimit hc (forgetConeIso F c hc).symm)

end LimitConstruction

/-- The forgetful functor creates limits for every monoidal left action. -/
noncomputable instance forgetCreatesLimits : CreatesLimitsOfSize.{v₃, u₃} (forget (D := D) A) where
  CreatesLimitsOfShape :=
    { CreatesLimit := fun {F} ↦
        { lifts := fun c hc ↦
            { liftedCone := LimitConstruction.cone F c hc
              validLift := LimitConstruction.forgetConeIso F c hc }
          reflects := fun {c} hc ↦ ⟨isLimitOfForget F c hc⟩ } }

/-- Module objects inherit every shape of limits existing in their ambient category. -/
noncomputable instance hasLimitsOfShape [HasLimitsOfShape J D] : HasLimitsOfShape J (Mod D A) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (forget A)

/-- Module objects inherit limits of every size existing in their ambient category. -/
noncomputable instance hasLimitsOfSize [HasLimitsOfSize.{v₃, u₃} D] :
    HasLimitsOfSize.{v₃, u₃} (Mod D A) :=
  hasLimits_of_hasLimits_createsLimits (forget A)

end CategoryTheory.Mod
