/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Basic

/-!
# The exterior-power pullback comparison for module presheaves

Pushforward, including restriction of scalars, has a canonical comparison from the exterior
power of a pushforward to the pushforward of the exterior power. On sections it sends a wedge
over the source coefficient ring to the same wedge over the target coefficient ring.
Its adjoint constructs a natural map `α* (⋀ⁿ M) ⟶ ⋀ⁿ (α* M)` for pullback of module
presheaves. This supplies the sectionwise input to exterior-power pullback comparisons for
sheaves. Unlike precomposition alone, restriction of scalars does not generally give an
isomorphism of exterior powers; no invertibility assertion is made here.

The construction uses Mathlib's `ModuleCat.exteriorPower.desc` and the pullback--pushforward
adjunction. The wedge formula specifies the pushforward comparison, and the unit equation
specifies the pullback comparison.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.16.
-/

public section

open CategoryTheory

namespace TauCeti.PresheafOfModules

universe u v w v' w'

noncomputable section

variable {C : Type v} [Category.{w} C] {D : Type v'} [Category.{w'} D]
  {F : C ⥤ D} {S : Cᵒᵖ ⥤ CommRingCat.{u}} {R : Dᵒᵖ ⥤ CommRingCat.{u}}
  (α : S ⟶ F.op ⋙ R)

private def exteriorPowerPushforwardApp (n : ℕ)
    (M : PresheafOfModulesOfCommRing.{u} R) (U : Cᵒᵖ) :
    PresheafOfModulesOfCommRing.obj ((PresheafOfModulesOfCommRing.exteriorPower n).obj
      ((PresheafOfModulesOfCommRing.pushforward α).obj M)) U ⟶
      PresheafOfModulesOfCommRing.obj ((PresheafOfModulesOfCommRing.pushforward α).obj
        ((PresheafOfModulesOfCommRing.exteriorPower n).obj M)) U :=
  ModuleCat.exteriorPower.desc
    { toFun m := ModuleCat.exteriorPower.mk (M := M.obj (F.op.obj U)) m
      map_update_add' m i a b :=
        (ModuleCat.exteriorPower.mk (M := M.obj (F.op.obj U))).map_update_add m i a b
      map_update_smul' m i r a :=
        (ModuleCat.exteriorPower.mk (M := M.obj (F.op.obj U))).map_update_smul m i (α.app U r) a
      map_eq_zero_of_eq' m _ _ h hij :=
        (ModuleCat.exteriorPower.mk (M := M.obj (F.op.obj U))).map_eq_zero_of_eq m h hij }

private lemma exteriorPowerPushforwardApp_mk (n : ℕ)
    (M : PresheafOfModulesOfCommRing.{u} R) (U : Cᵒᵖ)
    (m : Fin n → PresheafOfModulesOfCommRing.obj
      ((PresheafOfModulesOfCommRing.pushforward α).obj M) U) :
    exteriorPowerPushforwardApp α n M U (ModuleCat.exteriorPower.mk m) =
      ModuleCat.exteriorPower.mk (M := M.obj (F.op.obj U)) m :=
  ModuleCat.exteriorPower.desc_mk _ _

private def exteriorPowerPushforwardMap (n : ℕ)
    (M : PresheafOfModulesOfCommRing.{u} R) :
    (PresheafOfModulesOfCommRing.exteriorPower n).obj
        ((PresheafOfModulesOfCommRing.pushforward α).obj M) ⟶
      (PresheafOfModulesOfCommRing.pushforward α).obj
        ((PresheafOfModulesOfCommRing.exteriorPower n).obj M) where
  app U := exteriorPowerPushforwardApp α n M U
  naturality {U V} f := by
    apply ModuleCat.exteriorPower.hom_ext (R := S.obj U)
    apply ModuleCat.AlternatingMap.ext
    intro m
    let P := (PresheafOfModulesOfCommRing.pushforward α).obj M
    have h₁ := congrArg (exteriorPowerPushforwardApp α n M V)
      (PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk n P f m)
    have h₂ := exteriorPowerPushforwardApp_mk α n M V (fun j ↦ P.map f (m j))
    have h₃ := congrArg
      (((PresheafOfModulesOfCommRing.pushforward α).obj
        ((PresheafOfModulesOfCommRing.exteriorPower n).obj M)).map f)
      (exteriorPowerPushforwardApp_mk α n M U m)
    have h₄ := PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk n M (F.op.map f) m
    exact (h₁.trans h₂).trans (h₃.trans h₄).symm

/-- Pushforward of module presheaves carries the canonical exterior-power comparison.
It changes the coefficient ring of a wedge, without changing its factors. -/
def pushforwardExteriorPowerComparison (n : ℕ) :
    PresheafOfModulesOfCommRing.pushforward α ⋙
        PresheafOfModulesOfCommRing.exteriorPower n ⟶
      PresheafOfModulesOfCommRing.exteriorPower n ⋙
        PresheafOfModulesOfCommRing.pushforward α where
  app := exteriorPowerPushforwardMap α n
  naturality {M N} φ := by
    ext U : 1
    apply ModuleCat.exteriorPower.hom_ext (R := S.obj U)
    apply ModuleCat.AlternatingMap.ext
    intro m
    have h₁ := congrArg (exteriorPowerPushforwardApp α n N U)
      (ModuleCat.exteriorPower.map_mk
        (((PresheafOfModulesOfCommRing.pushforward α).map φ).app' U) m)
    have h₂ := exteriorPowerPushforwardApp_mk α n N U
      (fun j ↦ φ.app' (F.op.obj U) (m j))
    have h₃ := congrArg (ModuleCat.exteriorPower.map (φ.app' (F.op.obj U)) n)
      (exteriorPowerPushforwardApp_mk α n M U m)
    have h₄ := ModuleCat.exteriorPower.map_mk (φ.app' (F.op.obj U)) m
    exact (h₁.trans h₂).trans (h₃.trans h₄).symm

/-- The presheaf comparison sends a decomposable wedge to the wedge with the same factors,
now balanced over the target ring. -/
@[simp]
theorem pushforwardExteriorPowerComparison_app_app_mk (n : ℕ)
    (M : PresheafOfModulesOfCommRing.{u} R) (U : Cᵒᵖ)
    (m : Fin n → PresheafOfModulesOfCommRing.obj
      ((PresheafOfModulesOfCommRing.pushforward α).obj M) U) :
    dsimp% only [Functor.comp_obj]
    (((pushforwardExteriorPowerComparison α n).app M).app' U
        (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj
          ((PresheafOfModulesOfCommRing.pushforward α).obj M) U) m) =
      ModuleCat.exteriorPower.mk (M := M.obj (F.op.obj U)) m) :=
  exteriorPowerPushforwardApp_mk α n M U m

variable [(PresheafOfModulesOfCommRing.pushforward.{u} α).IsRightAdjoint]

/-- The canonical map from the pullback of an exterior power to the exterior power of a
pullback, characterized by compatibility with the pullback unit and wedges. -/
def pullbackExteriorPowerComparison (n : ℕ) :
    PresheafOfModulesOfCommRing.exteriorPower n ⋙ PresheafOfModulesOfCommRing.pullback α ⟶
      PresheafOfModulesOfCommRing.pullback α ⋙ PresheafOfModulesOfCommRing.exteriorPower n where
  app M := ((PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α).homEquiv _ _).symm
    ((PresheafOfModulesOfCommRing.exteriorPower n).map
        ((PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α).unit.app M) ≫
      (pushforwardExteriorPowerComparison α n).app
        ((PresheafOfModulesOfCommRing.pullback α).obj M))
  naturality {M N} f := by
    dsimp only [Functor.comp_map]
    apply ((PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [Equiv.apply_symm_apply]
    rw [← Category.assoc, ← Functor.map_comp,
      ← (PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α).unit_naturality,
      Functor.map_comp, Category.assoc]
    exact congrArg (fun g ↦ (PresheafOfModulesOfCommRing.exteriorPower n).map
      ((PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α).unit.app M) ≫ g)
      ((pushforwardExteriorPowerComparison α n).naturality
        ((PresheafOfModulesOfCommRing.pullback α).map f))

/-- The adjunction equation characterizes the canonical pullback comparison. -/
@[reassoc (attr := simp)]
theorem unit_comp_pushforward_pullbackExteriorPowerComparison (n : ℕ)
    (M : PresheafOfModulesOfCommRing.{u} S) :
    (PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α).unit.app
        ((PresheafOfModulesOfCommRing.exteriorPower n).obj M) ≫
      (PresheafOfModulesOfCommRing.pushforward α).map
        ((pullbackExteriorPowerComparison α n).app M) =
    (PresheafOfModulesOfCommRing.exteriorPower n).map
        ((PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α).unit.app M) ≫
      (pushforwardExteriorPowerComparison α n).app
        ((PresheafOfModulesOfCommRing.pullback α).obj M) :=
  ((PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α).homEquiv _ _).apply_symm_apply _

/-- On a wedge in the image of the pullback unit, the pullback comparison takes the wedge
of the images of its factors under the unit. -/
@[simp]
theorem pullbackExteriorPowerComparison_app_app_unit_mk (n : ℕ)
    (M : PresheafOfModulesOfCommRing.{u} S) (U : Cᵒᵖ) (m : Fin n → M.obj U) :
    dsimp% only [Functor.comp_obj, Functor.id_obj]
    (((PresheafOfModulesOfCommRing.pushforward α).map
        ((pullbackExteriorPowerComparison α n).app M)).app' U
      (((PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α).unit.app
        ((PresheafOfModulesOfCommRing.exteriorPower n).obj M)).app' U
          (ModuleCat.exteriorPower.mk m)) =
    ModuleCat.exteriorPower.mk
      (M := PresheafOfModulesOfCommRing.obj
        ((PresheafOfModulesOfCommRing.pullback α).obj M) (F.op.obj U))
      (fun i ↦ ((PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α).unit.app M).app' U
        (m i))) := by
  let η := (PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α).unit
  let P := (PresheafOfModulesOfCommRing.pullback α).obj M
  have h := congrArg (fun f ↦ f.app' U (ModuleCat.exteriorPower.mk m))
    (unit_comp_pushforward_pullbackExteriorPowerComparison α n M)
  have h₁ := congrArg (fun x ↦ ((pushforwardExteriorPowerComparison α n).app P).app' U x)
    (ModuleCat.exteriorPower.map_mk ((η.app M).app' U) m)
  have h₂ := pushforwardExteriorPowerComparison_app_app_mk α n P U
    (fun i ↦ (η.app M).app' U (m i))
  exact h.trans (h₁.trans h₂)

end

end TauCeti.PresheafOfModules
