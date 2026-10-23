/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Basic
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The exterior-power pullback comparison for module presheaves

Pushforward, including restriction of scalars, has a canonical comparison from the exterior
power of a pushforward to the pushforward of the exterior power. On sections it sends a wedge
over the source coefficient ring to the same wedge over the target coefficient ring.
Taking its mate under the pullback--pushforward adjunction constructs a natural map
`α* (⋀ⁿ M) ⟶ ⋀ⁿ (α* M)` for pullback of module presheaves. Only the adjunction is needed
for this construction. This supplies the sectionwise input to exterior-power pullback comparisons
for sheaves. Unlike precomposition alone, restriction of scalars does not generally give an
isomorphism of exterior powers. When the coefficient map is an isomorphism, the pushforward
comparison is invertible.

In degree one the pushforward comparison is the identity, read through the identifications
`⋀¹ M ≅ M`.

The construction uses the module-level restriction-of-scalars comparison and Mathlib's
`CategoryTheory.mateEquiv` for the pullback--pushforward adjunction. The wedge formula specifies
the pushforward comparison, and the unit equation specifies the pullback comparison.

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

private def exteriorPowerPushforwardMap (n : ℕ)
    (M : PresheafOfModulesOfCommRing.{u} R) :
    (PresheafOfModulesOfCommRing.exteriorPower n).obj
        ((PresheafOfModulesOfCommRing.pushforward α).obj M) ⟶
      (PresheafOfModulesOfCommRing.pushforward α).obj
        ((PresheafOfModulesOfCommRing.exteriorPower n).obj M) where
  app U := (ModuleCat.restrictScalarsExteriorPowerComparison (α.app U).hom n).app
    (M.obj (F.op.obj U))
  naturality {U V} f := by
    apply ModuleCat.exteriorPower.hom_ext (R := S.obj U)
    apply ModuleCat.AlternatingMap.ext
    intro m
    -- Restriction of scalars gives the concrete-category coercions different bundled objects
    -- with the same carriers, so `simp` cannot match the restriction and comparison formulas.
    -- Apply each wedge formula explicitly on the two sides of the naturality square.
    refine ((congrArg
      ((ModuleCat.restrictScalarsExteriorPowerComparison (α.app V).hom n).app
        (M.obj (F.op.obj V)))
      (PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk n
        ((PresheafOfModulesOfCommRing.pushforward α).obj M) f m)).trans
        (ModuleCat.restrictScalarsExteriorPowerComparison_app_mk (α.app V).hom n
          (M.obj (F.op.obj V)) _)).trans ?_
    -- The pushforward formula uses `.hom` rather than `ConcreteCategory.hom`, so apply it
    -- explicitly to identify the wedge factors before using the target restriction formula.
    refine (congrArg (ModuleCat.exteriorPower.mk (M := M.obj (F.op.obj V)))
      (funext fun j ↦ PresheafOfModules.pushforward_obj_map_apply _ _ _ (m j))).trans ?_
    exact ((congrArg
      (((PresheafOfModulesOfCommRing.pushforward α).obj
        ((PresheafOfModulesOfCommRing.exteriorPower n).obj M)).map f)
      (ModuleCat.restrictScalarsExteriorPowerComparison_app_mk (α.app U).hom n
        (M.obj (F.op.obj U)) m)).trans
      (PresheafOfModulesOfCommRing.exteriorPower_obj_map_mk n M (F.op.map f) m)).symm

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
    -- Pushforward evaluates a presheaf morphism at `F.op.obj U`; its section map is
    -- restriction of scalars of that module morphism. Exterior powers also evaluate sectionwise.
    exact (ModuleCat.restrictScalarsExteriorPowerComparison (α.app U).hom n).naturality
      (φ.app' (F.op.obj U))

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
  ModuleCat.restrictScalarsExteriorPowerComparison_app_mk (α.app U).hom n
    (M.obj (F.op.obj U)) m

/-- In degree one, the pushforward comparison is the identity of `α_* M`, read through the
identifications of first exterior powers with the presheaves themselves. -/
@[reassoc (attr := simp)]
theorem pushforwardExteriorPowerComparison_app_comp_map_exteriorPowerOneIso
    (M : PresheafOfModulesOfCommRing.{u} R) :
    (pushforwardExteriorPowerComparison α 1).app M ≫
        (PresheafOfModulesOfCommRing.pushforward α).map
          ((PresheafOfModulesOfCommRing.exteriorPowerOneIso R).hom.app M) =
      (PresheafOfModulesOfCommRing.exteriorPowerOneIso S).hom.app
        ((PresheafOfModulesOfCommRing.pushforward α).obj M) := by
  ext U : 1
  apply ModuleCat.exteriorPower.hom_ext (R := S.obj U)
  apply ModuleCat.AlternatingMap.ext
  intro m
  -- Both sides send the wedge of a single section `m 0` to `m 0`: the comparison keeps the wedge
  -- and `iso₁` evaluates it.
  have hR := congrArg (fun g ↦ g (ModuleCat.exteriorPower.mk
      (M := PresheafOfModulesOfCommRing.obj M (F.op.obj U)) m))
    (PresheafOfModulesOfCommRing.exteriorPowerOneIso_hom_app_app M (F.op.obj U))
  have hS := congrArg (fun g ↦ g (ModuleCat.exteriorPower.mk (M := PresheafOfModulesOfCommRing.obj
      ((PresheafOfModulesOfCommRing.pushforward α).obj M) U) m))
    (PresheafOfModulesOfCommRing.exteriorPowerOneIso_hom_app_app
      ((PresheafOfModulesOfCommRing.pushforward α).obj M) U)
  exact ((congrArg (((PresheafOfModulesOfCommRing.exteriorPowerOneIso R).hom.app M).app'
      (F.op.obj U)) (pushforwardExteriorPowerComparison_app_app_mk α 1 M U m)).trans
    (hR.trans (ModuleCat.exteriorPower.iso₁_hom_apply
      (M := PresheafOfModulesOfCommRing.obj M (F.op.obj U)) m))).trans
      (hS.trans (ModuleCat.exteriorPower.iso₁_hom_apply m)).symm

-- Adapted from `TauCeti.PresheafOfModules.isIso_pushforwardSymmetricPowerComparison`.
/-- Pushforward along an isomorphism of coefficient presheaves preserves exterior powers
sectionwise. -/
instance isIso_pushforwardExteriorPowerComparison [IsIso α] (n : ℕ) :
    IsIso (pushforwardExteriorPowerComparison α n) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have h (U : Cᵒᵖ) :
      IsIso (((pushforwardExteriorPowerComparison α n).app M).app U) :=
    ModuleCat.isIso_restrictScalarsExteriorPowerComparison_app_of_bijective
      (α.app U).hom ((ConcreteCategory.isIso_iff_bijective (α.app U)).mp inferInstance)
      n (M.obj (F.op.obj U))
  let e := _root_.PresheafOfModules.isoMk
    (fun U ↦ asIso (((pushforwardExteriorPowerComparison α n).app M).app U))
    (fun _ _ f ↦ ((pushforwardExteriorPowerComparison α n).app M).naturality f)
  have he : e.hom = (pushforwardExteriorPowerComparison α n).app M := by
    ext U
    rfl
  rw [← he]
  infer_instance

variable [(PresheafOfModulesOfCommRing.pushforward.{u} α).IsRightAdjoint]

/-- The canonical map from the pullback of an exterior power to the exterior power of a
pullback, characterized by compatibility with the pullback unit and wedges. -/
def pullbackExteriorPowerComparison (n : ℕ) :
    PresheafOfModulesOfCommRing.exteriorPower n ⋙ PresheafOfModulesOfCommRing.pullback α ⟶
      PresheafOfModulesOfCommRing.pullback α ⋙ PresheafOfModulesOfCommRing.exteriorPower n :=
  let A := PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α
  ((mateEquiv A A).symm (TwoSquare.mk _ _ _ _
    (pushforwardExteriorPowerComparison α n)))

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
  (unit_mateEquiv_symm (PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α)
    (PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α)
    (TwoSquare.mk _ _ _ _ (pushforwardExteriorPowerComparison α n)) M).symm

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
  -- `erw` identifies presheaf exterior-power section objects with module exterior powers;
  -- the composition and map formulas themselves are rewritten through the public API.
  erw [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    unit_comp_pushforward_pullbackExteriorPowerComparison, PresheafOfModules.comp_app,
    ModuleCat.comp_apply, PresheafOfModulesOfCommRing.exteriorPower_map_app]
  have h₁ := congrArg (fun x ↦ ((pushforwardExteriorPowerComparison α n).app P).app' U x)
    (ModuleCat.exteriorPower.map_mk ((η.app M).app' U) m)
  have h₂ := pushforwardExteriorPowerComparison_app_app_mk α n P U
    (fun i ↦ (η.app M).app' U (m i))
  exact h₁.trans h₂

end

end TauCeti.PresheafOfModules
