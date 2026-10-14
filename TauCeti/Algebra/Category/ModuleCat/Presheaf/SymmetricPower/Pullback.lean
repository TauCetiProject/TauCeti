/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.SymmetricPower.Basic
public import TauCeti.Algebra.Category.ModuleCat.SymmetricPower.RestrictScalars
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The symmetric-power pullback comparison for module presheaves

Pushforward, including restriction of scalars, has a canonical comparison from the symmetric
power of a pushforward to the pushforward of the symmetric power. On sections it sends a product
`m₁ ⋯ mₙ` over the source coefficient ring to the same product over the target coefficient ring.
Taking its mate under the pullback--pushforward adjunction constructs a natural map
`α* (Symⁿ M) ⟶ Symⁿ (α* M)` for pullback of module presheaves. Only the adjunction is needed
for this construction. This supplies the sectionwise input to symmetric-power pullback
comparisons for sheaves. Restriction of scalars does not generally give an isomorphism of
symmetric powers, and no invertibility assertion is made here.

The construction follows the exterior-power comparison
`TauCeti.PresheafOfModules.pullbackExteriorPowerComparison`: it uses the module-level
restriction-of-scalars comparison `TauCeti.ModuleCat.restrictScalarsSymmetricPowerComparison` and
Mathlib's `CategoryTheory.mateEquiv` for the pullback--pushforward adjunction. The section formula
specifies the pushforward comparison, and the unit equation specifies the pullback comparison.

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

private def symmetricPowerPushforwardMap (n : ℕ)
    (M : PresheafOfModulesOfCommRing.{u} R) :
    (PresheafOfModulesOfCommRing.symmetricPower n).obj
        ((PresheafOfModulesOfCommRing.pushforward α).obj M) ⟶
      (PresheafOfModulesOfCommRing.pushforward α).obj
        ((PresheafOfModulesOfCommRing.symmetricPower n).obj M) where
  app U := (ModuleCat.restrictScalarsSymmetricPowerComparison (α.app U).hom n).app
    (M.obj (F.op.obj U))
  naturality {U V} f := by
    ext x
    apply Subtype.ext
    -- Both sides are composites of ring homomorphisms of symmetric algebras induced by
    -- semilinear maps. The intermediate modules agree only after unfolding the pushforward, so
    -- the section formulas are instantiated explicitly rather than rewritten.
    have h₁ := ModuleCat.coe_restrictScalarsSymmetricPowerComparison_app_apply (α.app V).hom n
      (M.obj (F.op.obj V)) ((((PresheafOfModulesOfCommRing.symmetricPower n).obj
        ((PresheafOfModulesOfCommRing.pushforward α).obj M)).map f) x)
    have h₂ := PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply n
      ((PresheafOfModulesOfCommRing.pushforward α).obj M) f x
    have h₃ := ModuleCat.coe_restrictScalarsSymmetricPowerComparison_app_apply (α.app U).hom n
      (M.obj (F.op.obj U)) x
    have h₄ := PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply n M (F.op.map f)
      ((ModuleCat.restrictScalarsSymmetricPowerComparison (α.app U).hom n).app
        (M.obj (F.op.obj U)) x)
    refine (h₁.trans (congrArg (SymmetricAlgebra.mapₛₗ _) h₂)).trans
      (Eq.trans ?_ (h₄.trans (congrArg (SymmetricAlgebra.mapₛₗ _) h₃)).symm)
    exact SymmetricAlgebra.mapₛₗ_mapₛₗ_eq _ _ _ _
      (fun r ↦ ConcreteCategory.congr_hom (α.naturality f) r) (fun _ ↦ rfl) _

/-- Pushforward of module presheaves carries the canonical symmetric-power comparison.
It changes the coefficient ring of a product of sections, without changing its factors. -/
def pushforwardSymmetricPowerComparison (n : ℕ) :
    PresheafOfModulesOfCommRing.pushforward α ⋙
        PresheafOfModulesOfCommRing.symmetricPower n ⟶
      PresheafOfModulesOfCommRing.symmetricPower n ⋙
        PresheafOfModulesOfCommRing.pushforward α where
  app := symmetricPowerPushforwardMap α n
  naturality {M N} φ := by
    ext U : 1
    -- Pushforward evaluates a presheaf morphism at `F.op.obj U`; its section map is
    -- restriction of scalars of that module morphism. Symmetric powers also evaluate sectionwise.
    exact (ModuleCat.restrictScalarsSymmetricPowerComparison (α.app U).hom n).naturality
      (φ.app' (F.op.obj U))

/-- On sections over `U`, the pushforward comparison is computed in the symmetric algebra by the
ring homomorphism induced by the identity of `M(F U)`, viewed as a semilinear map over
`α.app U`; it sends a product of sections over `S(U)` to the same product over `R(F U)`. -/
@[simp]
theorem coe_pushforwardSymmetricPowerComparison_app_app_apply (n : ℕ)
    (M : PresheafOfModulesOfCommRing.{u} R) (U : Cᵒᵖ)
    (x : PresheafOfModulesOfCommRing.obj
      ((PresheafOfModulesOfCommRing.symmetricPower n).obj
        ((PresheafOfModulesOfCommRing.pushforward α).obj M)) U) :
    dsimp% only [Functor.comp_obj, Functor.op_obj]
    (Subtype.val (((pushforwardSymmetricPowerComparison α n).app M).app' U x) =
      SymmetricAlgebra.mapₛₗ ((_root_.ModuleCat.semilinearMapAddEquiv (α.app U).hom _
        (M.obj (F.op.obj U))).symm (𝟙 _)) x.1) :=
  ModuleCat.coe_restrictScalarsSymmetricPowerComparison_app_apply (α.app U).hom n
    (M.obj (F.op.obj U)) x

variable [(PresheafOfModulesOfCommRing.pushforward.{u} α).IsRightAdjoint]

/-- The canonical map from the pullback of a symmetric power to the symmetric power of a
pullback, characterized by compatibility with the pullback unit. -/
def pullbackSymmetricPowerComparison (n : ℕ) :
    PresheafOfModulesOfCommRing.symmetricPower n ⋙ PresheafOfModulesOfCommRing.pullback α ⟶
      PresheafOfModulesOfCommRing.pullback α ⋙ PresheafOfModulesOfCommRing.symmetricPower n :=
  let A := PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α
  ((mateEquiv A A).symm (TwoSquare.mk _ _ _ _
    (pushforwardSymmetricPowerComparison α n))).natTrans

/-- The adjunction equation characterizes the canonical pullback comparison. -/
@[reassoc (attr := simp)]
theorem unit_comp_pushforward_pullbackSymmetricPowerComparison (n : ℕ)
    (M : PresheafOfModulesOfCommRing.{u} S) :
    (PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α).unit.app
        ((PresheafOfModulesOfCommRing.symmetricPower n).obj M) ≫
      (PresheafOfModulesOfCommRing.pushforward α).map
        ((pullbackSymmetricPowerComparison α n).app M) =
    (PresheafOfModulesOfCommRing.symmetricPower n).map
        ((PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α).unit.app M) ≫
      (pushforwardSymmetricPowerComparison α n).app
        ((PresheafOfModulesOfCommRing.pullback α).obj M) :=
  (unit_mateEquiv_symm (PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α)
    (PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α)
    (TwoSquare.mk _ _ _ _ (pushforwardSymmetricPowerComparison α n)) M).symm

/-- On sections in the image of the pullback unit, the pullback comparison is computed in the
symmetric algebra by the ring homomorphism induced by the unit, viewed as a semilinear map over
`α.app U`; it sends a product of sections to the product of their images under the unit. -/
@[simp]
theorem coe_pullbackSymmetricPowerComparison_app_app_unit_apply (n : ℕ)
    (M : PresheafOfModulesOfCommRing.{u} S) (U : Cᵒᵖ)
    (x : PresheafOfModulesOfCommRing.obj ((PresheafOfModulesOfCommRing.symmetricPower n).obj M)
      U) :
    dsimp% only [Functor.comp_obj, Functor.op_obj, Functor.id_obj]
    (Subtype.val (((PresheafOfModulesOfCommRing.pushforward α).map
        ((pullbackSymmetricPowerComparison α n).app M)).app' U
      (((PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α).unit.app
        ((PresheafOfModulesOfCommRing.symmetricPower n).obj M)).app' U x)) =
    SymmetricAlgebra.mapₛₗ ((_root_.ModuleCat.semilinearMapAddEquiv (α.app U).hom _ _).symm
      (((PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α).unit.app M).app U))
        x.1) := by
  let η := (PresheafOfModulesOfCommRing.pullbackPushforwardAdjunction α).unit
  let P := (PresheafOfModulesOfCommRing.pullback α).obj M
  -- By the adjunction equation, this is the pushforward comparison applied after the symmetric
  -- power of the unit. As in `symmetricPowerPushforwardMap`, the section formulas are
  -- instantiated explicitly, and the two induced ring homomorphisms are composed at the end.
  have h₀ := congrArg (fun g ↦ Subtype.val (g.app' U x))
    (unit_comp_pushforward_pullbackSymmetricPowerComparison α n M)
  have h₁ := coe_pushforwardSymmetricPowerComparison_app_app_apply α n P U
    (((PresheafOfModulesOfCommRing.symmetricPower n).map (η.app M)).app' U x)
  have h₂ := ModuleCat.symmetricPower.coe_map_apply ((η.app M).app' U) n x
  refine h₀.trans (h₁.trans ((congrArg (SymmetricAlgebra.mapₛₗ _) h₂).trans ?_))
  refine (congrArg (SymmetricAlgebra.mapₛₗ _)
    (RingHom.congr_fun (SymmetricAlgebra.mapₛₗ_eq_map _).symm x.1)).trans ?_
  exact RingHom.congr_fun (SymmetricAlgebra.mapₛₗ_comp_mapₛₗ _ _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)) x.1

end

end TauCeti.PresheafOfModules
