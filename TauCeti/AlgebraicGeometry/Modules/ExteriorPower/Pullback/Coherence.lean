/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Pullback.Basic
public import TauCeti.CategoryTheory.Adjunction.Mates

/-!
# Coherence of exterior powers under pullback

The canonical exterior-power comparison respects the identity and composition isomorphisms
of module pullback. These equations concern the actual mate of the pushforward comparison,
not a separately chosen isomorphism. They require no quasicoherence or finiteness hypotheses.

The pushforward equations are checked on sheafified wedges of local sections; the pullback
equations follow from Mathlib's conjugacy of the canonical pullback and pushforward comparisons
by `CategoryTheory.Adjunction.app_comp_map_hom_app_of_mateEquiv` and
`CategoryTheory.Adjunction.app_comp_map_inv_app_of_mateEquiv`.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.16.
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y Z : Scheme.{u}}

/-- The exterior-power comparison for identity pushforward agrees with the canonical
identification of identity pushforward. -/
@[reassoc]
theorem pushforwardExteriorPowerComparison_id (n : ℕ) (M : X.Modules) :
    (SheafOfModules.pushforwardExteriorPowerComparison (S := X.sheaf) (R := X.sheaf)
      (𝟙 X : X ⟶ X).toRingCatSheafHom n).app M ≫
        (Scheme.Modules.pushforwardId X).hom.app
          ((_root_.SheafOfModules.exteriorPower X.sheaf n).obj M) =
      (_root_.SheafOfModules.exteriorPower X.sheaf n).map
        ((Scheme.Modules.pushforwardId X).hom.app M) := by
  apply SheafOfModules.exteriorPower_hom_ext n
    ((Scheme.Modules.pushforward (𝟙 X)).obj M)
  intro U m
  -- Identity pushforward and its comparison act identically on sections.
  erw [_root_.SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  erw [SheafOfModules.pushforwardExteriorPowerComparison_app_val_app_mk
      (S := X.sheaf) (R := X.sheaf) (𝟙 X : X ⟶ X).toRingCatSheafHom n M U m,
    _root_.SheafOfModules.exteriorPower_map_val_app_mk (R := X.sheaf)]
  rfl

/-- The exterior-power comparison for composite pushforward is the composite of the two
successive comparisons, through the canonical pushforward composition isomorphism. -/
@[reassoc]
theorem pushforwardExteriorPowerComparison_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (M : X.Modules) :
    (SheafOfModules.pushforwardExteriorPowerComparison (S := Z.sheaf) (R := Y.sheaf)
        g.toRingCatSheafHom n).app ((Scheme.Modules.pushforward f).obj M) ≫
        (Scheme.Modules.pushforward g).map
          ((SheafOfModules.pushforwardExteriorPowerComparison (S := Y.sheaf) (R := X.sheaf)
            f.toRingCatSheafHom n).app M) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app
          ((_root_.SheafOfModules.exteriorPower X.sheaf n).obj M) =
      (_root_.SheafOfModules.exteriorPower Z.sheaf n).map
          ((Scheme.Modules.pushforwardComp f g).hom.app M) ≫
        (SheafOfModules.pushforwardExteriorPowerComparison (S := Z.sheaf) (R := X.sheaf)
          (f ≫ g : X ⟶ Z).toRingCatSheafHom n).app M := by
  apply SheafOfModules.exteriorPower_hom_ext (R := Z.sheaf) n
    ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f).obj M))
  intro U m
  -- Display evaluation of the composites: rewriting their projections searches through the
  -- scheme-module wrappers, whereas composition on sections is ordinary function composition.
  change ((Scheme.Modules.pushforwardComp f g).hom.app
      ((_root_.SheafOfModules.exteriorPower X.sheaf n).obj M)).val.app U
      (((Scheme.Modules.pushforward g).map
        ((SheafOfModules.pushforwardExteriorPowerComparison (S := Y.sheaf) (R := X.sheaf)
          f.toRingCatSheafHom n).app M)).val.app U
        (((SheafOfModules.pushforwardExteriorPowerComparison (S := Z.sheaf) (R := Y.sheaf)
          g.toRingCatSheafHom n).app ((Scheme.Modules.pushforward f).obj M)).val.app U _)) =
    ((SheafOfModules.pushforwardExteriorPowerComparison (S := Z.sheaf) (R := X.sheaf)
      (f ≫ g : X ⟶ Z).toRingCatSheafHom n).app M).val.app U
      (((_root_.SheafOfModules.exteriorPower Z.sheaf n).map
        ((Scheme.Modules.pushforwardComp f g).hom.app M)).val.app U _)
  erw [SheafOfModules.pushforwardExteriorPowerComparison_app_val_app_mk
    (S := Z.sheaf) (R := Y.sheaf) g.toRingCatSheafHom n
    ((Scheme.Modules.pushforward f).obj M)]
  erw [SheafOfModules.pushforwardExteriorPowerComparison_app_val_app_mk
    (S := Y.sheaf) (R := X.sheaf) f.toRingCatSheafHom n M]
  erw [_root_.SheafOfModules.exteriorPower_map_val_app_mk (R := Z.sheaf)]
  erw [SheafOfModules.pushforwardExteriorPowerComparison_app_val_app_mk
    (S := Z.sheaf) (R := X.sheaf) (f ≫ g : X ⟶ Z).toRingCatSheafHom n M]
  rfl

/-- The exterior-power comparison along the identity is induced by the canonical identity
isomorphism of module pullback. -/
@[simp, reassoc]
theorem pullbackExteriorPowerComparison_id (n : ℕ) (M : X.Modules) :
    (Scheme.Modules.pullbackExteriorPowerComparison (𝟙 X) n).app M ≫
        (_root_.SheafOfModules.exteriorPower X.sheaf n).map
          ((Scheme.Modules.pullbackId X).hom.app M) =
      (Scheme.Modules.pullbackId X).hom.app
        ((_root_.SheafOfModules.exteriorPower X.sheaf n).obj M) := by
  let W : X.Modules ⥤ X.Modules := _root_.SheafOfModules.exteriorPower X.sheaf n
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)
  let c : TwoSquare W _ _ W := Scheme.Modules.pullbackExteriorPowerComparison (𝟙 X) n
  let q : TwoSquare (Scheme.Modules.pushforward (𝟙 X)) W W (Scheme.Modules.pushforward (𝟙 X)) :=
    SheafOfModules.pushforwardExteriorPowerComparison (S := X.sheaf) (R := X.sheaf)
      (𝟙 X : X ⟶ X).toRingCatSheafHom n
  have hcq : mateEquiv adj adj c = q :=
    Scheme.Modules.mateEquiv_pullbackExteriorPowerComparison (𝟙 X) n
  -- The typed endofunctor `W` avoids repeatedly reconstructing the scheme's sheaf category.
  exact adj.app_comp_map_hom_app_of_mateEquiv (Scheme.Modules.pullbackId X)
    (Scheme.Modules.pushforwardId X) (Scheme.Modules.conjugateEquiv_pullbackId_hom X) c q hcq
    (pushforwardExteriorPowerComparison_id n) M

/-- The exterior-power comparison for a composite agrees with the two successive comparisons,
using the canonical composition isomorphism of module pullback. -/
@[reassoc]
theorem pullbackExteriorPowerComparison_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (M : Z.Modules) :
    (Scheme.Modules.pullbackExteriorPowerComparison (f ≫ g) n).app M ≫
        (_root_.SheafOfModules.exteriorPower X.sheaf n).map
          ((Scheme.Modules.pullbackComp f g).inv.app M) =
      (Scheme.Modules.pullbackComp f g).inv.app
          ((_root_.SheafOfModules.exteriorPower Z.sheaf n).obj M) ≫
        (Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullbackExteriorPowerComparison g n).app M) ≫
        (Scheme.Modules.pullbackExteriorPowerComparison f n).app
          ((Scheme.Modules.pullback g).obj M) := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction g
  let B := Scheme.Modules.pullbackPushforwardAdjunction f
  let C := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  let W₁ : Z.Modules ⥤ Z.Modules := _root_.SheafOfModules.exteriorPower Z.sheaf n
  let W₂ : Y.Modules ⥤ Y.Modules := _root_.SheafOfModules.exteriorPower Y.sheaf n
  let W₃ : X.Modules ⥤ X.Modules := _root_.SheafOfModules.exteriorPower X.sheaf n
  let c₁ : TwoSquare W₁ _ _ W₂ := Scheme.Modules.pullbackExteriorPowerComparison g n
  let c₂ : TwoSquare W₂ _ _ W₃ := Scheme.Modules.pullbackExteriorPowerComparison f n
  let c₃ : TwoSquare W₁ _ _ W₃ := Scheme.Modules.pullbackExteriorPowerComparison (f ≫ g) n
  let q₁ : TwoSquare (Scheme.Modules.pushforward g) W₂ W₁ (Scheme.Modules.pushforward g) :=
    SheafOfModules.pushforwardExteriorPowerComparison (S := Z.sheaf) (R := Y.sheaf)
      g.toRingCatSheafHom n
  let q₂ : TwoSquare (Scheme.Modules.pushforward f) W₃ W₂ (Scheme.Modules.pushforward f) :=
    SheafOfModules.pushforwardExteriorPowerComparison (S := Y.sheaf) (R := X.sheaf)
      f.toRingCatSheafHom n
  let q₃ : TwoSquare (Scheme.Modules.pushforward (f ≫ g)) W₃ W₁
      (Scheme.Modules.pushforward (f ≫ g)) :=
    SheafOfModules.pushforwardExteriorPowerComparison (S := Z.sheaf) (R := X.sheaf)
      (f ≫ g : X ⟶ Z).toRingCatSheafHom n
  have h₁ : mateEquiv A A c₁ = q₁ :=
    Scheme.Modules.mateEquiv_pullbackExteriorPowerComparison g n
  have h₂ : mateEquiv B B c₂ = q₂ :=
    Scheme.Modules.mateEquiv_pullbackExteriorPowerComparison f n
  have h₃ : mateEquiv C C c₃ = q₃ :=
    Scheme.Modules.mateEquiv_pullbackExteriorPowerComparison (f ≫ g) n
  exact A.app_comp_map_inv_app_of_mateEquiv B C (Scheme.Modules.pullbackComp f g)
    (Scheme.Modules.pushforwardComp f g) (Scheme.Modules.conjugateEquiv_pullbackComp_inv f g)
    c₁ c₂ c₃ q₁ q₂ q₃ h₁ h₂ h₃ (pushforwardExteriorPowerComparison_comp f g n) M

end

end TauCeti.AlgebraicGeometry
