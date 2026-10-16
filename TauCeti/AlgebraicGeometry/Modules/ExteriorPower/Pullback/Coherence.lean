/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Pullback.Basic

/-!
# Coherence of exterior powers under pullback

The canonical exterior-power comparison respects the identity and composition isomorphisms
of module pullback. These equations concern the actual mate of the pushforward comparison,
not a separately chosen isomorphism. They require no quasicoherence or finiteness hypotheses.

The pushforward equations are checked on sheafified wedges of local sections; the pullback
equations use Mathlib's conjugacy of the canonical pullback and pushforward comparisons.

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
  let P := Scheme.Modules.pullback (𝟙 X)
  let Q := Scheme.Modules.pushforward (𝟙 X)
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)
  let a := Scheme.Modules.pullbackId X
  let b := Scheme.Modules.pushforwardId X
  let c : W ⋙ P ⟶ P ⋙ W := Scheme.Modules.pullbackExteriorPowerComparison (𝟙 X) n
  let q : Q ⋙ W ⟶ W ⋙ Q :=
    SheafOfModules.pushforwardExteriorPowerComparison (S := X.sheaf) (R := X.sheaf)
      (𝟙 X : X ⟶ X).toRingCatSheafHom n
  have hu (N : X.Modules) : adj.unit.app N ≫ Q.map (a.hom.app N) = b.inv.app N := by
    simpa only [adj, a, b, Q, Scheme.Modules.conjugateEquiv_pullbackId_hom,
      Adjunction.id_unit, NatTrans.id_app, Category.id_comp, Functor.id_obj] using
      (unit_conjugateEquiv Adjunction.id adj a.hom N).symm
  have hc : adj.unit.app (W.obj M) ≫ Q.map (c.app M) =
      W.map (adj.unit.app M) ≫ q.app (P.obj M) :=
    Scheme.Modules.unit_comp_pushforward_map_pullbackExteriorPowerComparison_app (𝟙 X) n M
  have hq : q.app M ≫ b.hom.app (W.obj M) = W.map (b.hom.app M) :=
    pushforwardExteriorPowerComparison_id n M
  have hn := q.naturality (a.hom.app M)
  dsimp only [Functor.comp_map] at hn
  -- The typed endofunctor `W` avoids repeatedly reconstructing the scheme's sheaf category.
  change c.app M ≫ W.map (a.hom.app M) = a.hom.app (W.obj M)
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, hc, Category.assoc, ← hn,
    ← W.map_comp_assoc, hu M, hu]
  dsimp only [Functor.id_obj]
  rw [(Iso.eq_comp_inv (b.app (W.obj M))).mpr hq, ← W.map_comp_assoc]
  simp only [Iso.inv_hom_id_app, Functor.id_obj, Iso.app_inv]
  rw [W.map_id M]
  exact Category.id_comp _

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
  have h₁ : mateEquiv A A c₁ = q₁ := by
    dsimp only [c₁, q₁, A]
    rw [Scheme.Modules.pullbackExteriorPowerComparison_eq]
    exact SheafOfModules.mateEquiv_pullbackExteriorPowerComparison
      (S := Z.sheaf) (R := Y.sheaf) (φ := g.toRingCatSheafHom) A n
  have h₂ : mateEquiv B B c₂ = q₂ := by
    dsimp only [c₂, q₂, B]
    rw [Scheme.Modules.pullbackExteriorPowerComparison_eq]
    exact SheafOfModules.mateEquiv_pullbackExteriorPowerComparison
      (S := Y.sheaf) (R := X.sheaf) (φ := f.toRingCatSheafHom) B n
  have h₃ : mateEquiv C C c₃ = q₃ := by
    dsimp only [c₃, q₃, C]
    rw [Scheme.Modules.pullbackExteriorPowerComparison_eq]
    exact SheafOfModules.mateEquiv_pullbackExteriorPowerComparison
      (S := Z.sheaf) (R := X.sheaf) (φ := (f ≫ g : X ⟶ Z).toRingCatSheafHom) C n
  have h : c₃.whiskerLeft (Scheme.Modules.pullbackComp f g).inv =
      (TwoSquare.vComp c₁ c₂).whiskerRight (Scheme.Modules.pullbackComp f g).inv := by
    apply (mateEquiv (A.comp B) C).injective
    rw [conjugateEquiv_mateEquiv_vcomp, mateEquiv_conjugateEquiv_vcomp,
      mateEquiv_hcomp, h₁, h₂, h₃, Scheme.Modules.conjugateEquiv_pullbackComp_inv]
    apply NatTrans.ext
    funext N
    -- Normalize square composition before crossing the scheme-module wrappers.
    simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
      NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.assoc]
    exact (pushforwardExteriorPowerComparison_comp f g n N).symm
  -- Components of the square operations are the two routes in the asserted diagram.
  simpa only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.vComp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using congr_app h M

end

end TauCeti.AlgebraicGeometry
