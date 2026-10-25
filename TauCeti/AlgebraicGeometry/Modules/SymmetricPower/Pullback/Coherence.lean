/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Pullback.Basic
public import TauCeti.CategoryTheory.Adjunction.Mates

/-!
# Coherence of symmetric powers under pullback

The canonical symmetric-power comparison `f^* (Symⁿ M) ⟶ Symⁿ (f^* M)` respects the identity
and composition isomorphisms of module pullback. These equations concern the actual mate of the
pushforward comparison, not a separately chosen isomorphism, and require no quasicoherence or
finiteness hypotheses.

The pushforward equations are checked on sheafified sectionwise symmetric tensors; the pullback
equations then follow from Mathlib's conjugacy of the canonical pullback and pushforward
comparisons by `CategoryTheory.Adjunction.app_comp_map_hom_app_of_mateEquiv` and
`CategoryTheory.Adjunction.app_comp_map_inv_app_of_mateEquiv`, exactly as for exterior powers in
`TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Pullback.Coherence`.

## Main results

* `TauCeti.AlgebraicGeometry.pushforwardSymmetricPowerComparison_id` and
  `TauCeti.AlgebraicGeometry.pushforwardSymmetricPowerComparison_comp`: the corresponding
  equations for the comparison `Symⁿ (f_* M) ⟶ f_* (Symⁿ M)` of pushforward;
* `TauCeti.AlgebraicGeometry.pullbackSymmetricPowerComparison_id`: along `𝟙 X` the comparison is
  induced by `Scheme.Modules.pullbackId`;
* `TauCeti.AlgebraicGeometry.pullbackSymmetricPowerComparison_comp`: along `f ≫ g` the
  comparison is the composite of the comparisons along `g` and `f`, through
  `Scheme.Modules.pullbackComp`.

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

/-- The symmetric-power comparison for identity pushforward agrees with the canonical
identification of identity pushforward. -/
@[reassoc]
theorem pushforwardSymmetricPowerComparison_id (n : ℕ) (M : X.Modules) :
    (SheafOfModules.pushforwardSymmetricPowerComparison (S := X.sheaf) (R := X.sheaf)
      (𝟙 X : X ⟶ X).toRingCatSheafHom n).app M ≫
        (Scheme.Modules.pushforwardId X).hom.app
          ((_root_.SheafOfModules.symmetricPower X.sheaf n).obj M) =
      (_root_.SheafOfModules.symmetricPower X.sheaf n).map
        ((Scheme.Modules.pushforwardId X).hom.app M) := by
  apply SheafOfModules.symmetricPower_hom_ext n ((Scheme.Modules.pushforward (𝟙 X)).obj M)
  intro U x
  -- Display evaluation of the composite: the identification of identity pushforward is the
  -- identity on sections, whereas rewriting its projection searches through the scheme-module
  -- wrappers.
  change ((SheafOfModules.pushforwardSymmetricPowerComparison (S := X.sheaf) (R := X.sheaf)
      (𝟙 X : X ⟶ X).toRingCatSheafHom n).app M).val.app U _ = _
  rw [_root_.SheafOfModules.symmetricPower_map_val_app_unit (R := X.sheaf) n
    ((Scheme.Modules.pushforwardId X).hom.app M) U x]
  -- `erw`: the evaluation lemma is stated for `SheafOfModules.pushforward`, which
  -- `Scheme.Modules.pushforward` wraps.
  erw [SheafOfModules.pushforwardSymmetricPowerComparison_app_val_app_unit
      (S := X.sheaf) (R := X.sheaf) (𝟙 X : X ⟶ X).toRingCatSheafHom n M U x]
  -- Both sides sheafify a symmetric tensor of the same sections; it remains to compare them.
  congr 2
  apply Subtype.ext
  -- Both maps are the identity on scalars and on sections.
  refine (TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleMapₛₗ_apply _ n x).trans ?_
  refine (DFunLike.congr_fun (_root_.SymmetricAlgebra.mapₛₗ_eq_id (fun _ ↦ rfl)
    (fun _ ↦ rfl)) x.1).trans ?_
  exact ((ModuleCat.symmetricPower.coe_map_apply_eq_mapₛₗ
    (((Scheme.Modules.pushforwardId X).hom.app M).val.app' U) n x).trans
      (DFunLike.congr_fun (_root_.SymmetricAlgebra.mapₛₗ_eq_id (fun _ ↦ rfl) (fun _ ↦ rfl))
        x.1)).symm

/-- The symmetric-power comparison for composite pushforward is the composite of the two
successive comparisons, through the canonical pushforward composition isomorphism. -/
@[reassoc]
theorem pushforwardSymmetricPowerComparison_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (M : X.Modules) :
    (SheafOfModules.pushforwardSymmetricPowerComparison (S := Z.sheaf) (R := Y.sheaf)
        g.toRingCatSheafHom n).app ((Scheme.Modules.pushforward f).obj M) ≫
        (Scheme.Modules.pushforward g).map
          ((SheafOfModules.pushforwardSymmetricPowerComparison (S := Y.sheaf) (R := X.sheaf)
            f.toRingCatSheafHom n).app M) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app
          ((_root_.SheafOfModules.symmetricPower X.sheaf n).obj M) =
      (_root_.SheafOfModules.symmetricPower Z.sheaf n).map
          ((Scheme.Modules.pushforwardComp f g).hom.app M) ≫
        (SheafOfModules.pushforwardSymmetricPowerComparison (S := Z.sheaf) (R := X.sheaf)
          (f ≫ g : X ⟶ Z).toRingCatSheafHom n).app M := by
  apply SheafOfModules.symmetricPower_hom_ext (R := Z.sheaf) n
    ((Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f).obj M))
  intro U x
  -- Display evaluation of the composites: rewriting their projections searches through the
  -- scheme-module wrappers, whereas composition on sections is function composition.
  change ((Scheme.Modules.pushforwardComp f g).hom.app
      ((_root_.SheafOfModules.symmetricPower X.sheaf n).obj M)).val.app U
      (((Scheme.Modules.pushforward g).map
        ((SheafOfModules.pushforwardSymmetricPowerComparison (S := Y.sheaf) (R := X.sheaf)
          f.toRingCatSheafHom n).app M)).val.app U
        (((SheafOfModules.pushforwardSymmetricPowerComparison (S := Z.sheaf) (R := Y.sheaf)
          g.toRingCatSheafHom n).app ((Scheme.Modules.pushforward f).obj M)).val.app U _)) =
    ((SheafOfModules.pushforwardSymmetricPowerComparison (S := Z.sheaf) (R := X.sheaf)
      (f ≫ g : X ⟶ Z).toRingCatSheafHom n).app M).val.app U
      (((_root_.SheafOfModules.symmetricPower Z.sheaf n).map
        ((Scheme.Modules.pushforwardComp f g).hom.app M)).val.app U _)
  -- Evaluate the comparisons along `g` and then `f` on the left; `pushforwardComp` is the
  -- identity on sections. As in `pushforwardSymmetricPowerComparison_id`, `erw` is needed
  -- because the evaluation lemma is stated for `SheafOfModules.pushforward`.
  erw [SheafOfModules.pushforwardSymmetricPowerComparison_app_val_app_unit
    (S := Z.sheaf) (R := Y.sheaf) g.toRingCatSheafHom n
    ((Scheme.Modules.pushforward f).obj M) U x]
  erw [SheafOfModules.pushforwardSymmetricPowerComparison_app_val_app_unit
    (S := Y.sheaf) (R := X.sheaf) f.toRingCatSheafHom n M
    ((TopologicalSpace.Opens.map g.base).op.obj U)]
  -- Evaluate the symmetric power of `pushforwardComp` and then the comparison along `f ≫ g` on
  -- the right. The two sides are now indexed by `(Opens.map f.base).op.obj ((Opens.map
  -- g.base).op.obj U)` and `(Opens.map (f ≫ g).base).op.obj U`; rewriting the whole goal makes
  -- the motive compare these indexings and times out, so rewrite the right side alone.
  conv_rhs =>
    erw [_root_.SheafOfModules.symmetricPower_map_val_app_unit (R := Z.sheaf) n
      ((Scheme.Modules.pushforwardComp f g).hom.app M) U x]
    erw [SheafOfModules.pushforwardSymmetricPowerComparison_app_val_app_unit
      (S := Z.sheaf) (R := X.sheaf) (f ≫ g : X ⟶ Z).toRingCatSheafHom n M U]
  -- Both sides sheafify a symmetric tensor of the same sections; it remains to compare the
  -- induced maps of symmetric algebras. Each step is a `refine` because `rw` here builds a motive
  -- that compares the two indexings again and times out.
  congr 2
  apply Subtype.ext
  refine (TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleMapₛₗ_apply _ n _).trans ?_
  refine (congrArg (_root_.SymmetricAlgebra.mapₛₗ _)
    (TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleMapₛₗ_apply _ n x)).trans ?_
  refine Eq.trans ?_ (TauCeti.SymmetricAlgebra.coe_homogeneousSubmoduleMapₛₗ_apply _ n _).symm
  refine Eq.trans ?_ (congrArg (_root_.SymmetricAlgebra.mapₛₗ _)
    (ModuleCat.symmetricPower.coe_map_apply_eq_mapₛₗ _ n x)).symm
  -- The coefficient maps and the maps of sections compose on the nose.
  apply _root_.SymmetricAlgebra.mapₛₗ_mapₛₗ_eq <;> intro <;> rfl

/-- The symmetric-power comparison along the identity is induced by the canonical identity
isomorphism of module pullback. -/
@[simp, reassoc]
theorem pullbackSymmetricPowerComparison_id (n : ℕ) (M : X.Modules) :
    (Scheme.Modules.pullbackSymmetricPowerComparison (𝟙 X) n).app M ≫
        (_root_.SheafOfModules.symmetricPower X.sheaf n).map
          ((Scheme.Modules.pullbackId X).hom.app M) =
      (Scheme.Modules.pullbackId X).hom.app
        ((_root_.SheafOfModules.symmetricPower X.sheaf n).obj M) := by
  let W : X.Modules ⥤ X.Modules := _root_.SheafOfModules.symmetricPower X.sheaf n
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X)
  let c : TwoSquare W _ _ W := Scheme.Modules.pullbackSymmetricPowerComparison (𝟙 X) n
  let q : TwoSquare (Scheme.Modules.pushforward (𝟙 X)) W W (Scheme.Modules.pushforward (𝟙 X)) :=
    SheafOfModules.pushforwardSymmetricPowerComparison (S := X.sheaf) (R := X.sheaf)
      (𝟙 X : X ⟶ X).toRingCatSheafHom n
  have hcq : mateEquiv adj adj c = q :=
    Scheme.Modules.mateEquiv_pullbackSymmetricPowerComparison (𝟙 X) n
  -- The typed endofunctor `W` avoids repeatedly reconstructing the scheme's sheaf category.
  exact adj.app_comp_map_hom_app_of_mateEquiv (Scheme.Modules.pullbackId X)
    (Scheme.Modules.pushforwardId X) (Scheme.Modules.conjugateEquiv_pullbackId_hom X) c q hcq
    (pushforwardSymmetricPowerComparison_id n) M

/-- The symmetric-power comparison for a composite agrees with the two successive comparisons,
using the canonical composition isomorphism of module pullback. -/
@[reassoc]
theorem pullbackSymmetricPowerComparison_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (M : Z.Modules) :
    (Scheme.Modules.pullbackSymmetricPowerComparison (f ≫ g) n).app M ≫
        (_root_.SheafOfModules.symmetricPower X.sheaf n).map
          ((Scheme.Modules.pullbackComp f g).inv.app M) =
      (Scheme.Modules.pullbackComp f g).inv.app
          ((_root_.SheafOfModules.symmetricPower Z.sheaf n).obj M) ≫
        (Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullbackSymmetricPowerComparison g n).app M) ≫
        (Scheme.Modules.pullbackSymmetricPowerComparison f n).app
          ((Scheme.Modules.pullback g).obj M) := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction g
  let B := Scheme.Modules.pullbackPushforwardAdjunction f
  let C := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  let W₁ : Z.Modules ⥤ Z.Modules := _root_.SheafOfModules.symmetricPower Z.sheaf n
  let W₂ : Y.Modules ⥤ Y.Modules := _root_.SheafOfModules.symmetricPower Y.sheaf n
  let W₃ : X.Modules ⥤ X.Modules := _root_.SheafOfModules.symmetricPower X.sheaf n
  let c₁ : TwoSquare W₁ _ _ W₂ := Scheme.Modules.pullbackSymmetricPowerComparison g n
  let c₂ : TwoSquare W₂ _ _ W₃ := Scheme.Modules.pullbackSymmetricPowerComparison f n
  let c₃ : TwoSquare W₁ _ _ W₃ := Scheme.Modules.pullbackSymmetricPowerComparison (f ≫ g) n
  let q₁ : TwoSquare (Scheme.Modules.pushforward g) W₂ W₁ (Scheme.Modules.pushforward g) :=
    SheafOfModules.pushforwardSymmetricPowerComparison (S := Z.sheaf) (R := Y.sheaf)
      g.toRingCatSheafHom n
  let q₂ : TwoSquare (Scheme.Modules.pushforward f) W₃ W₂ (Scheme.Modules.pushforward f) :=
    SheafOfModules.pushforwardSymmetricPowerComparison (S := Y.sheaf) (R := X.sheaf)
      f.toRingCatSheafHom n
  let q₃ : TwoSquare (Scheme.Modules.pushforward (f ≫ g)) W₃ W₁
      (Scheme.Modules.pushforward (f ≫ g)) :=
    SheafOfModules.pushforwardSymmetricPowerComparison (S := Z.sheaf) (R := X.sheaf)
      (f ≫ g : X ⟶ Z).toRingCatSheafHom n
  have h₁ : mateEquiv A A c₁ = q₁ :=
    Scheme.Modules.mateEquiv_pullbackSymmetricPowerComparison g n
  have h₂ : mateEquiv B B c₂ = q₂ :=
    Scheme.Modules.mateEquiv_pullbackSymmetricPowerComparison f n
  have h₃ : mateEquiv C C c₃ = q₃ :=
    Scheme.Modules.mateEquiv_pullbackSymmetricPowerComparison (f ≫ g) n
  exact A.app_comp_map_inv_app_of_mateEquiv B C (Scheme.Modules.pullbackComp f g)
    (Scheme.Modules.pushforwardComp f g) (Scheme.Modules.conjugateEquiv_pullbackComp_inv f g)
    c₁ c₂ c₃ q₁ q₂ q₃ h₁ h₂ h₃ (pushforwardSymmetricPowerComparison_comp f g n) M

end

end TauCeti.AlgebraicGeometry
