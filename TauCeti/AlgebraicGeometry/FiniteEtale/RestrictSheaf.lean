/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Sheaf
public import TauCeti.AlgebraicGeometry.Sites.Etale.Pullback

/-!
# Base change of sheaves of sections of finite étale schemes

This file relates the sheaf of sections functor `TauCeti.FiniteEtaleScheme.toSheaf` to inverse
image on the small étale site (`TauCeti.AlgebraicGeometry.Sites.Etale.Pullback`).

For any morphism of schemes `p : T ⟶ S`, pulling back the sheaf of sections of a finite étale
`S`-scheme `X` along `p` yields the sheaf of sections of its base change
`(FiniteEtaleScheme.pullback p).obj X`
(`AlgebraicGeometry.Scheme.Hom.toSheafCompSmallEtalePullbackIso`). When `p` is étale, the same
holds for sheaf restriction along `p.smallEtaleMap`
(`AlgebraicGeometry.Scheme.Hom.toSheafCompSmallEtaleMapPushforwardIso`), with explicit component
formulas via `p.smallEtaleMapBaseChangeAdj`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.toSheafCompSmallEtalePullbackIso`: natural isomorphism
  `toSheaf S ⋙ p.smallEtalePullback (Type u) ≅ FiniteEtaleScheme.pullback p ⋙ toSheaf T` for
  any morphism of schemes `p : T ⟶ S`.
* `AlgebraicGeometry.Scheme.Hom.toSheafCompSmallEtaleMapPushforwardIso`: natural isomorphism
  `toSheaf S ⋙ p.smallEtaleMap.sheafPushforwardContinuous (Type u) _ _ ≅`
  `FiniteEtaleScheme.pullback p ⋙ toSheaf T` when `p` is étale.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé IX, §2.
* The Stacks Project, [Tag 03Q4](https://stacks.math.columbia.edu/tag/03Q4).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.FiniteEtaleScheme

variable {S T : Scheme.{u}}

private noncomputable def toEtaleCompSmallEtaleBaseChangeForgetIso (p : T ⟶ S) :
    (toEtale S ⋙ p.smallEtaleBaseChange) ⋙ Etale.forget T ≅
      (TauCeti.FiniteEtaleScheme.pullback p ⋙ toEtale T) ⋙ Etale.forget T :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (toEtale S) p.smallEtaleBaseChangeCompForgetIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso (toEtale_comp_forget S)) _ ≪≫
    eqToIso (pullback_comp_ι p).symm ≪≫
    Functor.isoWhiskerLeft (TauCeti.FiniteEtaleScheme.pullback p)
      (eqToIso (toEtale_comp_forget T).symm) ≪≫
    (Functor.associator _ _ _).symm

/-- Compatibility of `toEtale` and base change `smallEtaleBaseChange` with `pullback p`, lifted
from `Over T` along the fully faithful forgetful functor `Etale.forget T`. -/
private noncomputable def toEtaleCompSmallEtaleBaseChangeIso (p : T ⟶ S) :
    toEtale S ⋙ p.smallEtaleBaseChange ≅
      TauCeti.FiniteEtaleScheme.pullback p ⋙ toEtale T :=
  ((Functor.FullyFaithful.ofFullyFaithful (Etale.forget T)).whiskeringRight _).preimageIso
    (toEtaleCompSmallEtaleBaseChangeForgetIso p)

private lemma toEtaleCompSmallEtaleBaseChangeIso_hom_app_left (p : T ⟶ S)
    (X : TauCeti.FiniteEtaleScheme S) :
    ((toEtaleCompSmallEtaleBaseChangeIso p).hom.app X).left =
      𝟙 (Limits.pullback X.obj.hom p) := by
  have h : Functor.whiskerRight (toEtaleCompSmallEtaleBaseChangeIso p).hom (Etale.forget T) =
      (toEtaleCompSmallEtaleBaseChangeForgetIso p).hom :=
    ((Functor.FullyFaithful.ofFullyFaithful (Etale.forget T)).whiskeringRight _).map_preimage _
  refine (congrArg (fun η ↦ (η.app X).left) h).trans ?_
  have happ₁ : ∀ {F G : TauCeti.FiniteEtaleScheme S ⥤ Over S} (e : F = G),
      (eqToHom e).app X = eqToHom (congrArg (·.obj X) e) := by
    rintro F _ rfl; rfl
  have happ₂ : ∀ {F G : TauCeti.FiniteEtaleScheme S ⥤ Over T} (e : F = G),
      (eqToHom e).app X = eqToHom (congrArg (·.obj X) e) := by
    rintro F _ rfl; rfl
  have happ₃ : ∀ {F G : TauCeti.FiniteEtaleScheme T ⥤ Over T} (e : F = G)
      (Y : TauCeti.FiniteEtaleScheme T),
      (eqToHom e).app Y = eqToHom (congrArg (·.obj Y) e) := by
    rintro F _ rfl Y; rfl
  have hmap : ∀ {A B : Over S} (e : A = B),
      (Over.pullback p).map (eqToHom e) = eqToHom (congrArg (Over.pullback p).obj e) := by
    rintro A _ rfl; simp
  have hleft : ∀ {A B : Over T} (e : A = B),
      (eqToHom e).left = eqToHom (congrArg Comma.left e) := by
    rintro A _ rfl; rfl
  simp only [toEtaleCompSmallEtaleBaseChangeForgetIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, eqToIso.hom, Category.id_comp, Category.comp_id,
    happ₁, happ₂, happ₃, hmap, eqToHom_trans, Over.comp_left,
    smallEtaleBaseChangeCompForgetIso_hom_app_left, hleft]
  exact (Category.id_comp _).trans (eqToHom_refl (Limits.pullback X.obj.hom p) rfl)

private lemma toEtaleCompSmallEtaleBaseChangeIso_inv_app_left (p : T ⟶ S)
    (X : TauCeti.FiniteEtaleScheme S) :
    ((toEtaleCompSmallEtaleBaseChangeIso p).inv.app X).left =
      𝟙 (Limits.pullback X.obj.hom p) := by
  have hid : ((toEtaleCompSmallEtaleBaseChangeIso p).hom.app X ≫
      (toEtaleCompSmallEtaleBaseChangeIso p).inv.app X).left =
      𝟙 (Limits.pullback X.obj.hom p) :=
    congrArg (·.left) ((toEtaleCompSmallEtaleBaseChangeIso p).hom_inv_id_app X)
  exact (Category.id_comp _).symm.trans
    ((congrArg (· ≫ _) (toEtaleCompSmallEtaleBaseChangeIso_hom_app_left p X).symm).trans
      ((MorphismProperty.Comma.comp_left _ _).symm.trans hid))

/-- Pulling back the sheaf of sections of a finite étale `S`-scheme along any morphism of schemes
`p : T ⟶ S` gives the sheaf of sections of its base change to `T`, naturally in `X`. -/
noncomputable def toSheafCompSmallEtalePullbackIso (p : T ⟶ S) :
    toSheaf S ⋙ p.smallEtalePullback (Type u) ≅
      TauCeti.FiniteEtaleScheme.pullback p ⋙ toSheaf T :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (toEtale S) p.yonedaCompSmallEtalePullbackIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (toEtaleCompSmallEtaleBaseChangeIso p)
      (smallEtaleTopology T).yoneda ≪≫
    Functor.associator _ _ _

/-- Restricting the sheaf of sections of a finite étale `S`-scheme along an étale morphism
`p : T ⟶ S` via `p.smallEtaleMap` gives the sheaf of sections of its base change to `T`,
naturally in `X`. -/
noncomputable def toSheafCompSmallEtaleMapPushforwardIso (p : T ⟶ S) [Etale p] :
    toSheaf S ⋙ p.smallEtaleMap.sheafPushforwardContinuous (Type u)
        (smallEtaleTopology T) (smallEtaleTopology S) ≅
      TauCeti.FiniteEtaleScheme.pullback p ⋙ toSheaf T :=
  Functor.isoWhiskerLeft (toSheaf S) (p.smallEtalePullbackIsoMapPushforward (Type u)).symm ≪≫
    p.toSheafCompSmallEtalePullbackIso

/-- Transporting a section of `(toSheaf S).obj X` along
`p.toSheafCompSmallEtaleMapPushforwardIso` applies the base-change adjunction
`p.smallEtaleMapBaseChangeAdj`. -/
@[simp]
lemma toSheafCompSmallEtaleMapPushforwardIso_hom_app_hom_app_apply (p : T ⟶ S) [Etale p]
    (X : TauCeti.FiniteEtaleScheme S) (W : T.Etale)
    (s : p.smallEtaleMap.obj W ⟶ (toEtale S).obj X) :
    dsimp%
      (((p.toSheafCompSmallEtaleMapPushforwardIso).hom.app X).hom.app (Opposite.op W)) s =
      MorphismProperty.Over.homMk
        (p.smallEtaleMapBaseChangeAdj.homEquiv W ((toEtale S).obj X) s).left
        (MorphismProperty.Over.w
          (p.smallEtaleMapBaseChangeAdj.homEquiv W ((toEtale S).obj X) s)) := by
  have h1 : (p.toSheafCompSmallEtaleMapPushforwardIso).hom.app X =
      p.yonedaCompSmallEtaleMapPushforwardIso.hom.app ((toEtale S).obj X) ≫
        (smallEtaleTopology T).yoneda.map ((toEtaleCompSmallEtaleBaseChangeIso p).hom.app X) := by
    simp only [toSheafCompSmallEtaleMapPushforwardIso, toSheafCompSmallEtalePullbackIso, toSheaf,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
      Category.id_comp, Category.comp_id]
    rw [yonedaCompSmallEtalePullbackIso_hom_app_of_etale, ← Category.assoc,
      Iso.inv_hom_id_app_assoc]
  rw [h1]
  apply MorphismProperty.Over.Hom.ext
  have heval : ((((p.yonedaCompSmallEtaleMapPushforwardIso.hom.app ((toEtale S).obj X) ≫
        (smallEtaleTopology T).yoneda.map
          ((toEtaleCompSmallEtaleBaseChangeIso p).hom.app X)).hom.app (Opposite.op W))) s).left =
      (p.smallEtaleMapBaseChangeAdj.homEquiv W ((toEtale S).obj X) s ≫
        (toEtaleCompSmallEtaleBaseChangeIso p).hom.app X).left :=
    congrArg (·.left)
      (congrArg (((smallEtaleTopology T).yoneda.map
        ((toEtaleCompSmallEtaleBaseChangeIso p).hom.app X)).hom.app (Opposite.op W))
        (p.yonedaCompSmallEtaleMapPushforwardIso_hom_app_hom_app_apply
          ((toEtale S).obj X) W s))
  exact heval.trans
    ((MorphismProperty.Comma.comp_left _ _).trans
      ((congrArg (_ ≫ ·) (toEtaleCompSmallEtaleBaseChangeIso_hom_app_left p X)).trans
        (Category.comp_id _)))

/-- Transporting a section of `(toSheaf T).obj ((FiniteEtaleScheme.pullback p).obj X)` along the
inverse of `p.toSheafCompSmallEtaleMapPushforwardIso` applies the inverse of
`p.smallEtaleMapBaseChangeAdj`. -/
@[simp]
lemma toSheafCompSmallEtaleMapPushforwardIso_inv_app_hom_app_apply (p : T ⟶ S) [Etale p]
    (X : TauCeti.FiniteEtaleScheme S) (W : T.Etale)
    (t : W ⟶ (toEtale T).obj ((TauCeti.FiniteEtaleScheme.pullback p).obj X)) :
    dsimp%
      (((p.toSheafCompSmallEtaleMapPushforwardIso).inv.app X).hom.app (Opposite.op W)) t =
      (p.smallEtaleMapBaseChangeAdj.homEquiv W ((toEtale S).obj X)).symm
        (MorphismProperty.Over.homMk t.left (MorphismProperty.Over.w t)) := by
  have h1 : (p.toSheafCompSmallEtaleMapPushforwardIso).inv.app X =
      (smallEtaleTopology T).yoneda.map ((toEtaleCompSmallEtaleBaseChangeIso p).inv.app X) ≫
        p.yonedaCompSmallEtaleMapPushforwardIso.inv.app ((toEtale S).obj X) := by
    simp only [toSheafCompSmallEtaleMapPushforwardIso, toSheafCompSmallEtalePullbackIso, toSheaf,
      Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj,
      Category.id_comp, Category.comp_id]
    rw [yonedaCompSmallEtalePullbackIso_inv_app_of_etale, Category.assoc, Category.assoc,
      Iso.inv_hom_id_app]
    exact congrArg (_ ≫ ·) (Category.comp_id _)
  rw [h1]
  have heval : (((((smallEtaleTopology T).yoneda.map
        ((toEtaleCompSmallEtaleBaseChangeIso p).inv.app X) ≫
        p.yonedaCompSmallEtaleMapPushforwardIso.inv.app ((toEtale S).obj X)).hom.app
          (Opposite.op W))) t) =
      (p.smallEtaleMapBaseChangeAdj.homEquiv W ((toEtale S).obj X)).symm
        (t ≫ (toEtaleCompSmallEtaleBaseChangeIso p).inv.app X) :=
    p.yonedaCompSmallEtaleMapPushforwardIso_inv_app_hom_app_apply ((toEtale S).obj X) W
      (t ≫ (toEtaleCompSmallEtaleBaseChangeIso p).inv.app X)
  refine heval.trans
    (congrArg (p.smallEtaleMapBaseChangeAdj.homEquiv W ((toEtale S).obj X)).symm ?_)
  apply MorphismProperty.Over.Hom.ext
  exact (MorphismProperty.Comma.comp_left _ _).trans
    ((congrArg (_ ≫ ·) (toEtaleCompSmallEtaleBaseChangeIso_inv_app_left p X)).trans
      (Category.comp_id _))

/-- When `p` is étale, `p.toSheafCompSmallEtalePullbackIso.hom.app X` factors through
`p.smallEtalePullbackIsoMapPushforward` and `p.toSheafCompSmallEtaleMapPushforwardIso`. -/
lemma toSheafCompSmallEtalePullbackIso_hom_app_of_etale (p : T ⟶ S) [Etale p]
    (X : TauCeti.FiniteEtaleScheme S) :
    p.toSheafCompSmallEtalePullbackIso.hom.app X =
      (p.smallEtalePullbackIsoMapPushforward (Type u)).hom.app ((toSheaf S).obj X) ≫
        p.toSheafCompSmallEtaleMapPushforwardIso.hom.app X := by
  simp [toSheafCompSmallEtaleMapPushforwardIso]

/-- When `p` is étale, `p.toSheafCompSmallEtalePullbackIso.inv.app X` factors through
`p.toSheafCompSmallEtaleMapPushforwardIso` and `p.smallEtalePullbackIsoMapPushforward`. -/
lemma toSheafCompSmallEtalePullbackIso_inv_app_of_etale (p : T ⟶ S) [Etale p]
    (X : TauCeti.FiniteEtaleScheme S) :
    p.toSheafCompSmallEtalePullbackIso.inv.app X =
      p.toSheafCompSmallEtaleMapPushforwardIso.inv.app X ≫
        (p.smallEtalePullbackIsoMapPushforward (Type u)).inv.app ((toSheaf S).obj X) := by
  simp [toSheafCompSmallEtaleMapPushforwardIso]

end AlgebraicGeometry.Scheme.Hom
