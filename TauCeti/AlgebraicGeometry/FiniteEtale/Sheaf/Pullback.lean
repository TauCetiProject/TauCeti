/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Sheaf.Basic
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
noncomputable def toEtaleCompSmallEtaleBaseChangeIso (p : T ⟶ S) :
    toEtale S ⋙ p.smallEtaleBaseChange ≅
      TauCeti.FiniteEtaleScheme.pullback p ⋙ toEtale T :=
  ((Functor.FullyFaithful.ofFullyFaithful (Etale.forget T)).whiskeringRight _).preimageIso
    (toEtaleCompSmallEtaleBaseChangeForgetIso p)

/-- On underlying schemes, the forward component of `toEtaleCompSmallEtaleBaseChangeIso` is the
identity on `Limits.pullback X.obj.hom p`. -/
@[simp]
lemma toEtaleCompSmallEtaleBaseChangeIso_hom_app_left (p : T ⟶ S)
    (X : TauCeti.FiniteEtaleScheme S) :
    ((toEtaleCompSmallEtaleBaseChangeIso p).hom.app X).left =
      𝟙 (Limits.pullback X.obj.hom p) := by
  have h : Functor.whiskerRight (toEtaleCompSmallEtaleBaseChangeIso p).hom (Etale.forget T) =
      (toEtaleCompSmallEtaleBaseChangeForgetIso p).hom :=
    ((Functor.FullyFaithful.ofFullyFaithful (Etale.forget T)).whiskeringRight _).map_preimage _
  refine (congrArg (fun η ↦ (η.app X).left) h).trans ?_
  simp only [toEtaleCompSmallEtaleBaseChangeForgetIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    eqToIso.hom, Category.id_comp,
    smallEtaleBaseChangeCompForgetIso_hom_app_left, Over.comp_left,
    Functor.comp_obj, Etale.forget_obj_left, Over.pullback_obj_left,
    Etale.forget_obj_hom, Functor.id_obj, Functor.const_obj_obj, ObjectProperty.ι_obj,
    CategoryTheory.eqToHom_app, CategoryTheory.eqToHom_map, Over.eqToHom_left]
  exact (Category.id_comp _).trans (eqToHom_refl (Limits.pullback X.obj.hom p) rfl)

/-- On underlying schemes, the inverse component of `toEtaleCompSmallEtaleBaseChangeIso` is the
identity on `Limits.pullback X.obj.hom p`. -/
@[simp]
lemma toEtaleCompSmallEtaleBaseChangeIso_inv_app_left (p : T ⟶ S)
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

/-- On components, `(p.toSheafCompSmallEtaleMapPushforwardIso).hom.app X` factors through
`p.yonedaCompSmallEtaleMapPushforwardIso` and `toEtaleCompSmallEtaleBaseChangeIso`. -/
@[reassoc]
lemma toSheafCompSmallEtaleMapPushforwardIso_hom_app (p : T ⟶ S) [Etale p]
    (X : TauCeti.FiniteEtaleScheme S) :
    (p.toSheafCompSmallEtaleMapPushforwardIso).hom.app X =
      p.yonedaCompSmallEtaleMapPushforwardIso.hom.app ((toEtale S).obj X) ≫
        (smallEtaleTopology T).yoneda.map ((toEtaleCompSmallEtaleBaseChangeIso p).hom.app X) := by
  simp [toSheafCompSmallEtaleMapPushforwardIso, toSheafCompSmallEtalePullbackIso, toSheaf,
    yonedaCompSmallEtalePullbackIso_hom_app_of_etale]

/-- On components, `(p.toSheafCompSmallEtaleMapPushforwardIso).inv.app X` factors through
`toEtaleCompSmallEtaleBaseChangeIso` and `p.yonedaCompSmallEtaleMapPushforwardIso`. -/
@[reassoc]
lemma toSheafCompSmallEtaleMapPushforwardIso_inv_app (p : T ⟶ S) [Etale p]
    (X : TauCeti.FiniteEtaleScheme S) :
    (p.toSheafCompSmallEtaleMapPushforwardIso).inv.app X =
      (smallEtaleTopology T).yoneda.map ((toEtaleCompSmallEtaleBaseChangeIso p).inv.app X) ≫
        p.yonedaCompSmallEtaleMapPushforwardIso.inv.app ((toEtale S).obj X) := by
  simp [toSheafCompSmallEtaleMapPushforwardIso, toSheafCompSmallEtalePullbackIso, toSheaf,
    yonedaCompSmallEtalePullbackIso_inv_app_of_etale]

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
  have hs :
      (((p.toSheafCompSmallEtaleMapPushforwardIso).hom.app X).hom.app (Opposite.op W)) s =
        ((smallEtaleTopology T).yoneda.map
            ((toEtaleCompSmallEtaleBaseChangeIso p).hom.app X)).hom.app (Opposite.op W)
          ((p.yonedaCompSmallEtaleMapPushforwardIso.hom.app ((toEtale S).obj X)).hom.app
            (Opposite.op W) s) :=
    congrArg (fun η ↦ (η.hom.app (Opposite.op W)) s)
      (p.toSheafCompSmallEtaleMapPushforwardIso_hom_app X)
  rw [hs]
  apply MorphismProperty.Over.Hom.ext
  have h :
      (((smallEtaleTopology T).yoneda.map
            ((toEtaleCompSmallEtaleBaseChangeIso p).hom.app X)).hom.app (Opposite.op W)
          ((p.yonedaCompSmallEtaleMapPushforwardIso.hom.app ((toEtale S).obj X)).hom.app
            (Opposite.op W) s)).left =
        (p.smallEtaleMapBaseChangeAdj.homEquiv W ((toEtale S).obj X) s).left ≫
          𝟙 (Limits.pullback X.obj.hom p) := by
    simp
    rfl
  exact h.trans (Category.comp_id _)

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
  have ht :
      (((p.toSheafCompSmallEtaleMapPushforwardIso).inv.app X).hom.app (Opposite.op W)) t =
        (p.yonedaCompSmallEtaleMapPushforwardIso.inv.app ((toEtale S).obj X)).hom.app
          (Opposite.op W)
          (((smallEtaleTopology T).yoneda.map
            ((toEtaleCompSmallEtaleBaseChangeIso p).inv.app X)).hom.app (Opposite.op W) t) :=
    congrArg (fun η ↦ (η.hom.app (Opposite.op W)) t)
      (p.toSheafCompSmallEtaleMapPushforwardIso_inv_app X)
  rw [ht]
  dsimp only [toSheaf]
  have h1 :
      (p.yonedaCompSmallEtaleMapPushforwardIso.inv.app ((toEtale S).obj X)).hom.app
          (Opposite.op W)
          (((smallEtaleTopology T).yoneda.map
            ((toEtaleCompSmallEtaleBaseChangeIso p).inv.app X)).hom.app (Opposite.op W) t) =
        (p.smallEtaleMapBaseChangeAdj.homEquiv W ((toEtale S).obj X)).symm
          (t ≫ (toEtaleCompSmallEtaleBaseChangeIso p).inv.app X) := by
    simp
    rfl
  refine h1.trans (congrArg (p.smallEtaleMapBaseChangeAdj.homEquiv W ((toEtale S).obj X)).symm ?_)
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
