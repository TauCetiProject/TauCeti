/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Over
public import TauCeti.AlgebraicGeometry.Morphisms.Etale.Basic
public import TauCeti.CategoryTheory.Sites.LocallyConstant
import TauCeti.AlgebraicGeometry.Sites.EtaleSepClosed

/-!
# Restriction of sheaves on the small étale site

Let `p : T ⟶ S` be an étale morphism of schemes. Post-composition with `p` defines a functor
`p.smallEtaleMap : T.Etale ⥤ S.Etale` (Mathlib's `MorphismProperty.Over.map`), left adjoint to
base change `S.Etale ⥤ T.Etale`.

For any `U : S.Etale` identified with `p : T ⟶ S` via an isomorphism `eU : U.left ≅ T` satisfying
`eU.hom ≫ p = U.hom` (for instance `U = Scheme.Etale.mk p`),
`AlgebraicGeometry.Scheme.Etale.overEquiv` identifies `T.Etale` with `Over U`. This equivalence is
a dense subsite in both directions, so `p.smallEtaleMap` is both continuous and cocontinuous for
the small étale topologies, and its right adjoint is continuous.

Consequently, precomposition with `p.smallEtaleMap` defines the sheaf restriction functor
`AlgebraicGeometry.Scheme.Etale.restrictSheaf p :
  Sheaf (smallEtaleTopology S) A ⥤ Sheaf (smallEtaleTopology T) A`
for any coefficient category `A`. It is a left adjoint (with right adjoint pushforward along base
change), so it commutes with the constant sheaf functor whenever sheafification exists
(`constantSheafCompRestrictSheafIso`) and preserves locally constant sheaves with values in any
property `P : ObjectProperty A` (`isLocallyConstantIn_restrictSheaf`).

We also record basic étale covering and locality facts: a single surjective étale morphism covers
its target (`isSheafFor_singleton_of_surjective`), pulling back a jointly surjective étale family
gives a small étale cover of every `U : S.Etale` (`pullback_ofArrows_mem_smallEtaleTopology`), and
a morphism of étale sheaves is an isomorphism if its restrictions along a jointly surjective étale
family are isomorphisms (`isIso_of_forall_isIso_restrictSheaf`).

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.smallEtaleMap`: post-composition `T.Etale ⥤ S.Etale` along an étale
  morphism `p : T ⟶ S`, with `smallEtaleMapCongr` and `smallEtaleMapComp`.
* `AlgebraicGeometry.Scheme.Etale.overEquiv`: the site equivalence `T.Etale ≌ Over U` for any
  `U : S.Etale` identified with `p : T ⟶ S`.
* `AlgebraicGeometry.Scheme.Etale.restrictSheaf`: restriction of small étale sheaves along an étale
  morphism `p : T ⟶ S`, with `restrictSheafOverIso`, `restrictSheafEqIso`, and
  `restrictSheafCompIso`.
* `AlgebraicGeometry.Scheme.Etale.constantSheafCompRestrictSheafIso`,
  `AlgebraicGeometry.Scheme.Etale.restrictSheafConstantSheafIso`: restriction commutes with the
  constant sheaf functor.
* `AlgebraicGeometry.Scheme.Etale.isLocallyConstantIn_restrictSheaf`: restriction preserves locally
  constant sheaves with values in any object property `P`.
* `AlgebraicGeometry.Scheme.Etale.isSheafFor_singleton_of_surjective`,
  `AlgebraicGeometry.Scheme.Etale.pullbackCover`,
  `AlgebraicGeometry.Scheme.Etale.pullback_ofArrows_mem_smallEtaleTopology`,
  `AlgebraicGeometry.Scheme.Etale.isIso_of_forall_isIso_restrictSheaf`: étale covering and locality
  of isomorphisms.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé III (continuous and cocontinuous
  functors) and Exposé IX, §2 (locally constant sheaves).
* The Stacks Project, [Tag 03Q4](https://stacks.math.columbia.edu/tag/03Q4), localization of the
  small étale site.
-/

public section

universe w u u' v'

open CategoryTheory Limits Opposite AlgebraicGeometry Scheme

namespace AlgebraicGeometry.Scheme

section SmallEtaleMap

variable {S T : Scheme.{u}} (p : T ⟶ S) [Etale p]

/-- Post-composition with an étale morphism `p : T ⟶ S`, as a functor `T.Etale ⥤ S.Etale`. -/
-- `Scheme.Etale` is a `protected def` of `MorphismProperty.Over @Etale ⊤`, so typing the functor as
-- `T.Etale ⥤ S.Etale` allows typeclass synthesis to use `Category T.Etale`. Exposed so that
-- characteristic `rfl` lemmas about `smallEtaleMap` and `restrictSheaf` typecheck in consumers.
@[expose]
def Hom.smallEtaleMap : T.Etale ⥤ S.Etale :=
  MorphismProperty.Over.map ⊤ (inferInstance : Etale p)

/-- `p.smallEtaleMap` preserves the underlying scheme of an étale `T`-scheme. -/
@[simp]
lemma Hom.smallEtaleMap_obj_left (V : T.Etale) : (p.smallEtaleMap.obj V).left = V.left :=
  rfl

/-- `p.smallEtaleMap` post-composes the structure morphism with `p`. -/
@[simp]
lemma Hom.smallEtaleMap_obj_hom (V : T.Etale) : (p.smallEtaleMap.obj V).hom = V.hom ≫ p :=
  rfl

/-- `p.smallEtaleMap` preserves the underlying scheme morphism. -/
@[simp]
lemma Hom.smallEtaleMap_map_left {V W : T.Etale} (f : V ⟶ W) :
    (p.smallEtaleMap.map f).left = f.left :=
  rfl

/-- Equal étale morphisms induce naturally isomorphic post-composition functors on small étale
sites. -/
-- Specializes `MorphismProperty.Over.mapCongr` to `p.smallEtaleMap ≅ q.smallEtaleMap`, since
-- `Scheme.Etale` is a `protected def` and `Category (MorphismProperty.Over @Etale ⊤ T)` is not
-- synthesized directly.
def Hom.smallEtaleMapCongr {p q : T ⟶ S} [Etale p] [Etale q] (h : p = q) :
    p.smallEtaleMap ≅ q.smallEtaleMap :=
  MorphismProperty.Over.mapCongr ⊤ h (inferInstance : Etale p)

/-- On underlying schemes, `smallEtaleMapCongr h` is the identity. -/
@[simp]
lemma Hom.smallEtaleMapCongr_hom_app_left {p q : T ⟶ S} [Etale p] [Etale q] (h : p = q)
    (V : T.Etale) :
    ((Hom.smallEtaleMapCongr h).hom.app V).left = 𝟙 V.left := by
  rfl

/-- On underlying schemes, the inverse of `smallEtaleMapCongr h` is the identity. -/
@[simp]
lemma Hom.smallEtaleMapCongr_inv_app_left {p q : T ⟶ S} [Etale p] [Etale q] (h : p = q)
    (V : T.Etale) :
    ((Hom.smallEtaleMapCongr h).inv.app V).left = 𝟙 V.left := by
  rfl

/-- Post-composition along a composite of étale morphisms is naturally isomorphic to the composite
of the post-composition functors. -/
def Hom.smallEtaleMapComp {R : Scheme.{u}} (q : R ⟶ T) [Etale q] (p : T ⟶ S) [Etale p] :
    q.smallEtaleMap ⋙ p.smallEtaleMap ≅ (q ≫ p).smallEtaleMap :=
  (MorphismProperty.Over.mapComp ⊤ (inferInstance : Etale q) (inferInstance : Etale p)).symm

/-- On underlying schemes, `smallEtaleMapComp q p` is the identity. -/
@[simp]
lemma Hom.smallEtaleMapComp_hom_app_left {R : Scheme.{u}} (q : R ⟶ T) [Etale q] (p : T ⟶ S)
    [Etale p] (V : R.Etale) :
    ((Hom.smallEtaleMapComp q p).hom.app V).left = 𝟙 V.left := by
  rfl

/-- On underlying schemes, the inverse of `smallEtaleMapComp q p` is the identity. -/
@[simp]
lemma Hom.smallEtaleMapComp_inv_app_left {R : Scheme.{u}} (q : R ⟶ T) [Etale q] (p : T ⟶ S)
    [Etale p] (V : R.Etale) :
    ((Hom.smallEtaleMapComp q p).inv.app V).left = 𝟙 V.left := by
  rfl

end SmallEtaleMap

namespace Etale

section OverEquiv

variable {S T : Scheme.{u}} (U : S.Etale) (p : T ⟶ S) [Etale p]
  (eU : U.left ≅ T) (hp : eU.hom ≫ p = U.hom)

/-- Equivalence between `T.Etale` and `Over U` for any `U : S.Etale` identified with `p : T ⟶ S`
via an isomorphism `eU : U.left ≅ T` with `eU.hom ≫ p = U.hom`. -/
-- Exposed so that the dependent types in the `overEquiv_*` characteristic lemmas below typecheck.
@[expose]
noncomputable def overEquiv : T.Etale ≌ Over U where
  functor :=
    { obj V := Over.mk (Y := p.smallEtaleMap.obj V)
        (MorphismProperty.Over.homMk (V.hom ≫ eU.inv) (by
          simpa [Category.assoc] using congrArg (V.hom ≫ ·) (eU.inv_comp_eq.mpr hp.symm)))
      map {V W} f := Over.homMk (p.smallEtaleMap.map f) (by
        apply MorphismProperty.Over.Hom.ext
        exact (Category.assoc f.left W.hom eU.inv).symm.trans
          (congrArg (· ≫ eU.inv) (MorphismProperty.Over.w f))) }
  inverse :=
    { obj W :=
        have : Etale (W.hom.left ≫ eU.hom) := inferInstance
        Etale.mk (W.hom.left ≫ eU.hom)
      map {W₁ W₂} g := MorphismProperty.Over.homMk g.left.left
        ((Category.assoc g.left.left W₂.hom.left eU.hom).symm.trans
          (congrArg (· ≫ eU.hom) (congrArg (fun k : W₁.left ⟶ U ↦ k.left) (Over.w g)))) }
  unitIso := NatIso.ofComponents
    (fun V ↦ MorphismProperty.Over.isoMk (Iso.refl V.left)
      ((Category.id_comp _).trans ((Category.assoc V.hom eU.inv eU.hom).trans (by simp))))
    (fun f ↦ by
      apply MorphismProperty.Over.Hom.ext
      exact (Category.comp_id f.left).trans (Category.id_comp f.left).symm)
  counitIso := NatIso.ofComponents
    (fun W ↦ Over.isoMk
      (MorphismProperty.Over.isoMk (Iso.refl W.left.left)
        ((Category.id_comp W.left.hom).trans
          ((MorphismProperty.Over.w W.hom).symm.trans
            ((congrArg (W.hom.left ≫ ·) hp.symm).trans
              (Category.assoc W.hom.left eU.hom p).symm))))
      (by
        apply MorphismProperty.Over.Hom.ext
        exact (Category.id_comp W.hom.left).trans
          ((Category.assoc W.hom.left eU.hom eU.inv).trans (by simp)).symm))
    (fun g ↦ by
      apply Over.OverMorphism.ext; apply MorphismProperty.Over.Hom.ext
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  functor_unitIso_comp V := by
    apply Over.OverMorphism.ext; apply MorphismProperty.Over.Hom.ext
    exact Category.id_comp _

/-- The underlying `S.Etale` object of `(overEquiv U p eU hp).functor.obj V` is
`p.smallEtaleMap.obj V`. -/
@[simp]
lemma overEquiv_functor_obj_left (V : T.Etale) :
    ((overEquiv U p eU hp).functor.obj V).left = p.smallEtaleMap.obj V := by
  rfl

/-- The structure morphism of `(overEquiv U p eU hp).functor.obj V` over `U` is
`V.hom ≫ eU.inv`. -/
@[simp]
lemma overEquiv_functor_obj_hom_left (V : T.Etale) :
    ((overEquiv U p eU hp).functor.obj V).hom.left = V.hom ≫ eU.inv := by
  rfl

/-- On underlying `S.Etale` morphisms, `(overEquiv U p eU hp).functor.map f` is
`p.smallEtaleMap.map f`. -/
@[simp]
lemma overEquiv_functor_map_left {V W : T.Etale} (f : V ⟶ W) :
    ((overEquiv U p eU hp).functor.map f).left = p.smallEtaleMap.map f := by
  rfl

/-- The underlying scheme of `(overEquiv U p eU hp).inverse.obj W` is `W.left.left`. -/
@[simp]
lemma overEquiv_inverse_obj_left (W : Over U) :
    ((overEquiv U p eU hp).inverse.obj W).left = W.left.left := by
  rfl

/-- The structure morphism of `(overEquiv U p eU hp).inverse.obj W` over `T` is
`W.hom.left ≫ eU.hom`. -/
@[simp]
lemma overEquiv_inverse_obj_hom (W : Over U) :
    ((overEquiv U p eU hp).inverse.obj W).hom = W.hom.left ≫ eU.hom := by
  rfl

/-- On underlying scheme morphisms, `(overEquiv U p eU hp).inverse.map g` is `g.left.left`. -/
@[simp]
lemma overEquiv_inverse_map_left {W₁ W₂ : Over U} (g : W₁ ⟶ W₂) :
    ((overEquiv U p eU hp).inverse.map g).left = g.left.left := by
  rfl

/-- Composing `(overEquiv U p eU hp).functor` with `Over.forget U` recovers `p.smallEtaleMap`. -/
noncomputable def overEquivFunctorCompForgetIso :
    (overEquiv U p eU hp).functor ⋙ Over.forget U ≅ p.smallEtaleMap :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _)

/-- The inverse of `overEquiv` is a dense subsite for `(smallEtaleTopology S).over U` and
`smallEtaleTopology T`. -/
instance isDenseSubsite_overEquiv_inverse :
    (overEquiv U p eU hp).inverse.IsDenseSubsite
      ((smallEtaleTopology S).over U) (smallEtaleTopology T) where
  functorPushforward_mem_iff {W R} := by
    let e := overEquiv U p eU hp
    have hpush : R.functorPushforward e.inverse =
        Sieve.ofArrows (fun g : Σ Y : Over U, {f : Y ⟶ W // R f} ↦ e.inverse.obj g.1)
          (fun g ↦ e.inverse.map g.2.1) := by
      ext Z h
      rw [Sieve.mem_ofArrows_iff]
      constructor
      · rintro ⟨W', g, k, hg, rfl⟩
        exact ⟨⟨W', g, hg⟩, k, rfl⟩
      · rintro ⟨⟨W', g, hg⟩, k, rfl⟩
        exact ⟨W', g, k, hg, rfl⟩
    rw [hpush, Scheme.ofArrows_mem_smallEtaleTopology_iff, GrothendieckTopology.mem_over_iff]
    have hR : Sieve.overEquiv W R =
        Sieve.ofArrows (fun g : Σ Y : Over U, {f : Y ⟶ W // R f} ↦ g.1.left)
          (fun g ↦ g.2.1.left) := by
      ext Z h
      rw [Sieve.mem_ofArrows_iff]
      constructor
      · intro hh
        have hh' : R (Over.homMk h rfl : Over.mk (h ≫ W.hom) ⟶ W) :=
          (Sieve.overEquiv_iff R h).mp hh
        exact ⟨⟨Over.mk (h ≫ W.hom), Over.homMk h rfl, hh'⟩, 𝟙 Z, by simp⟩
      · rintro ⟨⟨W', g, hg⟩, k, rfl⟩
        let hk : Over.mk ((k ≫ g.left) ≫ W.hom) ⟶ W' := Over.homMk k (by simp [Over.w g])
        have hcomp : hk ≫ g = Over.homMk (k ≫ g.left) rfl := by
          ext; simp [hk]
        exact (Sieve.overEquiv_iff R (k ≫ g.left)).mpr (hcomp ▸ R.downward_closed hg hk)
    rw [hR, Scheme.ofArrows_mem_smallEtaleTopology_iff]
    simp only [e, overEquiv_inverse_map_left]
    exact Iff.rfl

end OverEquiv

section Restrict

variable {S T : Scheme.{u}} (p : T ⟶ S) [Etale p]

/-- Post-composition `p.smallEtaleMap : T.Etale ⥤ S.Etale` is continuous for the small étale
topologies. -/
instance isContinuous_smallEtaleMap :
    p.smallEtaleMap.IsContinuous (smallEtaleTopology T) (smallEtaleTopology S) := by
  let eIso : (Etale.mk p).left ≅ T :=
    eqToIso (MorphismProperty.Over.mk_left (P := @Etale) ⊤ p inferInstance)
  have hp : eIso.hom ≫ p = (Etale.mk p).hom := Category.id_comp p
  exact Functor.isContinuous_comp'
    (overEquivFunctorCompForgetIso (Etale.mk p) p eIso hp)
    (smallEtaleTopology T) ((smallEtaleTopology S).over (Etale.mk p)) (smallEtaleTopology S)

/-- Post-composition `p.smallEtaleMap : T.Etale ⥤ S.Etale` is cocontinuous for the small étale
topologies. -/
instance isCocontinuous_smallEtaleMap :
    p.smallEtaleMap.IsCocontinuous (smallEtaleTopology T) (smallEtaleTopology S) := by
  let eIso : (Etale.mk p).left ≅ T :=
    eqToIso (MorphismProperty.Over.mk_left (P := @Etale) ⊤ p inferInstance)
  have hp : eIso.hom ≫ p = (Etale.mk p).hom := Category.id_comp p
  have : ((overEquiv (Etale.mk p) p eIso hp).functor ⋙
      Over.forget (Etale.mk p)).IsCocontinuous (smallEtaleTopology T) (smallEtaleTopology S) :=
    isCocontinuous_comp (overEquiv (Etale.mk p) p eIso hp).functor
      (Over.forget (Etale.mk p)) (smallEtaleTopology T)
      ((smallEtaleTopology S).over (Etale.mk p))
  exact Functor.IsCocontinuous.of_iso
    (overEquivFunctorCompForgetIso (Etale.mk p) p eIso hp)

/-- Restriction of sheaves on the small étale site along an étale morphism `p : T ⟶ S`, given by
precomposition with `p.smallEtaleMap : T.Etale ⥤ S.Etale`. -/
-- Exposed so that `restrictSheaf_obj_obj`, `restrictSheaf_obj_map`, and `restrictSheaf_map_app`
-- are well-typed `rfl` lemmas in downstream modules.
@[expose]
noncomputable def restrictSheaf {A : Type u'} [Category.{v'} A] (p : T ⟶ S) [Etale p] :
    Sheaf (smallEtaleTopology S) A ⥤ Sheaf (smallEtaleTopology T) A :=
  p.smallEtaleMap.sheafPushforwardContinuous A (smallEtaleTopology T) (smallEtaleTopology S)

/-- Sections of `(restrictSheaf p).obj F` over `V : T.Etale` are sections of `F` over
`p.smallEtaleMap.obj V`. -/
@[simp]
lemma restrictSheaf_obj_obj {A : Type u'} [Category.{v'} A] (F : Sheaf (smallEtaleTopology S) A)
    (V : T.Etale) :
    ((restrictSheaf p).obj F).obj.obj (op V) = F.obj.obj (op (p.smallEtaleMap.obj V)) :=
  rfl

/-- Restriction maps of `(restrictSheaf p).obj F` are restriction maps of `F` along
`p.smallEtaleMap`. -/
@[simp]
lemma restrictSheaf_obj_map {A : Type u'} [Category.{v'} A] (F : Sheaf (smallEtaleTopology S) A)
    {V W : T.Etale} (f : V ⟶ W) :
    ((restrictSheaf p).obj F).obj.map f.op = F.obj.map (p.smallEtaleMap.map f).op :=
  rfl

/-- On components, `(restrictSheaf p).map φ` evaluates `φ` at `p.smallEtaleMap.obj V`. -/
@[simp]
lemma restrictSheaf_map_app {A : Type u'} [Category.{v'} A] {F G : Sheaf (smallEtaleTopology S) A}
    (φ : F ⟶ G) (V : T.Etale) :
    ((restrictSheaf p).map φ).hom.app (op V) = φ.hom.app (op (p.smallEtaleMap.obj V)) :=
  rfl

/-- Identification of `restrictSheaf p` with localization `(smallEtaleTopology S).overPullback A U`
transported along `overEquiv U p eU hp`. -/
noncomputable def restrictSheafOverIso {A : Type u'} [Category.{v'} A]
    (U : S.Etale) (p : T ⟶ S) [Etale p] (eU : U.left ≅ T) (hp : eU.hom ≫ p = U.hom) :
    (smallEtaleTopology S).overPullback A U ⋙
        ((overEquiv U p eU hp).sheafCongr
          (smallEtaleTopology T) ((smallEtaleTopology S).over U) A).inverse ≅
      restrictSheaf (A := A) p :=
  Functor.sheafPushforwardContinuousComp'
    (overEquivFunctorCompForgetIso U p eU hp) A
    (smallEtaleTopology T) ((smallEtaleTopology S).over U) (smallEtaleTopology S)

/-- Equal étale morphisms induce naturally isomorphic restriction functors. -/
noncomputable def restrictSheafEqIso {A : Type u'} [Category.{v'} A]
    {p q : T ⟶ S} [Etale p] [Etale q] (h : p = q) :
    restrictSheaf (A := A) p ≅ restrictSheaf (A := A) q :=
  Functor.sheafPushforwardContinuousIso (Hom.smallEtaleMapCongr h) A
    (smallEtaleTopology T) (smallEtaleTopology S)

/-- Component formula for `restrictSheafEqIso`. -/
@[simp]
lemma restrictSheafEqIso_hom_app_hom_app {A : Type u'} [Category.{v'} A]
    {p q : T ⟶ S} [Etale p] [Etale q] (h : p = q) (F : Sheaf (smallEtaleTopology S) A)
    (V : T.Etale) :
    ((restrictSheafEqIso (A := A) h).hom.app F).hom.app (op V) =
      F.obj.map ((Hom.smallEtaleMapCongr h).inv.app V).op := by
  rfl

/-- Inverse component formula for `restrictSheafEqIso`. -/
@[simp]
lemma restrictSheafEqIso_inv_app_hom_app {A : Type u'} [Category.{v'} A]
    {p q : T ⟶ S} [Etale p] [Etale q] (h : p = q) (F : Sheaf (smallEtaleTopology S) A)
    (V : T.Etale) :
    ((restrictSheafEqIso (A := A) h).inv.app F).hom.app (op V) =
      F.obj.map ((Hom.smallEtaleMapCongr h).hom.app V).op := by
  rfl

/-- Successive restrictions along étale morphisms `q : R ⟶ T` and `p : T ⟶ S` agree with
restriction along `q ≫ p`. -/
noncomputable def restrictSheafCompIso {A : Type u'} [Category.{v'} A]
    {R : Scheme.{u}} (q : R ⟶ T) [Etale q] (p : T ⟶ S) [Etale p] :
    restrictSheaf (A := A) p ⋙ restrictSheaf (A := A) q ≅ restrictSheaf (A := A) (q ≫ p) :=
  Functor.sheafPushforwardContinuousComp' (Hom.smallEtaleMapComp q p) A
    (smallEtaleTopology R) (smallEtaleTopology T) (smallEtaleTopology S)

/-- Component formula for `restrictSheafCompIso`. -/
@[simp]
lemma restrictSheafCompIso_hom_app_hom_app {A : Type u'} [Category.{v'} A]
    {R : Scheme.{u}} (q : R ⟶ T) [Etale q] (p : T ⟶ S) [Etale p]
    (F : Sheaf (smallEtaleTopology S) A) (V : R.Etale) :
    ((restrictSheafCompIso (A := A) q p).hom.app F).hom.app (op V) =
      F.obj.map ((Hom.smallEtaleMapComp q p).inv.app V).op := by
  exact Category.id_comp _

/-- Inverse component formula for `restrictSheafCompIso`. -/
@[simp]
lemma restrictSheafCompIso_inv_app_hom_app {A : Type u'} [Category.{v'} A]
    {R : Scheme.{u}} (q : R ⟶ T) [Etale q] (p : T ⟶ S) [Etale p]
    (F : Sheaf (smallEtaleTopology S) A) (V : R.Etale) :
    ((restrictSheafCompIso (A := A) q p).inv.app F).hom.app (op V) =
      F.obj.map ((Hom.smallEtaleMapComp q p).hom.app V).op := by
  exact Category.comp_id _

/-- Restricting the constant sheaf functor along an étale morphism `p : T ⟶ S` yields the constant
sheaf functor on `T`, for any coefficient category admitting weak sheafification. -/
noncomputable def constantSheafCompRestrictSheafIso {A : Type u'} [Category.{v'} A]
    [HasWeakSheafify (smallEtaleTopology S) A] [HasWeakSheafify (smallEtaleTopology T) A]
    (p : T ⟶ S) [Etale p] :
    constantSheaf (smallEtaleTopology S) A ⋙ restrictSheaf p ≅
      constantSheaf (smallEtaleTopology T) A := by
  let R : S.Etale ⥤ T.Etale := MorphismProperty.Over.pullback @Etale ⊤ p
  let adj : p.smallEtaleMap ⊣ R :=
    MorphismProperty.Over.mapPullbackAdj @Etale ⊤ p (inferInstance : Etale p) trivial
  have : R.IsContinuous (smallEtaleTopology S) (smallEtaleTopology T) :=
    adj.isContinuous_of_isCocontinuous (smallEtaleTopology T) (smallEtaleTopology S)
  have : R.IsRightAdjoint := adj.isRightAdjoint
  let adjSheaf : restrictSheaf (A := A) p ⊣
      R.sheafPushforwardContinuous A (smallEtaleTopology S) (smallEtaleTopology T) :=
    adj.sheafPushforwardContinuous (smallEtaleTopology T) (smallEtaleTopology S)
  let hterm : IsTerminal (R.obj (Etale.mk (𝟙 S))) :=
    (Etale.mkIdTerminal S).isTerminalObj R
  let adj₁ := (constantSheafAdj (smallEtaleTopology S) A (Etale.mkIdTerminal S)).comp adjSheaf
  let adj₂ := constantSheafAdj (smallEtaleTopology T) A hterm
  exact adj₁.leftAdjointUniq adj₂

/-- Restricting a constant sheaf with value `M` along an étale morphism `p : T ⟶ S` yields the
constant sheaf with value `M` on `T`. -/
noncomputable def restrictSheafConstantSheafIso {A : Type u'} [Category.{v'} A]
    [HasWeakSheafify (smallEtaleTopology S) A] [HasWeakSheafify (smallEtaleTopology T) A]
    (p : T ⟶ S) [Etale p] (M : A) :
    (restrictSheaf p).obj ((constantSheaf (smallEtaleTopology S) A).obj M) ≅
      (constantSheaf (smallEtaleTopology T) A).obj M :=
  (constantSheafCompRestrictSheafIso p).app M

/-- Structure morphism compatibility for the canonical identification
`(p.smallEtaleMap.obj Y).left ≅ Y.left`. -/
private lemma smallEtaleMap_obj_left_eqToIso_hom_comp (p : T ⟶ S) [Etale p] (Y : T.Etale) :
    (eqToIso (p.smallEtaleMap_obj_left Y)).hom ≫ (Y.hom ≫ p) = (p.smallEtaleMap.obj Y).hom :=
  Category.id_comp (Y.hom ≫ p)

/-- Restricting a sheaf `F` along `p : T ⟶ S` and then localizing at `Y : T.Etale` matches
localizing `F` at `p.smallEtaleMap.obj Y`, once both over-sites are transported to `Y.left.Etale`.
-/
private noncomputable def restrictSheafOverCompatIso {A : Type u'} [Category.{v'} A]
    (p : T ⟶ S) [Etale p] (Y : T.Etale) (F : Sheaf (smallEtaleTopology S) A) :
    ((overEquiv Y Y.hom (Iso.refl Y.left) (Category.id_comp Y.hom)).sheafCongr
        (smallEtaleTopology Y.left) ((smallEtaleTopology T).over Y) A).inverse.obj
        (((restrictSheaf p).obj F).over Y) ≅
      ((overEquiv (p.smallEtaleMap.obj Y) (Y.hom ≫ p)
          (eqToIso (p.smallEtaleMap_obj_left Y))
          (smallEtaleMap_obj_left_eqToIso_hom_comp p Y)).sheafCongr
        (smallEtaleTopology Y.left)
        ((smallEtaleTopology S).over (p.smallEtaleMap.obj Y)) A).inverse.obj
        (F.over (p.smallEtaleMap.obj Y)) :=
  (restrictSheafOverIso Y Y.hom (Iso.refl Y.left) (Category.id_comp Y.hom)).app
      ((restrictSheaf p).obj F) ≪≫
    (restrictSheafCompIso Y.hom p).app F ≪≫
    ((restrictSheafOverIso (p.smallEtaleMap.obj Y) (Y.hom ≫ p)
      (eqToIso (p.smallEtaleMap_obj_left Y))
      (smallEtaleMap_obj_left_eqToIso_hom_comp p Y)).app F).symm

/-- Restriction along an étale morphism preserves locally constant sheaves with values in any
object property `P`. -/
theorem isLocallyConstantIn_restrictSheaf {A : Type u'} [Category.{v'} A]
    [HasWeakSheafify (smallEtaleTopology S) A] [HasWeakSheafify (smallEtaleTopology T) A]
    {P : ObjectProperty A} {F : Sheaf (smallEtaleTopology S) A}
    (hF : F.IsLocallyConstantIn (smallEtaleTopology S) P) :
    ((restrictSheaf p).obj F).IsLocallyConstantIn (smallEtaleTopology T) P := by
  rw [Sheaf.isLocallyConstantIn_iff] at hF ⊢
  intro X
  have hmem : (F.locallyConstantSieve P (p.smallEtaleMap.obj X)).functorPullback p.smallEtaleMap ∈
      smallEtaleTopology T X :=
    p.smallEtaleMap.cover_lift (smallEtaleTopology T) (smallEtaleTopology S)
      (hF (p.smallEtaleMap.obj X))
  refine (smallEtaleTopology T).superset_covering ?_ hmem
  intro Y f hf
  obtain ⟨M, hM, ⟨e⟩⟩ := (Sheaf.locallyConstantSieve_apply P F (p.smallEtaleMap.map f)).mp hf
  rw [Sheaf.locallyConstantSieve_apply]
  refine ⟨M, hM, ⟨?_⟩⟩
  let eqT := (overEquiv Y Y.hom (Iso.refl Y.left) (Category.id_comp Y.hom)).sheafCongr
    (smallEtaleTopology Y.left) ((smallEtaleTopology T).over Y) A
  let eqS := (overEquiv (p.smallEtaleMap.obj Y) (Y.hom ≫ p)
    (eqToIso (p.smallEtaleMap_obj_left Y))
    (smallEtaleMap_obj_left_eqToIso_hom_comp p Y)).sheafCongr
    (smallEtaleTopology Y.left) ((smallEtaleTopology S).over (p.smallEtaleMap.obj Y)) A
  have hC : eqS.inverse.obj (((constantSheaf (smallEtaleTopology S) A).obj M).over
        (p.smallEtaleMap.obj Y)) ≅
      eqT.inverse.obj (((constantSheaf (smallEtaleTopology T) A).obj M).over Y) :=
    (restrictSheafOverCompatIso p Y ((constantSheaf (smallEtaleTopology S) A).obj M)).symm ≪≫
      eqT.inverse.mapIso
        (((smallEtaleTopology T).overPullback A Y).mapIso (restrictSheafConstantSheafIso p M))
  exact (eqT.counitIso.app _).symm ≪≫
    eqT.functor.mapIso (restrictSheafOverCompatIso p Y F ≪≫ eqS.inverse.mapIso e ≪≫ hC) ≪≫
    eqT.counitIso.app _

end Restrict

section Locality

/-- A sheaf of types on the small étale site of `S` satisfies the sheaf condition for any single
morphism `f : U ⟶ V` in `S.Etale` whose underlying morphism of schemes is surjective. -/
theorem isSheafFor_singleton_of_surjective {S : Scheme.{u}}
    (F : Sheaf (smallEtaleTopology S) (Type w))
    {U V : S.Etale} (f : U ⟶ V) [Surjective f.left] :
    Presieve.IsSheafFor F.obj (.singleton f) := by
  rw [Presieve.isSheafFor_iff_generate]
  have hmem : Sieve.generate (.singleton f) ∈ smallEtaleTopology S V := by
    rw [← Presieve.ofArrows_pUnit.{w} f]
    -- `Sieve.generate (Presieve.ofArrows _ _)` is definitionally `Sieve.ofArrows _ _`.
    change Sieve.ofArrows (fun _ : PUnit.{w + 1} ↦ U) (fun _ ↦ f) ∈ smallEtaleTopology S V
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    simp [Set.range_eq_univ.mpr f.left.surjective, Set.iUnion_const]
  exact (isSheaf_iff_isSheaf_of_type _ _).mp F.property _ hmem

/-- The pullback projection `U ×_S T ⟶ U` in `S.Etale`, where `U ×_S T` is viewed over `S` via
`p.smallEtaleMap`. -/
noncomputable def pullbackCover {S T : Scheme.{u}} (p : T ⟶ S) [Etale p] (U : S.Etale) :
    p.smallEtaleMap.obj (Etale.mk (pullback.snd U.hom p)) ⟶ U :=
  MorphismProperty.Over.homMk (pullback.fst U.hom p) (by
    simp only [Hom.smallEtaleMap_obj_hom]
    exact pullback.condition)

/-- On underlying schemes, `pullbackCover p U` is the first projection `pullback.fst U.hom p`. -/
@[simp]
lemma pullbackCover_left {S T : Scheme.{u}} (p : T ⟶ S) [Etale p] (U : S.Etale) :
    (pullbackCover p U).left = pullback.fst U.hom p := by
  rfl

/-- Pulling back a jointly surjective family of étale `S`-schemes along any `U : S.Etale` gives a
covering sieve of `U` in the small étale topology. -/
theorem pullback_ofArrows_mem_smallEtaleTopology {S : Scheme.{u}} {ι : Type*}
    {T : ι → Scheme.{u}} (p : ∀ i, T i ⟶ S) [∀ i, Etale (p i)]
    (hsurj : ⋃ i, Set.range (p i) = .univ) (U : S.Etale) :
    Sieve.ofArrows
        (fun i ↦ (p i).smallEtaleMap.obj (Etale.mk (pullback.snd U.hom (p i))))
        (fun i ↦ pullbackCover (p i) U) ∈
      smallEtaleTopology S U := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext u
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true, pullbackCover_left]
  obtain ⟨i, t, ht⟩ := Set.mem_iUnion.mp (hsurj.symm ▸ Set.mem_univ (U.hom u))
  obtain ⟨w, hw, _⟩ := Scheme.Pullback.exists_preimage_pullback u t ht.symm
  exact ⟨i, w, hw⟩

/-- If `φ : G ⟶ F` becomes an isomorphism after restriction along `p`, then its component on
`p.smallEtaleMap.obj (Etale.mk (pullback.snd U.hom p))` is bijective. -/
private lemma bijective_app_of_isIso_restrictSheaf {S T : Scheme.{u}} (p : T ⟶ S) [Etale p]
    {G F : Sheaf (smallEtaleTopology S) (Type w)} (φ : G ⟶ F) [IsIso ((restrictSheaf p).map φ)]
    (U : S.Etale) :
    Function.Bijective
      (φ.hom.app (op (p.smallEtaleMap.obj (Etale.mk (pullback.snd U.hom p))))) := by
  have hnat : IsIso (((restrictSheaf p).map φ).hom) :=
    (sheafToPresheaf (smallEtaleTopology T) (Type w)).map_isIso ((restrictSheaf p).map φ)
  have happ : IsIso (((restrictSheaf p).map φ).hom.app (op (Etale.mk (pullback.snd U.hom p)))) :=
    (NatTrans.isIso_iff_isIso_app _).mp hnat _
  rw [restrictSheaf_map_app] at happ
  exact (isIso_iff_bijective _).mp happ

/-- A sheaf of types satisfies the sheaf condition for the pulled-back étale cover of `U`. -/
private lemma isSheafFor_pullbackCover {S : Scheme.{u}} {ι : Type*}
    {T : ι → Scheme.{u}} (p : ∀ i, T i ⟶ S) [∀ i, Etale (p i)]
    (hsurj : ⋃ i, Set.range (p i) = .univ)
    (F : Sheaf (smallEtaleTopology S) (Type w)) (U : S.Etale) :
    Presieve.IsSheafFor F.obj
      (Presieve.ofArrows
        (fun i ↦ (p i).smallEtaleMap.obj (Etale.mk (pullback.snd U.hom (p i))))
        (fun i ↦ pullbackCover (p i) U)) :=
  (Presieve.isSheafFor_iff_generate _).mpr <|
    (isSheaf_iff_isSheaf_of_type _ _).mp F.property _
      (pullback_ofArrows_mem_smallEtaleTopology p hsurj U)

/-- A morphism of étale sheaves of types whose restrictions along a jointly surjective étale
family are isomorphisms is injective on every section set. -/
private lemma app_injective_of_forall_isIso_restrictSheaf {S : Scheme.{u}} {ι : Type*}
    {T : ι → Scheme.{u}} (p : ∀ i, T i ⟶ S) [∀ i, Etale (p i)]
    (hsurj : ⋃ i, Set.range (p i) = .univ)
    {G F : Sheaf (smallEtaleTopology S) (Type w)} (φ : G ⟶ F)
    (hiso : ∀ i, IsIso ((restrictSheaf (p i)).map φ)) (U : S.Etale) :
    Function.Injective (φ.hom.app (op U)) := by
  have hG := (Presieve.isSheafFor_arrows_iff G.obj (fun i ↦ pullbackCover (p i) U)).mp
    (isSheafFor_pullbackCover p hsurj G U)
  intro a b hab
  refine (hG (fun i ↦ G.obj.map (pullbackCover (p i) U).op a)
    (Presieve.Arrows.toCompatible G.obj (fun i ↦ pullbackCover (p i) U) a).2).unique
    (fun _ ↦ rfl) fun i ↦ ?_
  have : IsIso ((restrictSheaf (p i)).map φ) := hiso i
  refine (bijective_app_of_isIso_restrictSheaf (p i) φ U).1 ?_
  have ha := ConcreteCategory.congr_hom (φ.hom.naturality (pullbackCover (p i) U).op) a
  have hb := ConcreteCategory.congr_hom (φ.hom.naturality (pullbackCover (p i) U).op) b
  simp only [types_comp_apply] at ha hb
  exact hb.trans ((congrArg (F.obj.map (pullbackCover (p i) U).op) hab.symm).trans ha.symm)

/-- A morphism of étale sheaves of types is an isomorphism if its restrictions along a jointly
surjective étale family are isomorphisms. -/
private lemma isIso_of_forall_isIso_restrictSheaf_type {S : Scheme.{u}} {ι : Type*}
    {T : ι → Scheme.{u}} (p : ∀ i, T i ⟶ S) [∀ i, Etale (p i)]
    (hsurj : ⋃ i, Set.range (p i) = .univ)
    {G F : Sheaf (smallEtaleTopology S) (Type w)} (φ : G ⟶ F)
    (hiso : ∀ i, IsIso ((restrictSheaf (p i)).map φ)) :
    IsIso φ := by
  have hval : IsIso ((sheafToPresheaf (smallEtaleTopology S) (Type w)).map φ) := by
    refine (NatTrans.isIso_iff_isIso_app φ.hom).mpr fun ⟨U⟩ ↦ (isIso_iff_bijective _).mpr
      ⟨app_injective_of_forall_isIso_restrictSheaf p hsurj φ hiso U, fun y ↦ ?_⟩
    have hbij : ∀ i, Function.Bijective
        (φ.hom.app (op ((p i).smallEtaleMap.obj (Etale.mk (pullback.snd U.hom (p i)))))) :=
      fun i ↦ by
        have : IsIso ((restrictSheaf (p i)).map φ) := hiso i
        exact bijective_app_of_isIso_restrictSheaf (p i) φ U
    choose x hx using fun i ↦ (hbij i).2 (F.obj.map (pullbackCover (p i) U).op y)
    have hG := (Presieve.isSheafFor_arrows_iff G.obj (fun i ↦ pullbackCover (p i) U)).mp
      (isSheafFor_pullbackCover p hsurj G U)
    have hF := (Presieve.isSheafFor_arrows_iff F.obj (fun i ↦ pullbackCover (p i) U)).mp
      (isSheafFor_pullbackCover p hsurj F U)
    -- The local preimages `x i` agree on overlaps because `φ` is injective on every section set.
    have hcompat : Presieve.Arrows.Compatible G.obj (fun i ↦ pullbackCover (p i) U) x := by
      intro i j W g₁ g₂ hcomm
      apply app_injective_of_forall_isIso_restrictSheaf p hsurj φ hiso W
      have h1 := ConcreteCategory.congr_hom (φ.hom.naturality g₁.op) (x i)
      have h2 := ConcreteCategory.congr_hom (φ.hom.naturality g₂.op) (x j)
      simp only [types_comp_apply] at h1 h2
      rw [h1, h2, hx i, hx j, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
        ← op_comp, ← op_comp, hcomm]
    obtain ⟨t, ht, -⟩ := hG x hcompat
    refine ⟨t, (hF (fun i ↦ F.obj.map (pullbackCover (p i) U).op y)
      (Presieve.Arrows.toCompatible F.obj (fun i ↦ pullbackCover (p i) U) y).2).unique
      (fun i ↦ ?_) (fun _ ↦ rfl)⟩
    have hnat := ConcreteCategory.congr_hom (φ.hom.naturality (pullbackCover (p i) U).op) t
    simp only [types_comp_apply] at hnat
    exact hnat.symm.trans ((congrArg (φ.hom.app _) (ht i)).trans (hx i))
  exact isIso_of_reflects_iso φ (sheafToPresheaf (smallEtaleTopology S) (Type w))

/-- **Étale locality of isomorphisms.** A morphism `φ : G ⟶ F` of sheaves on the small étale site
of `S` (with values in any category `A`) is an isomorphism if its restrictions along a jointly
surjective family of étale morphisms `p i : T i ⟶ S` are isomorphisms. -/
theorem isIso_of_forall_isIso_restrictSheaf {S : Scheme.{u}} {A : Type u'} [Category.{v'} A]
    {ι : Type*} {T : ι → Scheme.{u}} (p : ∀ i, T i ⟶ S) [∀ i, Etale (p i)]
    (hsurj : ⋃ i, Set.range (p i) = .univ)
    {G F : Sheaf (smallEtaleTopology S) A} (φ : G ⟶ F)
    (hiso : ∀ i, IsIso ((restrictSheaf (p i)).map φ)) :
    IsIso φ := by
  have hval : IsIso ((sheafToPresheaf (smallEtaleTopology S) A).map φ) := by
    refine (NatTrans.isIso_iff_isIso_app φ.hom).mpr fun ⟨U⟩ ↦ ?_
    -- By Yoneda in `A`, it suffices to check `(coyoneda.obj (op X)).map (φ.hom.app (op U))` for
    -- every `X : A`, reducing to the `Type v'` case on `Hom(X, -)`.
    have hyon : IsIso (yoneda.map (φ.hom.app (op U))) := by
      refine (NatTrans.isIso_iff_isIso_app _).mpr fun ⟨X⟩ ↦ ?_
      let G' : Sheaf (smallEtaleTopology S) (Type v') :=
        ⟨G.obj ⋙ coyoneda.obj (op X), (isSheaf_iff_isSheaf_of_type _ _).mpr (G.property X)⟩
      let F' : Sheaf (smallEtaleTopology S) (Type v') :=
        ⟨F.obj ⋙ coyoneda.obj (op X), (isSheaf_iff_isSheaf_of_type _ _).mpr (F.property X)⟩
      let φ' : G' ⟶ F' := ⟨Functor.whiskerRight φ.hom (coyoneda.obj (op X))⟩
      have hiso' : ∀ i, IsIso ((restrictSheaf (p i)).map φ') := fun i ↦ by
        have : IsIso ((restrictSheaf (p i)).map φ) := hiso i
        have hnat : IsIso (((restrictSheaf (p i)).map φ).hom) :=
          (sheafToPresheaf (smallEtaleTopology (T i)) A).map_isIso ((restrictSheaf (p i)).map φ)
        have hval' : IsIso ((sheafToPresheaf (smallEtaleTopology (T i)) (Type v')).map
            ((restrictSheaf (p i)).map φ')) := by
          refine (NatTrans.isIso_iff_isIso_app _).mpr fun ⟨V⟩ ↦ ?_
          have hV : IsIso (φ.hom.app (op ((p i).smallEtaleMap.obj V))) := by
            simpa [restrictSheaf_map_app] using (NatTrans.isIso_iff_isIso_app _).mp hnat (op V)
          exact (coyoneda.obj (op X)).map_isIso (φ.hom.app (op ((p i).smallEtaleMap.obj V)))
        exact isIso_of_reflects_iso ((restrictSheaf (p i)).map φ')
          (sheafToPresheaf (smallEtaleTopology (T i)) (Type v'))
      have hφ' : IsIso φ' := isIso_of_forall_isIso_restrictSheaf_type p hsurj φ' hiso'
      have hnat' : IsIso φ'.hom :=
        (sheafToPresheaf (smallEtaleTopology S) (Type v')).map_isIso φ'
      exact (NatTrans.isIso_iff_isIso_app _).mp hnat' (op U)
    exact isIso_of_reflects_iso (φ.hom.app (op U)) yoneda
  exact isIso_of_reflects_iso φ (sheafToPresheaf (smallEtaleTopology S) A)

end Locality

end Etale

end AlgebraicGeometry.Scheme
