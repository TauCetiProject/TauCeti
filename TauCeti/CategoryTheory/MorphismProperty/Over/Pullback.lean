/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Coherence and pseudofunctoriality of base change in restricted over categories

For morphism properties `P` and `Q` on a category `T`, Mathlib defines the base-change functor
`CategoryTheory.MorphismProperty.Over.pullback P Q f : P.Over Q Y ⥤ P.Over Q X` along `f : X ⟶ Y`,
together with its composition isomorphism `Over.pullbackComp` and congruence isomorphism
`Over.pullbackCongr`.

This file supplies the remaining coherence data and packages the categories `P.Over Q X` and their
base-change functors into a contravariant pseudofunctor into `Cat`:

* `CategoryTheory.MorphismProperty.Over.pullbackId`: base change along an identity morphism is
  naturally isomorphic to the identity functor, via the first projection `pullback.fst A.hom f`.
* `CategoryTheory.MorphismProperty.Over.pullbackCommSqIso` and
  `CategoryTheory.MorphismProperty.Over.pullbackConditionIso`: the base-change comparison
  isomorphism across a commutative (in particular cartesian) square.
* `CategoryTheory.MorphismProperty.Over.pullbackComp_assoc`,
  `CategoryTheory.MorphismProperty.Over.pullbackComp_id`, and
  `CategoryTheory.MorphismProperty.Over.id_pullbackComp`: associativity and unit coherence of
  `Over.pullbackComp` and `Over.pullbackId`, together with flexible-factorization forms
  `Over.pullbackComp_assoc'`, `Over.pullbackComp_id'`, and `Over.id_pullbackComp'`.
* `CategoryTheory.MorphismProperty.Over.pullbackPseudofunctor`: the contravariant pseudofunctor
  `LocallyDiscrete Tᵒᵖ ⥤ᵖ Cat` sending `X` to `P.Over Q X` and `f : X ⟶ Y` to
  `Over.pullback P Q f`.
-/

public section

universe v u

namespace CategoryTheory.MorphismProperty

open Bicategory Category Limits

variable {T : Type u} [Category.{v} T]

section IsIso

variable {P : MorphismProperty T} {X Y : T}

/-- Pullbacks of morphisms satisfying `P` exist along every isomorphism. -/
instance hasPullbacksAlong_of_isIso (f : X ⟶ Y) [IsIso f] : P.HasPullbacksAlong f where
  hasPullback _ _ := hasPullback_of_right_iso _ _

/-- Any isomorphism-invariant morphism property is stable under base change along isomorphisms. -/
instance isStableUnderBaseChangeAlong_of_isIso [P.RespectsIso] (f : X ⟶ Y) [IsIso f] :
    P.IsStableUnderBaseChangeAlong f where
  of_isPullback {_ _ f' g' g} pb hg := by
    have := pb.isIso_fst_of_isIso
    have hEq : g' = (f' ≫ g) ≫ inv f := by rw [pb.w, assoc, IsIso.hom_inv_id, comp_id]
    rw [hEq, P.cancel_right_of_respectsIso, P.cancel_left_of_respectsIso]
    exact hg

end IsIso

namespace Over

section Ext

variable {P Q : MorphismProperty T} [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]

/-- Two morphisms in `P.Over Q X` into a base-changed object `(Over.pullback P Q f).obj A` are
equal as soon as their compositions with the first projection `pullback.fst A.hom f` agree, since
their second projections agree automatically over `X`. -/
lemma pullback_hom_ext {X Y : T} {f : X ⟶ Y} [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] {B : P.Over Q X} {A : P.Over Q Y}
    {u v : B ⟶ (Over.pullback P Q f).obj A}
    (h : u.left ≫ Limits.pullback.fst A.hom f = v.left ≫ Limits.pullback.fst A.hom f) :
    u = v :=
  Over.Hom.ext <| Limits.pullback.hom_ext h ((Over.w u).trans (Over.w v).symm)

/-- Two morphisms in `P.Over Q W` into an iterated base change
`(Over.pullback P Q f).obj ((Over.pullback P Q g).obj A)` are equal as soon as their compositions
with `pullback.fst _ f ≫ pullback.fst A.hom g` agree. -/
lemma pullback_pullback_hom_ext {W X Y : T} {f : W ⟶ X} {g : X ⟶ Y}
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g]
    [P.IsStableUnderBaseChangeAlong f] [P.IsStableUnderBaseChangeAlong g]
    {B : P.Over Q W} {A : P.Over Q Y}
    {u v : B ⟶ (Over.pullback P Q f).obj ((Over.pullback P Q g).obj A)}
    (h : u.left ≫ Limits.pullback.fst (Limits.pullback.snd A.hom g) f ≫
        Limits.pullback.fst A.hom g =
      v.left ≫ Limits.pullback.fst (Limits.pullback.snd A.hom g) f ≫
        Limits.pullback.fst A.hom g) :
    u = v := by
  refine pullback_hom_ext (Limits.pullback.hom_ext ?_ ?_)
  · exact (assoc _ _ _).trans (h.trans (assoc _ _ _).symm)
  · exact (assoc u.left _ _).trans ((congrArg (u.left ≫ ·) Limits.pullback.condition).trans
      ((assoc _ _ _).symm.trans ((congrArg (· ≫ f) ((Over.w u).trans (Over.w v).symm)).trans
        ((assoc _ _ _).trans ((congrArg (v.left ≫ ·) Limits.pullback.condition.symm).trans
          (assoc v.left _ _).symm)))))

@[reassoc]
lemma pullback_map_left_fst {X Y : T} (f : X ⟶ Y) [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] {A B : P.Over Q Y} (g : A ⟶ B) :
    ((Over.pullback P Q f).map g).left ≫ Limits.pullback.fst B.hom f =
      Limits.pullback.fst A.hom f ≫ g.left :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
lemma pullback_map_left_snd {X Y : T} (f : X ⟶ Y) [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] {A B : P.Over Q Y} (g : A ⟶ B) :
    ((Over.pullback P Q f).map g).left ≫ Limits.pullback.snd B.hom f =
      Limits.pullback.snd A.hom f :=
  Limits.pullback.lift_snd _ _ _

/-- For `A : P.Over Q Y`, the object `(Over.pullback P Q f).obj A` fits into a pullback square over
`f : X ⟶ Y` with top morphism `pullback.fst A.hom f`. -/
lemma isPullback_pullback_obj {X Y : T} (f : X ⟶ Y) [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] (A : P.Over Q Y) :
    IsPullback (Limits.pullback.fst A.hom f) ((Over.pullback P Q f).obj A).hom A.hom f :=
  IsPullback.of_hasPullback A.hom f

/-- For a morphism `g : A ⟶ B` in `P.Over Q Y`, its base change `(Over.pullback P Q f).map g` fits
into a pullback square with `g.left` along the projections `pullback.fst A.hom f` and
`pullback.fst B.hom f`. -/
lemma isPullback_pullback_map {X Y : T} (f : X ⟶ Y) [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] {A B : P.Over Q Y} (g : A ⟶ B) :
    IsPullback (Limits.pullback.fst A.hom f) ((Over.pullback P Q f).map g).left
      g.left (Limits.pullback.fst B.hom f) :=
  IsPullback.of_bot
    ((pullback_map_left_snd f g).symm ▸ (Over.w g).symm ▸ IsPullback.of_hasPullback A.hom f)
    (pullback_map_left_fst f g).symm
    (IsPullback.of_hasPullback B.hom f)

private lemma pullback_iterated₃_hom_ext {W X Y Z : T} {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z}
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g] [P.HasPullbacksAlong h]
    [P.IsStableUnderBaseChangeAlong f] [P.IsStableUnderBaseChangeAlong g]
    [P.IsStableUnderBaseChangeAlong h]
    {B : P.Over Q W} {A : P.Over Q Z}
    {u v : B ⟶ (Over.pullback P Q f).obj
      ((Over.pullback P Q g).obj ((Over.pullback P Q h).obj A))}
    (heq : haveI : HasPullback (Limits.pullback.snd (Limits.pullback.snd A.hom h) g) f :=
        (HasPullbacksAlong.hasPullback _
          ((Over.pullback P Q g).obj ((Over.pullback P Q h).obj A)).prop)
      u.left ≫
        Limits.pullback.fst (Limits.pullback.snd (Limits.pullback.snd A.hom h) g) f ≫
          Limits.pullback.fst (Limits.pullback.snd A.hom h) g ≫
            Limits.pullback.fst A.hom h =
      v.left ≫
        Limits.pullback.fst (Limits.pullback.snd (Limits.pullback.snd A.hom h) g) f ≫
          Limits.pullback.fst (Limits.pullback.snd A.hom h) g ≫
            Limits.pullback.fst A.hom h) :
    u = v := by
  have : HasPullback (Limits.pullback.snd (Limits.pullback.snd A.hom h) g) f :=
    HasPullbacksAlong.hasPullback _ ((Over.pullback P Q g).obj ((Over.pullback P Q h).obj A)).prop
  have hproj (w : B ⟶ (Over.pullback P Q f).obj
      ((Over.pullback P Q g).obj ((Over.pullback P Q h).obj A))) :
      w.left ≫ (Limits.pullback.fst (Limits.pullback.snd (Limits.pullback.snd A.hom h) g) f ≫
        Limits.pullback.fst (Limits.pullback.snd A.hom h) g) ≫ Limits.pullback.snd A.hom h =
      (B.hom ≫ f) ≫ g :=
    (congrArg (w.left ≫ ·) ((assoc _ _ _).trans
      ((congrArg (_ ≫ ·)
        (Limits.pullback.condition (f := Limits.pullback.snd A.hom h) (g := g))).trans
        ((assoc _ _ _).symm.trans (congrArg (· ≫ g)
          (Limits.pullback.condition
            (f := Limits.pullback.snd (Limits.pullback.snd A.hom h) g) (g := f))))))).trans
          ((assoc _ _ _).symm.trans (congrArg (· ≫ g)
            ((assoc _ _ _).symm.trans (congrArg (· ≫ f) (Over.w w)))))
  refine pullback_pullback_hom_ext (Limits.pullback.hom_ext ?_ ?_)
  · exact (assoc u.left _ _).trans ((congrArg (u.left ≫ ·) (assoc _ _ _)).trans
      (heq.trans ((congrArg (v.left ≫ ·) (assoc _ _ _).symm).trans
        (assoc v.left _ _).symm)))
  · exact (assoc u.left _ _).trans
      ((hproj u).trans ((hproj v).symm.trans (assoc v.left _ _).symm))

end Ext

section PullbackId

variable (P Q : MorphismProperty T) [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]

/-- Base change in `P.Over Q X` along a morphism equal to `𝟙 X` is naturally isomorphic to the
identity functor, with forward component given by `pullback.fst`. -/
noncomputable def pullbackId (X : T) (f : X ⟶ X := 𝟙 X) (hf : f = 𝟙 X := by cat_disch)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] :
    Over.pullback P Q f ≅ 𝟭 (P.Over Q X) :=
  NatIso.ofComponents
    (fun A ↦ Over.isoMk
      { hom := Limits.pullback.fst A.hom f
        inv := Limits.pullback.lift (𝟙 A.left) A.hom (by simp [hf])
        hom_inv_id := by
          subst hf
          apply Limits.pullback.hom_ext
          · exact (assoc _ _ _).trans ((congrArg (_ ≫ ·) (Limits.pullback.lift_fst _ _ _)).trans
              ((comp_id _).trans (id_comp _).symm))
          · exact (assoc _ _ _).trans ((congrArg (_ ≫ ·) (Limits.pullback.lift_snd _ _ _)).trans
              (Limits.pullback.condition.trans ((comp_id _).trans (id_comp _).symm)))
        inv_hom_id := Limits.pullback.lift_fst _ _ _ }
      (by subst hf; exact Limits.pullback.condition.trans (comp_id _)))
    (fun _ ↦ Over.Hom.ext (Limits.pullback.lift_fst _ _ _))

end PullbackId

section PullbackIdSimp

variable {P Q : MorphismProperty T} [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]

@[simp]
lemma pullbackId_hom_app_left {X : T} {f : X ⟶ X} (hf : f = 𝟙 X)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] (A : P.Over Q X) :
    ((pullbackId P Q X f hf).hom.app A).left = Limits.pullback.fst A.hom f :=
  (rfl)

@[simp, reassoc]
lemma pullbackId_inv_app_left_fst {X : T} {f : X ⟶ X} (hf : f = 𝟙 X)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] (A : P.Over Q X) :
    ((pullbackId P Q X f hf).inv.app A).left ≫ Limits.pullback.fst A.hom f = 𝟙 A.left :=
  Limits.pullback.lift_fst _ _ _

@[simp, reassoc]
lemma pullbackId_inv_app_left_snd {X : T} {f : X ⟶ X} (hf : f = 𝟙 X)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] (A : P.Over Q X) :
    ((pullbackId P Q X f hf).inv.app A).left ≫ Limits.pullback.snd A.hom f = A.hom :=
  Limits.pullback.lift_snd _ _ _

end PullbackIdSimp

section Projections

variable {P Q : MorphismProperty T} [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]

@[simp, reassoc]
lemma pullbackCongr_hom_app_left_snd {X Y : T} {f g : X ⟶ Y} [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] (h : f = g) (A : P.Over Q Y) :
    haveI : P.HasPullbacksAlong g := by subst h; infer_instance
    ((pullbackCongr h).hom.app A).left ≫ Limits.pullback.snd A.hom g =
      Limits.pullback.snd A.hom f :=
  Over.w _

@[simp]
lemma pullbackCongr_rfl {X Y : T} (f : X ⟶ Y) [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] :
    pullbackCongr (P := P) (Q := Q) (rfl : f = f) = Iso.refl _ := by
  ext A
  apply Limits.pullback.hom_ext
  · exact (pullbackCongr_hom_app_left_fst rfl A).trans
      (id_comp (Limits.pullback.fst A.hom f)).symm
  · exact (pullbackCongr_hom_app_left_snd rfl A).trans
      (id_comp (Limits.pullback.snd A.hom f)).symm

@[simp, reassoc]
lemma pullbackCongr_inv_app_left_fst {X Y : T} {f g : X ⟶ Y} [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] (h : f = g) (A : P.Over Q Y) :
    ((pullbackCongr h).inv.app A).left ≫ Limits.pullback.fst A.hom f =
      haveI : P.HasPullbacksAlong g := by subst h; infer_instance
      Limits.pullback.fst A.hom g := by
  subst h
  rw [pullbackCongr_rfl]
  exact id_comp (Limits.pullback.fst A.hom f)

@[simp, reassoc]
lemma pullbackCongr_inv_app_left_snd {X Y : T} {f g : X ⟶ Y} [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] (h : f = g) (A : P.Over Q Y) :
    ((pullbackCongr h).inv.app A).left ≫ Limits.pullback.snd A.hom f =
      haveI : P.HasPullbacksAlong g := by subst h; infer_instance
      Limits.pullback.snd A.hom g :=
  Over.w _

@[reassoc]
lemma pullbackComp_hom_app_left_fst_fst {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z)
    [P.IsStableUnderBaseChangeAlong f] [P.IsStableUnderBaseChangeAlong g]
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g]
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (A : P.Over Q Z) :
    haveI : P.HasPullbacksAlong fg := by subst hfg; infer_instance
    ((pullbackComp f g fg hfg).hom.app A).left ≫
        Limits.pullback.fst (Limits.pullback.snd A.hom g) f ≫ Limits.pullback.fst A.hom g =
      Limits.pullback.fst A.hom fg := by
  subst hfg
  exact pullbackComp_left_fst_fst f g A

@[reassoc]
lemma pullbackComp_hom_app_left_snd {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z)
    [P.IsStableUnderBaseChangeAlong f] [P.IsStableUnderBaseChangeAlong g]
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g]
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (A : P.Over Q Z) :
    haveI : P.HasPullbacksAlong fg := by subst hfg; infer_instance
    ((pullbackComp f g fg hfg).hom.app A).left ≫
        Limits.pullback.snd (Limits.pullback.snd A.hom g) f =
      Limits.pullback.snd A.hom fg :=
  Over.w _

@[reassoc]
lemma pullbackComp_inv_app_left_fst {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z)
    [P.IsStableUnderBaseChangeAlong f] [P.IsStableUnderBaseChangeAlong g]
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g]
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (A : P.Over Q Z) :
    haveI : P.HasPullbacksAlong fg := by subst hfg; infer_instance
    ((pullbackComp f g fg hfg).inv.app A).left ≫ Limits.pullback.fst A.hom fg =
      Limits.pullback.fst (Limits.pullback.snd A.hom g) f ≫ Limits.pullback.fst A.hom g := by
  have hid : (((pullbackComp (P := P) (Q := Q) f g fg hfg).inv.app A).left ≫
      ((pullbackComp (P := P) (Q := Q) f g fg hfg).hom.app A).left) = 𝟙 _ :=
    congrArg (·.left) ((pullbackComp (P := P) (Q := Q) f g fg hfg).inv_hom_id_app A)
  exact (congrArg (_ ≫ ·) (pullbackComp_hom_app_left_fst_fst f g fg hfg A).symm).trans
    ((assoc _ _ _).symm.trans ((congrArg (· ≫ _) hid).trans (id_comp _)))

@[reassoc]
lemma pullbackComp_inv_app_left_snd {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z)
    [P.IsStableUnderBaseChangeAlong f] [P.IsStableUnderBaseChangeAlong g]
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g]
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) (A : P.Over Q Z) :
    haveI : P.HasPullbacksAlong fg := by subst hfg; infer_instance
    ((pullbackComp f g fg hfg).inv.app A).left ≫ Limits.pullback.snd A.hom fg =
      Limits.pullback.snd (Limits.pullback.snd A.hom g) f :=
  Over.w _

end Projections

section CommSq

variable {P Q : MorphismProperty T} [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]

/-- A commutative square `f' ≫ f = g' ≫ g` induces a natural isomorphism between the composite
base-change functors `Over.pullback P Q f ⋙ Over.pullback P Q f'` and
`Over.pullback P Q g ⋙ Over.pullback P Q g'`. -/
noncomputable def pullbackCommSqIso {W X Y Z : T} {f' : W ⟶ X} {f : X ⟶ Z} {g' : W ⟶ Y}
    {g : Y ⟶ Z} (w : f' ≫ f = g' ≫ g)
    [P.HasPullbacksAlong f'] [P.HasPullbacksAlong f]
    [P.HasPullbacksAlong g'] [P.HasPullbacksAlong g]
    [P.IsStableUnderBaseChangeAlong f'] [P.IsStableUnderBaseChangeAlong f]
    [P.IsStableUnderBaseChangeAlong g'] [P.IsStableUnderBaseChangeAlong g] :
    Over.pullback P Q f ⋙ Over.pullback P Q f' ≅ Over.pullback P Q g ⋙ Over.pullback P Q g' :=
  (pullbackComp f' f).symm ≪≫ pullbackCongr w ≪≫ pullbackComp g' g

@[reassoc]
lemma pullbackCommSqIso_hom_app_left_fst_fst {W X Y Z : T} {f' : W ⟶ X} {f : X ⟶ Z}
    {g' : W ⟶ Y} {g : Y ⟶ Z} (w : f' ≫ f = g' ≫ g)
    [P.HasPullbacksAlong f'] [P.HasPullbacksAlong f]
    [P.HasPullbacksAlong g'] [P.HasPullbacksAlong g]
    [P.IsStableUnderBaseChangeAlong f'] [P.IsStableUnderBaseChangeAlong f]
    [P.IsStableUnderBaseChangeAlong g'] [P.IsStableUnderBaseChangeAlong g]
    (A : P.Over Q Z) :
    ((pullbackCommSqIso (P := P) (Q := Q) w).hom.app A).left ≫
        Limits.pullback.fst (Limits.pullback.snd A.hom g) g' ≫ Limits.pullback.fst A.hom g =
      Limits.pullback.fst (Limits.pullback.snd A.hom f) f' ≫ Limits.pullback.fst A.hom f := by
  change (((pullbackComp f' f).inv.app A).left ≫ ((pullbackCongr w).hom.app A).left ≫
      ((pullbackComp g' g).hom.app A).left) ≫ _ = _
  refine (assoc _ _ _).trans ((congrArg (_ ≫ ·) ((assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (pullbackComp_hom_app_left_fst_fst g' g _ rfl A)).trans
      (pullbackCongr_hom_app_left_fst w A)))).trans
        (pullbackComp_inv_app_left_fst f' f _ rfl A))

@[reassoc]
lemma pullbackCommSqIso_hom_app_left_snd {W X Y Z : T} {f' : W ⟶ X} {f : X ⟶ Z}
    {g' : W ⟶ Y} {g : Y ⟶ Z} (w : f' ≫ f = g' ≫ g)
    [P.HasPullbacksAlong f'] [P.HasPullbacksAlong f]
    [P.HasPullbacksAlong g'] [P.HasPullbacksAlong g]
    [P.IsStableUnderBaseChangeAlong f'] [P.IsStableUnderBaseChangeAlong f]
    [P.IsStableUnderBaseChangeAlong g'] [P.IsStableUnderBaseChangeAlong g]
    (A : P.Over Q Z) :
    ((pullbackCommSqIso (P := P) (Q := Q) w).hom.app A).left ≫
        Limits.pullback.snd (Limits.pullback.snd A.hom g) g' =
      Limits.pullback.snd (Limits.pullback.snd A.hom f) f' :=
  Over.w _

@[simp]
lemma pullbackCommSqIso_symm {W X Y Z : T} {f' : W ⟶ X} {f : X ⟶ Z} {g' : W ⟶ Y} {g : Y ⟶ Z}
    (w : f' ≫ f = g' ≫ g)
    [P.HasPullbacksAlong f'] [P.HasPullbacksAlong f]
    [P.HasPullbacksAlong g'] [P.HasPullbacksAlong g]
    [P.IsStableUnderBaseChangeAlong f'] [P.IsStableUnderBaseChangeAlong f]
    [P.IsStableUnderBaseChangeAlong g'] [P.IsStableUnderBaseChangeAlong g] :
    (pullbackCommSqIso (P := P) (Q := Q) w).symm = pullbackCommSqIso w.symm := by
  refine Iso.ext <| NatTrans.ext <| funext fun A ↦ pullback_pullback_hom_ext ?_
  have hid : (((pullbackCommSqIso (P := P) (Q := Q) w).inv.app A).left ≫
      ((pullbackCommSqIso (P := P) (Q := Q) w).hom.app A).left) = 𝟙 _ :=
    congrArg (·.left) ((pullbackCommSqIso (P := P) (Q := Q) w).inv_hom_id_app A)
  exact (congrArg (_ ≫ ·) (pullbackCommSqIso_hom_app_left_fst_fst w A).symm).trans
    ((assoc _ _ _).symm.trans ((congrArg (· ≫ _) hid).trans
      ((id_comp _).trans (pullbackCommSqIso_hom_app_left_fst_fst w.symm A).symm)))

@[reassoc]
lemma pullbackCommSqIso_inv_app_left_fst_fst {W X Y Z : T} {f' : W ⟶ X} {f : X ⟶ Z}
    {g' : W ⟶ Y} {g : Y ⟶ Z} (w : f' ≫ f = g' ≫ g)
    [P.HasPullbacksAlong f'] [P.HasPullbacksAlong f]
    [P.HasPullbacksAlong g'] [P.HasPullbacksAlong g]
    [P.IsStableUnderBaseChangeAlong f'] [P.IsStableUnderBaseChangeAlong f]
    [P.IsStableUnderBaseChangeAlong g'] [P.IsStableUnderBaseChangeAlong g]
    (A : P.Over Q Z) :
    ((pullbackCommSqIso (P := P) (Q := Q) w).inv.app A).left ≫
        Limits.pullback.fst (Limits.pullback.snd A.hom f) f' ≫ Limits.pullback.fst A.hom f =
      Limits.pullback.fst (Limits.pullback.snd A.hom g) g' ≫ Limits.pullback.fst A.hom g := by
  have := pullbackCommSqIso_hom_app_left_fst_fst (P := P) (Q := Q) w.symm A
  rwa [← pullbackCommSqIso_symm] at this

@[reassoc]
lemma pullbackCommSqIso_inv_app_left_snd {W X Y Z : T} {f' : W ⟶ X} {f : X ⟶ Z}
    {g' : W ⟶ Y} {g : Y ⟶ Z} (w : f' ≫ f = g' ≫ g)
    [P.HasPullbacksAlong f'] [P.HasPullbacksAlong f]
    [P.HasPullbacksAlong g'] [P.HasPullbacksAlong g]
    [P.IsStableUnderBaseChangeAlong f'] [P.IsStableUnderBaseChangeAlong f]
    [P.IsStableUnderBaseChangeAlong g'] [P.IsStableUnderBaseChangeAlong g]
    (A : P.Over Q Z) :
    ((pullbackCommSqIso (P := P) (Q := Q) w).inv.app A).left ≫
        Limits.pullback.snd (Limits.pullback.snd A.hom f) f' =
      Limits.pullback.snd (Limits.pullback.snd A.hom g) g' :=
  Over.w _

/-- For a pullback square of `f : X ⟶ Z` and `g : Y ⟶ Z`, base change along `f` followed by
`pullback.fst f g` is naturally isomorphic to base change along `g` followed by
`pullback.snd f g`. -/
noncomputable abbrev pullbackConditionIso {X Y Z : T} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]
    [P.HasPullbacksAlong (Limits.pullback.fst f g)] [P.HasPullbacksAlong f]
    [P.HasPullbacksAlong (Limits.pullback.snd f g)] [P.HasPullbacksAlong g]
    [P.IsStableUnderBaseChangeAlong (Limits.pullback.fst f g)] [P.IsStableUnderBaseChangeAlong f]
    [P.IsStableUnderBaseChangeAlong (Limits.pullback.snd f g)] [P.IsStableUnderBaseChangeAlong g] :
    Over.pullback P Q f ⋙ Over.pullback P Q (Limits.pullback.fst f g) ≅
      Over.pullback P Q g ⋙ Over.pullback P Q (Limits.pullback.snd f g) :=
  pullbackCommSqIso Limits.pullback.condition

end CommSq

section Coherence

variable {P Q : MorphismProperty T} [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]

/-- Associativity of `Over.pullbackComp` at arbitrary factorizations `fg = f ≫ g`, `gh = g ≫ h`,
and `fgh = fg ≫ h = f ≫ gh`, stated componentwise without `eqToHom`. -/
@[reassoc]
theorem pullbackComp_assoc' {W X Y Z : T} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h) (hfgh' : fgh = f ≫ gh)
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g] [P.HasPullbacksAlong h]
    [P.IsStableUnderBaseChangeAlong f] [P.IsStableUnderBaseChangeAlong g]
    [P.IsStableUnderBaseChangeAlong h] (A : P.Over Q Z) :
    haveI : P.HasPullbacksAlong fg := by subst hfg; infer_instance
    haveI : P.IsStableUnderBaseChangeAlong fg := by subst hfg; infer_instance
    haveI : P.HasPullbacksAlong gh := by subst hgh; infer_instance
    haveI : P.IsStableUnderBaseChangeAlong gh := by subst hgh; infer_instance
    (pullbackComp f gh fgh hfgh').hom.app A ≫
        (Over.pullback P Q f).map ((pullbackComp g h gh hgh).hom.app A) =
      (pullbackComp fg h fgh hfgh).hom.app A ≫
        (pullbackComp f g fg hfg).hom.app ((Over.pullback P Q h).obj A) := by
  subst hfg hgh hfgh
  refine pullback_iterated₃_hom_ext
    (Eq.trans (b := Limits.pullback.fst A.hom ((f ≫ g) ≫ h)) ?_ (Eq.symm ?_))
  · change (_ ≫ ((Over.pullback P Q f).map _).left) ≫ _ = Limits.pullback.fst A.hom ((f ≫ g) ≫ h)
    exact (assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (((assoc _ _ _).symm.trans (congrArg (· ≫ _)
        (pullback_map_left_fst f ((pullbackComp g h (g ≫ h) rfl).hom.app A)))).trans
          ((assoc _ _ _).trans (congrArg (_ ≫ ·)
            (pullbackComp_hom_app_left_fst_fst g h (g ≫ h) rfl A))))).trans
              (pullbackComp_hom_app_left_fst_fst f (g ≫ h) ((f ≫ g) ≫ h) hfgh' A))
  · change (_ ≫ _) ≫ _ = Limits.pullback.fst A.hom ((f ≫ g) ≫ h)
    exact (assoc _ _ _).trans ((congrArg (_ ≫ ·)
      ((congrArg (_ ≫ ·) (assoc _ _ _).symm).trans
        ((assoc _ _ _).symm.trans (congrArg (· ≫ _)
          (pullbackComp_hom_app_left_fst_fst f g (f ≫ g) rfl
            ((Over.pullback P Q h).obj A)))))).trans
              (pullbackComp_hom_app_left_fst_fst (f ≫ g) h ((f ≫ g) ≫ h) rfl A))

/-- Associativity coherence of `Over.pullbackComp` as an equality of natural isomorphisms. -/
theorem pullbackComp_assoc {W X Y Z : T} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    [P.HasPullbacksAlong f] [P.HasPullbacksAlong g] [P.HasPullbacksAlong h]
    [P.IsStableUnderBaseChangeAlong f] [P.IsStableUnderBaseChangeAlong g]
    [P.IsStableUnderBaseChangeAlong h] :
    pullbackCongr (P := P) (Q := Q) (Category.assoc f g h) ≪≫ pullbackComp f (g ≫ h) ≪≫
        Functor.isoWhiskerRight (pullbackComp g h) (Over.pullback P Q f) ≪≫
        Functor.associator _ _ _ =
      pullbackComp (f ≫ g) h ≪≫
        Functor.isoWhiskerLeft (Over.pullback P Q h) (pullbackComp f g) := by
  refine Iso.ext <| NatTrans.ext <| funext fun A ↦ ?_
  refine (pullback_iterated₃_hom_ext
    (Eq.trans (b := Limits.pullback.fst A.hom ((f ≫ g) ≫ h)) ?_ (Eq.symm ?_))).trans
    (pullbackComp_assoc' (P := P) (Q := Q) f g h (f ≫ g) (g ≫ h) ((f ≫ g) ≫ h) rfl rfl rfl
      (Category.assoc f g h) A)
  · change (_ ≫ _ ≫ ((Over.pullback P Q f).map _).left ≫ 𝟙 _) ≫ _ =
      Limits.pullback.fst A.hom ((f ≫ g) ≫ h)
    exact (assoc _ _ _).trans ((congrArg (_ ≫ ·) ((assoc _ _ _).trans
      ((congrArg (_ ≫ ·) ((assoc _ _ _).trans ((congrArg (_ ≫ ·) (id_comp _)).trans
        (((assoc _ _ _).symm.trans (congrArg (· ≫ _)
          (pullback_map_left_fst f ((pullbackComp g h (g ≫ h) rfl).hom.app A)))).trans
            ((assoc _ _ _).trans (congrArg (_ ≫ ·)
              (pullbackComp_hom_app_left_fst_fst g h (g ≫ h) rfl A))))))).trans
                (pullbackComp_hom_app_left_fst_fst f (g ≫ h) (f ≫ g ≫ h) rfl A)))).trans
                  (pullbackCongr_hom_app_left_fst (Category.assoc f g h) A))
  · change (_ ≫ ((Over.pullback P Q f).map _).left) ≫ _ = Limits.pullback.fst A.hom ((f ≫ g) ≫ h)
    exact (assoc _ _ _).trans ((congrArg (_ ≫ ·)
      (((assoc _ _ _).symm.trans (congrArg (· ≫ _)
        (pullback_map_left_fst f ((pullbackComp g h (g ≫ h) rfl).hom.app A)))).trans
          ((assoc _ _ _).trans (congrArg (_ ≫ ·)
            (pullbackComp_hom_app_left_fst_fst g h (g ≫ h) rfl A))))).trans
              (pullbackComp_hom_app_left_fst_fst f (g ≫ h) ((f ≫ g) ≫ h)
                (Category.assoc f g h) A))

/-- Right unitality of `Over.pullbackComp` and `Over.pullbackId` at an arbitrary factorization
`f = f ≫ u` with `u = 𝟙 Y`. -/
@[reassoc]
theorem pullbackComp_id' {X Y : T} (f : X ⟶ Y) (u : Y ⟶ Y) (hu : u = 𝟙 Y) (hfu : f = f ≫ u)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [P.HasPullbacksAlong u] [P.IsStableUnderBaseChangeAlong u] (A : P.Over Q Y) :
    (pullbackComp f u f hfu).hom.app A ≫
        (Over.pullback P Q f).map ((pullbackId P Q Y u hu).hom.app A) =
      𝟙 ((Over.pullback P Q f).obj A) :=
  pullback_hom_ext <| (assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (Limits.pullback.lift_fst _ _ _)).trans
      ((pullbackComp_hom_app_left_fst_fst f u f hfu A).trans (id_comp _).symm))

/-- Right unitality coherence of `Over.pullbackComp` and `Over.pullbackId` as an equality of
natural isomorphisms. -/
theorem pullbackComp_id {X Y : T} (f : X ⟶ Y) [P.RespectsIso]
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] :
    pullbackComp (P := P) (Q := Q) f (𝟙 Y) ≪≫
        Functor.isoWhiskerRight (pullbackId P Q Y) (Over.pullback P Q f) ≪≫
        Functor.leftUnitor (Over.pullback P Q f) =
      pullbackCongr (Category.comp_id f) :=
  Iso.ext <| NatTrans.ext <| funext fun A ↦ pullback_hom_ext <| by
    change (_ ≫ ((Over.pullback P Q f).map _).left ≫ 𝟙 _) ≫ _ = _
    exact (assoc _ _ _).trans ((congrArg (_ ≫ ·) ((assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (id_comp _)).trans (Limits.pullback.lift_fst _ _ _)))).trans
        ((pullbackComp_hom_app_left_fst_fst f (𝟙 Y) (f ≫ 𝟙 Y) rfl A).trans
          (pullbackCongr_hom_app_left_fst (Category.comp_id f) A).symm))

/-- Left unitality of `Over.pullbackComp` and `Over.pullbackId` at an arbitrary factorization
`f = u ≫ f` with `u = 𝟙 X`. -/
@[reassoc]
theorem id_pullbackComp' {X Y : T} (u : X ⟶ X) (hu : u = 𝟙 X) (f : X ⟶ Y) (huf : f = u ≫ f)
    [P.HasPullbacksAlong u] [P.IsStableUnderBaseChangeAlong u]
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] (A : P.Over Q Y) :
    (pullbackComp u f f huf).hom.app A ≫
        (pullbackId P Q X u hu).hom.app ((Over.pullback P Q f).obj A) =
      𝟙 ((Over.pullback P Q f).obj A) :=
  pullback_hom_ext <| (assoc _ _ _).trans
    ((pullbackComp_hom_app_left_fst_fst u f f huf A).trans (id_comp _).symm)

/-- Left unitality coherence of `Over.pullbackComp` and `Over.pullbackId` as an equality of
natural isomorphisms. -/
theorem id_pullbackComp {X Y : T} (f : X ⟶ Y) [P.RespectsIso]
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] :
    pullbackComp (P := P) (Q := Q) (𝟙 X) f ≪≫
        Functor.isoWhiskerLeft (Over.pullback P Q f) (pullbackId P Q X) ≪≫
        Functor.rightUnitor (Over.pullback P Q f) =
      pullbackCongr (Category.id_comp f) :=
  Iso.ext <| NatTrans.ext <| funext fun A ↦ pullback_hom_ext <| by
    change (_ ≫ _ ≫ 𝟙 _) ≫ _ = _
    exact (assoc _ _ _).trans ((congrArg (_ ≫ ·) ((assoc _ _ _).trans
      (congrArg (_ ≫ ·) (id_comp _)))).trans
        ((pullbackComp_hom_app_left_fst_fst (𝟙 X) f (𝟙 X ≫ f) rfl A).trans
          (pullbackCongr_hom_app_left_fst (Category.id_comp f) A).symm))

end Coherence

section Pseudofunctor

variable (P Q : MorphismProperty T) [P.HasPullbacks] [P.IsStableUnderBaseChange]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]

/-- The contravariant pseudofunctor sending `X : T` to `P.Over Q X` and `f : X ⟶ Y` to
`Over.pullback P Q f`. Its unit and composition comparisons are `Over.pullbackId` and
`Over.pullbackComp`. -/
@[expose]
noncomputable def pullbackPseudofunctor : LocallyDiscrete Tᵒᵖ ⥤ᵖ Cat.{v, max u v} :=
  LocallyDiscrete.mkCatPseudofunctor
    (obj := fun X ↦ Cat.of (P.Over Q X.unop))
    (fun f ↦ Over.pullback P Q f.unop)
    (fun X ↦ pullbackId P Q X.unop)
    (fun f g fg hfg ↦ pullbackComp g.unop f.unop fg.unop (congrArg Quiver.Hom.unop hfg.symm))
    (fun f g h fg gh fgh hfg hgh hfgh hfgh' A ↦
      pullbackComp_assoc' h.unop g.unop f.unop gh.unop fg.unop fgh.unop
        (congrArg Quiver.Hom.unop hgh.symm) (congrArg Quiver.Hom.unop hfg.symm)
        (congrArg Quiver.Hom.unop hfgh'.symm) (congrArg Quiver.Hom.unop hfgh.symm) A)
    (fun f hf A ↦
      pullbackComp_id' f.unop (𝟙 _) rfl (congrArg Quiver.Hom.unop hf.symm) A)
    (fun f hf A ↦
      id_pullbackComp' (𝟙 _) rfl f.unop (congrArg Quiver.Hom.unop hf.symm) A)

@[simp]
lemma pullbackPseudofunctor_obj (X : LocallyDiscrete Tᵒᵖ) :
    (pullbackPseudofunctor P Q).obj X = Cat.of (P.Over Q X.as.unop) :=
  rfl

@[simp]
lemma pullbackPseudofunctor_map_toFunctor {X Y : LocallyDiscrete Tᵒᵖ} (f : X ⟶ Y) :
    ((pullbackPseudofunctor P Q).map f).toFunctor = Over.pullback P Q f.as.unop :=
  rfl

@[simp]
lemma pullbackPseudofunctor_mapId_hom_toNatTrans_app (X : LocallyDiscrete Tᵒᵖ)
    (A : P.Over Q X.as.unop) :
    ((pullbackPseudofunctor P Q).mapId X).hom.toNatTrans.app A =
      (pullbackId P Q X.as.unop).hom.app A :=
  rfl

@[simp]
lemma pullbackPseudofunctor_mapId_inv_toNatTrans_app (X : LocallyDiscrete Tᵒᵖ)
    (A : P.Over Q X.as.unop) :
    ((pullbackPseudofunctor P Q).mapId X).inv.toNatTrans.app A =
      (pullbackId P Q X.as.unop).inv.app A :=
  rfl

@[simp]
lemma pullbackPseudofunctor_mapComp_hom_toNatTrans_app {X Y Z : LocallyDiscrete Tᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : P.Over Q X.as.unop) :
    ((pullbackPseudofunctor P Q).mapComp f g).hom.toNatTrans.app A =
      (pullbackComp g.as.unop f.as.unop (g.as.unop ≫ f.as.unop) rfl).hom.app A :=
  rfl

@[simp]
lemma pullbackPseudofunctor_mapComp_inv_toNatTrans_app {X Y Z : LocallyDiscrete Tᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : P.Over Q X.as.unop) :
    ((pullbackPseudofunctor P Q).mapComp f g).inv.toNatTrans.app A =
      (pullbackComp g.as.unop f.as.unop (g.as.unop ≫ f.as.unop) rfl).inv.app A :=
  rfl

end Pseudofunctor

end Over

end CategoryTheory.MorphismProperty
