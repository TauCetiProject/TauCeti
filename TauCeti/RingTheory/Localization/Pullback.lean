/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Category.Ring.Under.Limits
import TauCeti.CategoryTheory.Comma.Under.Pushout

/-!
# Localization of ring pullbacks

Localization at a submonoid of the upper-left ring preserves a pullback square of
commutative rings. The four carriers may be arbitrary localizations, and the maps need
only agree with the original square on numerators.

The principal-localization specialization is
[Stacks Project, Lemma 15.5.3, tag 01Z8](https://stacks.math.columbia.edu/tag/01Z8).
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.IsPullback

universe u

/-- Localizing a pullback square of commutative rings at a submonoid of its upper-left
ring preserves the pullback. The maps on the given localization carriers are specified by
compatibility with the original arrows on numerators.

The submonoids in the other three rings are the images of `M` along the two
outgoing arrows and their composite to the common target. -/
theorem localization {A B C D A' B' C' D' : CommRingCat.{u}}
    {i : A ⟶ B} {j : A ⟶ C} {f : B ⟶ D} {g : C ⟶ D} (h : IsPullback i j f g)
    (M : Submonoid A) [Algebra A A'] [Algebra B B'] [Algebra C C'] [Algebra D D']
    [IsLocalization M A'] [IsLocalization (M.map i.hom) B']
    [IsLocalization (M.map j.hom) C'] [IsLocalization (M.map (i ≫ f).hom) D']
    {i' : A' ⟶ B'} {j' : A' ⟶ C'} {f' : B' ⟶ D'} {g' : C' ⟶ D'}
    (hi : ∀ x, i' (algebraMap A A' x) = algebraMap B B' (i x))
    (hj : ∀ x, j' (algebraMap A A' x) = algebraMap C C' (j x))
    (hf : ∀ x, f' (algebraMap B B' x) = algebraMap D D' (f x))
    (hg : ∀ x, g' (algebraMap C C' x) = algebraMap D D' (g x)) :
    IsPullback i' j' f' g' := by
  let a : A ⟶ A' := CommRingCat.ofHom (algebraMap A A')
  let b : B ⟶ B' := CommRingCat.ofHom (algebraMap B B')
  let c : C ⟶ C' := CommRingCat.ofHom (algebraMap C C')
  let d : D ⟶ D' := CommRingCat.ofHom (algebraMap D D')
  have hi₀ : a ≫ i' = i ≫ b := by ext x; exact hi x
  have hj₀ : a ≫ j' = j ≫ c := by ext x; exact hj x
  have hf₀ : b ≫ f' = f ≫ d := by ext x; exact hf x
  have hg₀ : c ≫ g' = g ≫ d := by ext x; exact hg x
  have hiP : IsPushout i a b i' :=
    CommRingCat.isPushout_of_isLocalization i.hom i'.hom (congrArg CommRingCat.Hom.hom hi₀) M
  have hjP : IsPushout j a c j' :=
    CommRingCat.isPushout_of_isLocalization j.hom j'.hom (congrArg CommRingCat.Hom.hom hj₀) M
  -- Reassociate the two numerator squares to obtain the composite square.
  have hdComm : a ≫ (i' ≫ f') = (i ≫ f) ≫ d := by
    rw [← Category.assoc, hi₀, Category.assoc, hf₀, Category.assoc]
  have hdP : IsPushout (i ≫ f) a d (i' ≫ f') :=
    CommRingCat.isPushout_of_isLocalization (i ≫ f).hom (i' ≫ f').hom
      (congrArg CommRingCat.Hom.hom hdComm) M
  have haP : IsPushout (𝟙 A) a a (𝟙 A') := IsPushout.of_id_fst
  -- Lift the original square to rings under `A`, where flat base change preserves limits.
  let ii : Under.mk (𝟙 A) ⟶ Under.mk i := Under.homMk i
  let jj : Under.mk (𝟙 A) ⟶ Under.mk j := Under.homMk j
  let ff : Under.mk i ⟶ Under.mk (i ≫ f) := Under.homMk f
  let gg : Under.mk j ⟶ Under.mk (i ≫ f) := Under.homMk g h.w.symm
  have hu : IsPullback ii jj ff gg :=
    IsPullback.of_map (Under.forget A) (by apply Under.UnderMorphism.ext; exact h.w) h
  let F := Under.pushout a ⋙ Under.forget A'
  have : PreservesFiniteLimits (Under.pushout a) :=
    CommRingCat.Under.preservesFiniteLimits_of_flat a
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A' M))
  have hm := hu.map F
  -- Evaluate the original square on numerators before extending to the localizations.
  have hw_on_numerators (x : A) :
      (i' ≫ f') (algebraMap A A' x) = (j' ≫ g') (algebraMap A A' x) := by
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, hi, hj, hf, hg]
    exact congrArg (algebraMap D D') (ConcreteCategory.congr_hom h.w x)
  have hw : i' ≫ f' = j' ≫ g' := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext M
    ext x
    exact hw_on_numerators x
  -- Identify each chosen localization with its categorical pushout.
  exact hm.of_iso haP.isoPushout.symm hiP.isoPushout.symm hjP.isoPushout.symm
    hdP.isoPushout.symm
    (Under.pushout_map_isoPushout_inv ii haP hiP i' hi₀ (by simp))
    (Under.pushout_map_isoPushout_inv jj haP hjP j' hj₀ (by simp))
    (Under.pushout_map_isoPushout_inv ff hiP hdP f' hf₀ rfl)
    (Under.pushout_map_isoPushout_inv gg hjP hdP g' hg₀ hw.symm)

/-- A pullback square of commutative rings stays a pullback when localizing at an element of the
upper-left ring. The four given maps on localizations agree with the original arrows on numerators,
so the statement also applies to the section maps on principal opens. -/
theorem localizationAway {A B C D A' B' C' D' : CommRingCat.{u}}
    {i : A ⟶ B} {j : A ⟶ C} {f : B ⟶ D} {g : C ⟶ D} (h : IsPullback i j f g)
    (r : A) [Algebra A A'] [Algebra B B'] [Algebra C C'] [Algebra D D']
    [IsLocalization.Away r A'] [IsLocalization.Away (i r) B']
    [IsLocalization.Away (j r) C'] [IsLocalization.Away (f (i r)) D']
    {i' : A' ⟶ B'} {j' : A' ⟶ C'} {f' : B' ⟶ D'} {g' : C' ⟶ D'}
    (hi : ∀ x, i' (algebraMap A A' x) = algebraMap B B' (i x))
    (hj : ∀ x, j' (algebraMap A A' x) = algebraMap C C' (j x))
    (hf : ∀ x, f' (algebraMap B B' x) = algebraMap D D' (f x))
    (hg : ∀ x, g' (algebraMap C C' x) = algebraMap D D' (g x)) :
    IsPullback i' j' f' g' := by
  have : IsLocalization ((Submonoid.powers r).map i.hom) B' := by
    simpa only [Submonoid.map_powers] using (inferInstance : IsLocalization.Away (i r) B')
  have : IsLocalization ((Submonoid.powers r).map j.hom) C' := by
    simpa only [Submonoid.map_powers] using (inferInstance : IsLocalization.Away (j r) C')
  have : IsLocalization ((Submonoid.powers r).map (i ≫ f).hom) D' := by
    simpa only [Submonoid.map_powers, CommRingCat.comp_apply] using
      (inferInstance : IsLocalization.Away (f (i r)) D')
  exact h.localization (.powers r) hi hj hf hg

end CategoryTheory.IsPullback
