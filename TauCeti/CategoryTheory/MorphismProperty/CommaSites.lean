/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.CommaSites
public import Mathlib.CategoryTheory.Sites.Equivalence
public import TauCeti.CategoryTheory.MorphismProperty.Over

/-!
# Continuity, base change, and slice equivalences for restricted over sites

Let `(C, J)` be a site and `P` a morphism property on `C`. When `Over.forget P ⊤ X` is locally
cover-dense with respect to `J.over X`, the category `P.Over ⊤ X` carries the restricted topology
`(Over.forget P ⊤ X).restrictedTopology (J.over X)` (for example, the small étale site of a scheme).

This file establishes three general site-theoretic facts in this setting:
* **Iterated slice equivalence of sites**: for `U : P.Over ⊤ X`, when `P` is stable under
  composition and satisfies `P.HasOfPostcompProperty P`, the slice equivalence
  `Over.iteratedSliceEquiv U : CategoryTheory.Over U ≌ P.Over ⊤ U.left` is a dense-subsite
  equivalence between `(((Over.forget P ⊤ X).restrictedTopology (J.over X)).over U)` and
  `(Over.forget P ⊤ U.left).restrictedTopology (J.over U.left)` (adapting the
  `CategoryTheory.Over.iteratedSliceEquiv` dense-subsite and continuity/cocontinuity instances in
  `Mathlib.CategoryTheory.Sites.Over`). Consequently it induces an equivalence of sheaf categories
  (`overRestrictedSheafEquiv`) under which the over-site restriction `overPullback` identifies with
  pushforward along `Over.map ⊤ U.prop`.
* **Cover-preservation and continuity of `Over.map`**: for a morphism `f : Y ⟶ X` satisfying `P`,
  when `P` is stable under composition, `Over.map ⊤ hf` is cover-preserving for the restricted over
  topologies, and when `P` additionally satisfies `P.HasOfPostcompProperty P`, `Over.map ⊤ hf` is
  continuous.
* **Cover-preservation and continuity of `Over.pullback`**: when `C` has pullbacks and `P` is
  multiplicative, stable under base change, and satisfies `P.HasOfPostcompProperty P`,
  `Over.pullback P ⊤ f` is representably flat, cover-preserving, and continuous for the restricted
  over topologies.
-/

public section

namespace CategoryTheory.MorphismProperty

open Limits Opposite

section IteratedSlice

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  {P : MorphismProperty C} [P.IsStableUnderComposition] [P.HasOfPostcompProperty P]
  {X : C}

omit [P.IsStableUnderComposition] [P.HasOfPostcompProperty P] in
/-- A sieve on `V : P.Over ⊤ X` covers `V` in the restricted over topology if and only if its
pushforward to `C` covers `V.left` in `J`. -/
lemma mem_restrictedTopology_over_iff
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)] {V : P.Over ⊤ X} (S : Sieve V) :
    S ∈ ((Over.forget P ⊤ X).restrictedTopology (J.over X)) V ↔
      S.functorPushforward (Over.forget P ⊤ X ⋙ CategoryTheory.Over.forget X) ∈ J V.left := by
  rw [Functor.mem_restrictedTopology_iff, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_apply, ← Sieve.functorPushforward_comp]
  rfl

omit [P.HasOfPostcompProperty P] in
/-- Pushing a sieve forward along `Over.map ⊤ hf` covers `(Over.map ⊤ hf).obj V` in the restricted
over topology on `X` if and only if the original sieve covers `V` in the restricted over topology
on `Y`. -/
lemma functorPushforward_over_map_mem_restrictedTopology_iff {Y : C} {f : Y ⟶ X} (hf : P f)
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ Y).LocallyCoverDense (J.over Y)]
    {V : P.Over ⊤ Y} (S : Sieve V) :
    S.functorPushforward (Over.map ⊤ hf) ∈
        ((Over.forget P ⊤ X).restrictedTopology (J.over X)) ((Over.map ⊤ hf).obj V) ↔
      S ∈ ((Over.forget P ⊤ Y).restrictedTopology (J.over Y)) V := by
  rw [mem_restrictedTopology_over_iff, mem_restrictedTopology_over_iff,
    ← Sieve.functorPushforward_comp]
  change Sieve.functorPushforward (Over.map ⊤ hf ⋙ Over.forget P ⊤ X ⋙ CategoryTheory.Over.forget X)
      S ∈ J ((Over.map ⊤ hf ⋙ Over.forget P ⊤ X ⋙ CategoryTheory.Over.forget X).obj V) ↔ _
  rw [Over.map_forget_forget]
  rfl

/-- For `U : P.Over ⊤ X`, `Over.iteratedSliceBackward U` is a dense subsite between the restricted
over topology on `P.Over ⊤ U.left` and the slice over `U` of the restricted over topology on
`P.Over ⊤ X`. -/
instance isDenseSubsite_iteratedSliceEquiv_inverse (U : P.Over ⊤ X)
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ U.left).LocallyCoverDense (J.over U.left)] :
    (Over.iteratedSliceEquiv U).inverse.IsDenseSubsite
      ((Over.forget P ⊤ U.left).restrictedTopology (J.over U.left))
      (((Over.forget P ⊤ X).restrictedTopology (J.over X)).over U) where
  functorPushforward_mem_iff {V S} := by
    rw [Over.iteratedSliceEquiv_inverse, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_apply,
      ← Sieve.functorPushforward_comp]
    change Sieve.functorPushforward (U.iteratedSliceBackward ⋙ CategoryTheory.Over.forget U) S ∈
        ((Over.forget P ⊤ X).restrictedTopology (J.over X))
          ((U.iteratedSliceBackward ⋙ CategoryTheory.Over.forget U).obj V) ↔ _
    rw [Over.iteratedSliceBackward_forget]
    exact functorPushforward_over_map_mem_restrictedTopology_iff (X := X) (Y := U.left) J U.prop S

instance isContinuous_iteratedSliceForward (U : P.Over ⊤ X)
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ U.left).LocallyCoverDense (J.over U.left)] :
    (Over.iteratedSliceForward U).IsContinuous
      (((Over.forget P ⊤ X).restrictedTopology (J.over X)).over U)
      ((Over.forget P ⊤ U.left).restrictedTopology (J.over U.left)) := by
  rw [← Over.iteratedSliceEquiv_functor]
  infer_instance

instance isCocontinuous_iteratedSliceForward (U : P.Over ⊤ X)
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ U.left).LocallyCoverDense (J.over U.left)] :
    (Over.iteratedSliceForward U).IsCocontinuous
      (((Over.forget P ⊤ X).restrictedTopology (J.over X)).over U)
      ((Over.forget P ⊤ U.left).restrictedTopology (J.over U.left)) := by
  rw [← Over.iteratedSliceEquiv_functor]
  infer_instance

instance isContinuous_iteratedSliceBackward (U : P.Over ⊤ X)
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ U.left).LocallyCoverDense (J.over U.left)] :
    (Over.iteratedSliceBackward U).IsContinuous
      ((Over.forget P ⊤ U.left).restrictedTopology (J.over U.left))
      (((Over.forget P ⊤ X).restrictedTopology (J.over X)).over U) := by
  rw [← Over.iteratedSliceEquiv_inverse]
  infer_instance

instance isCocontinuous_iteratedSliceBackward (U : P.Over ⊤ X)
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ U.left).LocallyCoverDense (J.over U.left)] :
    (Over.iteratedSliceBackward U).IsCocontinuous
      ((Over.forget P ⊤ U.left).restrictedTopology (J.over U.left))
      (((Over.forget P ⊤ X).restrictedTopology (J.over X)).over U) := by
  rw [← Over.iteratedSliceEquiv_inverse]
  infer_instance

/-- When `P` is stable under composition and satisfies `P.HasOfPostcompProperty P`, for a morphism
`f : Y ⟶ X` satisfying `P`, post-composition `Over.map ⊤ hf` is continuous for the restricted over
topologies. -/
instance isContinuous_over_map {Y : C} {f : Y ⟶ X} (hf : P f)
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ Y).LocallyCoverDense (J.over Y)] :
    (Over.map (P := P) ⊤ hf).IsContinuous
      ((Over.forget P ⊤ Y).restrictedTopology (J.over Y))
      ((Over.forget P ⊤ X).restrictedTopology (J.over X)) := by
  have : (Over.forget P ⊤ (Over.mk ⊤ f hf).left).LocallyCoverDense
      (J.over (Over.mk ⊤ f hf).left) := by
    rw [Over.mk_left]
    infer_instance
  have : (Over.iteratedSliceBackward (Over.mk ⊤ f hf)).IsContinuous
      ((Over.forget P ⊤ Y).restrictedTopology (J.over Y))
      (((Over.forget P ⊤ X).restrictedTopology (J.over X)).over (Over.mk ⊤ f hf)) :=
    isContinuous_iteratedSliceBackward J (Over.mk ⊤ f hf)
  rw [show Over.map (P := P) ⊤ hf =
      Over.map (X := (Over.mk ⊤ f hf).left) (Y := X) ⊤ (Over.mk ⊤ f hf).prop from rfl,
    ← Over.iteratedSliceBackward_forget (Over.mk ⊤ f hf)]
  exact Functor.isContinuous_comp (Over.iteratedSliceBackward (Over.mk ⊤ f hf))
    (CategoryTheory.Over.forget (Over.mk ⊤ f hf))
    ((Over.forget P ⊤ Y).restrictedTopology (J.over Y))
    (((Over.forget P ⊤ X).restrictedTopology (J.over X)).over (Over.mk ⊤ f hf))
    ((Over.forget P ⊤ X).restrictedTopology (J.over X))

omit [P.HasOfPostcompProperty P] in
/-- For a morphism `f : Y ⟶ X` satisfying `P`, post-composition `Over.map ⊤ hf` is
cover-preserving for the restricted over topologies. -/
lemma coverPreserving_over_map {Y : C} {f : Y ⟶ X} (hf : P f)
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ Y).LocallyCoverDense (J.over Y)] :
    CoverPreserving
      ((Over.forget P ⊤ Y).restrictedTopology (J.over Y))
      ((Over.forget P ⊤ X).restrictedTopology (J.over X))
      (Over.map (P := P) ⊤ hf) where
  cover_preserve hS := (functorPushforward_over_map_mem_restrictedTopology_iff J hf _).mpr hS

/-- Equivalence between sheaves on the slice `(P.Over ⊤ X)/U` and sheaves on `P.Over ⊤ U.left`
induced by `Over.iteratedSliceEquiv U`. -/
noncomputable def overRestrictedSheafEquiv (U : P.Over ⊤ X) (A : Type*) [Category* A]
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ U.left).LocallyCoverDense (J.over U.left)] :
    Sheaf (((Over.forget P ⊤ X).restrictedTopology (J.over X)).over U) A ≌
      Sheaf ((Over.forget P ⊤ U.left).restrictedTopology (J.over U.left)) A :=
  (Over.iteratedSliceEquiv U).sheafCongr
    (((Over.forget P ⊤ X).restrictedTopology (J.over X)).over U)
    ((Over.forget P ⊤ U.left).restrictedTopology (J.over U.left)) A

@[simp]
lemma overRestrictedSheafEquiv_functor_obj_obj (U : P.Over ⊤ X) (A : Type*) [Category* A]
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ U.left).LocallyCoverDense (J.over U.left)]
    (F : Sheaf (((Over.forget P ⊤ X).restrictedTopology (J.over X)).over U) A) :
    ((overRestrictedSheafEquiv J U A).functor.obj F).obj =
      (Over.iteratedSliceBackward U).op ⋙ F.obj := by
  rw [← Over.iteratedSliceEquiv_inverse]
  rfl

@[simp]
lemma overRestrictedSheafEquiv_inverse_obj_obj (U : P.Over ⊤ X) (A : Type*) [Category* A]
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ U.left).LocallyCoverDense (J.over U.left)]
    (F : Sheaf ((Over.forget P ⊤ U.left).restrictedTopology (J.over U.left)) A) :
    ((overRestrictedSheafEquiv J U A).inverse.obj F).obj =
      (Over.iteratedSliceForward U).op ⋙ F.obj := by
  rw [← Over.iteratedSliceEquiv_functor]
  rfl

/-- Under `overRestrictedSheafEquiv`, restricting a sheaf on `P.Over ⊤ X` to the slice over `U`
identifies with pushing it forward along `Over.map ⊤ U.prop : P.Over ⊤ U.left ⥤ P.Over ⊤ X`. -/
noncomputable def overPullbackCompOverRestrictedSheafEquivIso
    (U : P.Over ⊤ X) (A : Type*) [Category* A]
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ U.left).LocallyCoverDense (J.over U.left)] :
    ((Over.forget P ⊤ X).restrictedTopology (J.over X)).overPullback A U ⋙
        (overRestrictedSheafEquiv J U A).functor ≅
      (Over.map (X := U.left) (Y := X) ⊤ U.prop).sheafPushforwardContinuous A
        ((Over.forget P ⊤ U.left).restrictedTopology (J.over U.left))
        ((Over.forget P ⊤ X).restrictedTopology (J.over X)) :=
  Functor.sheafPushforwardContinuousComp'
    (eqToIso (by rw [Over.iteratedSliceEquiv_inverse, Over.iteratedSliceBackward_forget]))
    A ((Over.forget P ⊤ U.left).restrictedTopology (J.over U.left))
    (((Over.forget P ⊤ X).restrictedTopology (J.over X)).over U)
    ((Over.forget P ⊤ X).restrictedTopology (J.over X))

lemma overPullbackCompOverRestrictedSheafEquivIso_hom_app_hom_app
    (U : P.Over ⊤ X) (A : Type*) [Category* A]
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ U.left).LocallyCoverDense (J.over U.left)]
    (F : Sheaf ((Over.forget P ⊤ X).restrictedTopology (J.over X)) A)
    (V : (P.Over ⊤ U.left)ᵒᵖ) :
    (((overPullbackCompOverRestrictedSheafEquivIso J U A).hom.app F).hom.app V) =
      eqToHom (by simp) := by
  simp only [overPullbackCompOverRestrictedSheafEquivIso, Functor.comp_obj,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app, eqToIso.inv,
    eqToHom_op, eqToHom_app, eqToHom_map]
  exact rfl

@[simp]
lemma overPullbackCompOverRestrictedSheafEquivIso_hom_app_hom
    (U : P.Over ⊤ X) (A : Type*) [Category* A]
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ U.left).LocallyCoverDense (J.over U.left)]
    (F : Sheaf ((Over.forget P ⊤ X).restrictedTopology (J.over X)) A) :
    ((overPullbackCompOverRestrictedSheafEquivIso J U A).hom.app F).hom =
      eqToHom (by
        simp only [Functor.comp_obj, overRestrictedSheafEquiv_functor_obj_obj,
          ← MorphismProperty.Over.iteratedSliceBackward_forget]
        rfl) := by
  ext V
  simp only [overPullbackCompOverRestrictedSheafEquivIso_hom_app_hom_app, eqToHom_app]

lemma overPullbackCompOverRestrictedSheafEquivIso_inv_app_hom_app
    (U : P.Over ⊤ X) (A : Type*) [Category* A]
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ U.left).LocallyCoverDense (J.over U.left)]
    (F : Sheaf ((Over.forget P ⊤ X).restrictedTopology (J.over X)) A)
    (V : (P.Over ⊤ U.left)ᵒᵖ) :
    (((overPullbackCompOverRestrictedSheafEquivIso J U A).inv.app F).hom.app V) =
      eqToHom (by simp) := by
  simp only [overPullbackCompOverRestrictedSheafEquivIso, Functor.comp_obj,
    Functor.sheafPushforwardContinuousComp'_inv_app_hom_app, eqToIso.hom,
    eqToHom_op, eqToHom_app, eqToHom_map]
  exact rfl

@[simp]
lemma overPullbackCompOverRestrictedSheafEquivIso_inv_app_hom
    (U : P.Over ⊤ X) (A : Type*) [Category* A]
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ U.left).LocallyCoverDense (J.over U.left)]
    (F : Sheaf ((Over.forget P ⊤ X).restrictedTopology (J.over X)) A) :
    ((overPullbackCompOverRestrictedSheafEquivIso J U A).inv.app F).hom =
      eqToHom (by
        simp only [Functor.comp_obj, overRestrictedSheafEquiv_functor_obj_obj,
          ← MorphismProperty.Over.iteratedSliceBackward_forget]
        rfl) := by
  ext V
  simp only [overPullbackCompOverRestrictedSheafEquivIso_inv_app_hom_app, eqToHom_app]

end IteratedSlice

section Pullback

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  (P : MorphismProperty C) {X Y : C} (f : X ⟶ Y)

/-- Base change `Over.pullback P ⊤ f : P.Over ⊤ Y ⥤ P.Over ⊤ X` is representably flat when `C` has
pullbacks and `P` is multiplicative, stable under base change, and satisfies post-cancellation. -/
instance representablyFlat_over_pullback [HasPullbacks C] [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    RepresentablyFlat (Over.pullback P ⊤ f) :=
  flat_of_preservesFiniteLimits (Over.pullback P ⊤ f)

/-- Base change `Over.pullback P ⊤ f` is cover-preserving for the restricted over topologies. -/
lemma coverPreserving_over_pullback [HasPullbacks C] [P.IsStableUnderBaseChangeAlong f]
    [(Over.forget P ⊤ Y).LocallyCoverDense (J.over Y)]
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)] :
    CoverPreserving
      ((Over.forget P ⊤ Y).restrictedTopology (J.over Y))
      ((Over.forget P ⊤ X).restrictedTopology (J.over X))
      (Over.pullback P ⊤ f) where
  cover_preserve {U S} hS := by
    have hmem :
        Sieve.functorPushforward (Over.forget P ⊤ Y ⋙ CategoryTheory.Over.pullback f) S ∈
          (J.over X) ((CategoryTheory.Over.pullback f).obj ((Over.forget P ⊤ Y).obj U)) := by
      rw [Sieve.functorPushforward_comp]
      exact (J.coverPreserving_overPullback f).cover_preserve
        ((Functor.coverPreserving_restrictedTopology (Over.forget P ⊤ Y) (J.over Y)).cover_preserve
          hS)
    rw [Functor.mem_restrictedTopology_iff, ← Sieve.functorPushforward_comp]
    exact hmem

/-- Base change `Over.pullback P ⊤ f` is continuous for the restricted over topologies when `C` has
pullbacks and `P` is multiplicative, stable under base change, and satisfies
`P.HasOfPostcompProperty P`. -/
instance isContinuous_over_pullback [HasPullbacks C] [P.IsMultiplicative]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    [(Over.forget P ⊤ Y).LocallyCoverDense (J.over Y)]
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)] :
    (Over.pullback P ⊤ f).IsContinuous
      ((Over.forget P ⊤ Y).restrictedTopology (J.over Y))
      ((Over.forget P ⊤ X).restrictedTopology (J.over X)) := by
  rw [Functor.isContinuous_iff_coverPreserving]
  exact coverPreserving_over_pullback J P f

end Pullback

end CategoryTheory.MorphismProperty
