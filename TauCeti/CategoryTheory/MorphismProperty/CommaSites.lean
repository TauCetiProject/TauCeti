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
* **Iterated slice equivalence of sites**: for `U : P.Over ⊤ X`, the slice equivalence
  `Over.iteratedSliceEquiv U : CategoryTheory.Over U ≌ P.Over ⊤ U.left` is a dense-subsite
  equivalence between `(((Over.forget P ⊤ X).restrictedTopology (J.over X)).over U)` and
  `(Over.forget P ⊤ U.left).restrictedTopology (J.over U.left)`. Consequently it induces an
  equivalence of sheaf categories (`overRestrictedSheafEquiv`) under which the over-site restriction
  `overPullback` identifies with pushforward along `Over.map ⊤ U.prop`.
* **Cover-preservation and continuity of `Over.map`**: for a morphism `f : Y ⟶ X` satisfying `P`,
  `Over.map ⊤ hf` is cover-preserving and continuous for the restricted over topologies.
* **Cover-preservation and continuity of `Over.pullback`**: when `C` has pullbacks and `P` is
  multiplicative, stable under base change, and satisfies post-cancellation, `Over.pullback P ⊤ f`
  is representably flat, cover-preserving, and continuous for the restricted over topologies.
-/

public section

namespace CategoryTheory.MorphismProperty

open Limits

section IteratedSlice

variable {C : Type*} [Category* C] (J : GrothendieckTopology C)
  {P : MorphismProperty C} [P.IsStableUnderComposition] [P.HasOfPostcompProperty P]
  {X : C}

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
      ← Sieve.functorPushforward_comp, Functor.mem_restrictedTopology_iff,
      GrothendieckTopology.mem_over_iff, Sieve.overEquiv_apply, ← Sieve.functorPushforward_comp,
      ← Sieve.functorPushforward_comp, Functor.mem_restrictedTopology_iff,
      GrothendieckTopology.mem_over_iff, Sieve.overEquiv_apply, ← Sieve.functorPushforward_comp]
    rfl

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

/-- For a morphism `f : Y ⟶ X` satisfying `P`, post-composition `Over.map ⊤ hf` is continuous for
the restricted over topologies. -/
lemma isContinuous_over_map {Y : C} {f : Y ⟶ X} (hf : P f)
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ Y).LocallyCoverDense (J.over Y)] :
    (Over.map (P := P) ⊤ hf).IsContinuous
      ((Over.forget P ⊤ Y).restrictedTopology (J.over Y))
      ((Over.forget P ⊤ X).restrictedTopology (J.over X)) :=
  have : (Over.forget P ⊤ (Over.mk ⊤ f hf).left).LocallyCoverDense
      (J.over (Over.mk ⊤ f hf).left) := by
    rw [Over.mk_left]
    infer_instance
  have : (Over.iteratedSliceBackward (Over.mk ⊤ f hf)).IsContinuous
      ((Over.forget P ⊤ Y).restrictedTopology (J.over Y))
      (((Over.forget P ⊤ X).restrictedTopology (J.over X)).over (Over.mk ⊤ f hf)) :=
    isContinuous_iteratedSliceBackward J (Over.mk ⊤ f hf)
  Functor.isContinuous_comp (Over.iteratedSliceBackward (Over.mk ⊤ f hf))
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
  cover_preserve hS := by
    rw [Functor.mem_restrictedTopology_iff, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv_apply, ← Sieve.functorPushforward_comp] at hS
    rw [Functor.mem_restrictedTopology_iff, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv_apply, ← Sieve.functorPushforward_comp, ← Sieve.functorPushforward_comp]
    exact hS

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

/-- Under `overRestrictedSheafEquiv`, restricting a sheaf on `P.Over ⊤ X` to the slice over `U`
identifies with pushing it forward along `Over.map ⊤ U.prop : P.Over ⊤ U.left ⥤ P.Over ⊤ X`. -/
noncomputable def overPullbackCompOverRestrictedSheafEquivIso
    (U : P.Over ⊤ X) (A : Type*) [Category* A]
    [(Over.forget P ⊤ X).LocallyCoverDense (J.over X)]
    [(Over.forget P ⊤ U.left).LocallyCoverDense (J.over U.left)] :
    haveI := isContinuous_over_map (X := X) (Y := U.left) (f := U.hom) J U.prop
    ((Over.forget P ⊤ X).restrictedTopology (J.over X)).overPullback A U ⋙
        (overRestrictedSheafEquiv J U A).functor ≅
      (Over.map (f := U.hom) ⊤ U.prop).sheafPushforwardContinuous A
        ((Over.forget P ⊤ U.left).restrictedTopology (J.over U.left))
        ((Over.forget P ⊤ X).restrictedTopology (J.over X)) :=
  haveI := isContinuous_over_map (X := X) (Y := U.left) (f := U.hom) J U.prop
  NatIso.ofComponents
    (fun F ↦ ObjectProperty.isoMk _ (Iso.refl ((Over.map (f := U.hom) ⊤ U.prop).op ⋙ F.obj)))
    (fun φ ↦ by ext V; exact (Category.comp_id _).trans (Category.id_comp _).symm)

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

/-- Base change `Over.pullback P ⊤ f` is continuous for the restricted over topologies. -/
lemma isContinuous_over_pullback [HasPullbacks C] [P.IsMultiplicative]
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
