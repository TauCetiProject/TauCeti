/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.CommaSites

/-!
# Base change of restricted sites on `P.Over ⊤ X`

Let `P` be a morphism property on a category `C` and `J` a Grothendieck topology on `C`. The
forgetful functor `Over.forget P ⊤ X : P.Over ⊤ X ⥤ Over X` endows `P.Over ⊤ X` with the
restricted topology `(Over.forget P ⊤ X).restrictedTopology (J.over X)` (the construction used by
`AlgebraicGeometry.Scheme.smallGrothendieckTopology`).

This file proves that for a morphism `f : X ⟶ Y` along which morphisms in `P` admit pullbacks and
remain in `P`, base change `Over.pullback P ⊤ f : P.Over ⊤ Y ⥤ P.Over ⊤ X` is cover-preserving
whenever `Over.forget P ⊤ Y` is locally cover-dense for `J.over Y`, and continuous whenever
`Over.pullback P ⊤ f` is moreover representably flat (in particular when `C` has pullbacks and `P`
is multiplicative, stable under base change, and post-cancellative).
-/

public section

namespace CategoryTheory.MorphismProperty.Over

open Category Limits

variable {C : Type*} [Category* C]

/-- When `C` has pullbacks and `P` is multiplicative, stable under base change, and
post-cancellative, `Over.pullback P ⊤ f` is representably flat because `P.Over ⊤ Y` has finite
limits and `Over.pullback P ⊤ f` preserves them. -/
instance representablyFlat_pullback (P : MorphismProperty C) [HasPullbacks C]
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    {X Y : C} (f : X ⟶ Y) :
    RepresentablyFlat (Over.pullback P ⊤ f) :=
  flat_of_preservesFiniteLimits _

/-- Base change `Over.pullback P ⊤ f : P.Over ⊤ Y ⥤ P.Over ⊤ X` preserves covering sieves for the
restricted topologies induced from `J.over Y` and `J.over X`, provided `Over.forget P ⊤ Y` is
locally cover-dense for `J.over Y`. -/
theorem coverPreserving_pullback_restrictedTopology (P : MorphismProperty C)
    (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [(Over.forget P ⊤ Y).LocallyCoverDense (J.over Y)] :
    CoverPreserving
      ((Over.forget P ⊤ Y).restrictedTopology (J.over Y))
      ((Over.forget P ⊤ X).restrictedTopology (J.over X))
      (Over.pullback P ⊤ f) where
  cover_preserve {V S} hS := by
    apply Functor.mem_restrictedTopology_of_functorPushforward_mem
    have hSY : Sieve.overEquiv ((Over.forget P ⊤ Y).obj V)
        (S.functorPushforward (Over.forget P ⊤ Y)) ∈
          J ((Over.forget P ⊤ Y).obj V).left := by
      rw [← GrothendieckTopology.mem_over_iff, ← Functor.mem_restrictedTopology_iff]
      exact hS
    rw [GrothendieckTopology.mem_over_iff]
    refine J.superset_covering ?_ (J.pullback_stable (Limits.pullback.fst V.hom f) hSY)
    intro T t ht
    dsimp [Sieve.overEquiv] at ht ⊢
    rw [← Sieve.functorPushforward_comp] at ht
    rw [← Sieve.functorPushforward_comp, ← Sieve.functorPushforward_comp]
    rcases ht with ⟨W, g, u, hg, hu⟩
    have hw : u ≫ W.hom = (t ≫ Limits.pullback.snd V.hom f) ≫ f :=
      (congrArg (u ≫ ·) (Over.w g).symm).trans
        (((assoc u g.left V.hom).symm.trans (congrArg (· ≫ V.hom) hu.symm)).trans
          ((assoc t _ V.hom).trans
            ((congrArg (t ≫ ·) Limits.pullback.condition).trans (assoc t _ f).symm)))
    refine ⟨W, g, Limits.pullback.lift u (t ≫ Limits.pullback.snd V.hom f) hw, hg, ?_⟩
    apply Limits.pullback.hom_ext
    · exact ((assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (Limits.pullback.lift_fst _ _ _)).trans
          (((assoc _ _ _).symm.trans
            (congrArg (· ≫ g.left) (Limits.pullback.lift_fst _ _ _))).trans hu.symm))).symm
    · exact ((assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (Limits.pullback.lift_snd _ _ _)).trans
          (Limits.pullback.lift_snd _ _ _))).symm

/-- Base change `Over.pullback P ⊤ f : P.Over ⊤ Y ⥤ P.Over ⊤ X` is continuous for the restricted
topologies induced from `J.over Y` and `J.over X` whenever `Over.forget P ⊤ Y` is locally
cover-dense for `J.over Y` and `Over.pullback P ⊤ f` is representably flat. -/
instance isContinuous_pullback_restrictedTopology (P : MorphismProperty C)
    (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y)
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f]
    [(Over.forget P ⊤ Y).LocallyCoverDense (J.over Y)]
    [RepresentablyFlat (Over.pullback P ⊤ f)] :
    (Over.pullback P ⊤ f).IsContinuous
      ((Over.forget P ⊤ Y).restrictedTopology (J.over Y))
      ((Over.forget P ⊤ X).restrictedTopology (J.over X)) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ _)
    (coverPreserving_pullback_restrictedTopology P J f)

end CategoryTheory.MorphismProperty.Over
