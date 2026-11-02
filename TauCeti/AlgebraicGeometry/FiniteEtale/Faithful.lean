/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Basic
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Faithfulness of finite étale base change

Pullback of finite étale schemes along a dominant morphism is faithful. In particular,
restriction to a dense open subscheme determines every morphism between finite étale covers.
The base and covers may be nonreduced.

The statement uses Mathlib's morphism-property over category, with all morphisms over the base.
This is the same finite étale carrier described by `finiteEtaleSchemeProperty_eq_overObj`.
The source cover is open over the base, so dominance survives its base change. The relative
equalizer into the target cover is both open and closed, hence a dominant such equalizer is
an isomorphism.

The proof uses Mathlib's `MorphismProperty.Over.pullback` and its map computation,
`Scheme.Pullback.range_fst`, and Tau Ceti's relative unramified equalizer API.
-/

open CategoryTheory Limits

public section

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Base change of finite étale schemes along a dominant morphism is faithful, including over
nonreduced bases. -/
theorem finiteEtalePullback_faithful {S T : Scheme.{u}} (f : T ⟶ S) [IsDominant f] :
    letI : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
    (MorphismProperty.Over.pullback
      (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) ⊤ f).Faithful := by
  -- Specify the intersection when applying Mathlib's `inf` instance, as in `FiniteEtale.Limits`.
  let : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
  refine ⟨fun {X Y} a b hab ↦ ?_⟩
  have : Etale X.hom := X.prop.2
  have : IsFinite Y.hom := Y.prop.1
  have : Etale Y.hom := Y.prop.2
  have : IsDominant (pullback.fst X.hom f) :=
    IsDominant.pullback_fst_of_isOpenMap X.hom f X.hom.isOpenMap
  apply MorphismProperty.Over.Hom.ext
  apply ext_of_isDominant_of_isSeparated_of_formallyUnramified Y.hom
    ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm) (pullback.fst X.hom f)
  have heq := congrArg (fun k ↦ k.left ≫ pullback.fst Y.hom f) hab
  -- Matching the property intersection in a rewrite requires more transparency than `rw`:
  -- apply the characteristic equation of the pullback lift directly instead.
  have hmap (k : X ⟶ Y) :
      ((MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ f).map k).left ≫
        pullback.fst Y.hom f = pullback.fst X.hom f ≫ k.left :=
    pullback.lift_fst _ _ _
  exact (hmap a).symm.trans (heq.trans (hmap b))

end AlgebraicGeometry.Scheme.Hom
