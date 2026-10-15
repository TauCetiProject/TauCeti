/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import TauCeti.AlgebraicGeometry.RelativeSpec.Functor

/-!
# Base change of affine schemes over a scheme

An affine morphism remains affine after arbitrary base change. Consequently, pulling back a
scheme affine over `X` along `f : Y ⟶ X` gives a scheme affine over `Y`. This file packages
that construction as the functor `baseChangeAffineSchemeOver`.

This functor is part of the contravariant pseudofunctoriality of affine schemes over varying bases.
It is the geometric input for the theorem that relative spectrum commutes with arbitrary base
change.

The construction specializes Mathlib's pullback functor on morphism-property over-categories to
the property `IsAffineHom`; no new choice of fibre product is made.

## Main declaration

* `TauCeti.AlgebraicGeometry.baseChangeAffineSchemeOver`: base change of affine schemes over a
  fixed base.

## References

* The Stacks Project, Tag 01SD (affine morphisms are stable under base change).
-/

public section

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}}

local instance (f : Y ⟶ X) :
    MorphismProperty.HasPullbacksAlong
      (@IsAffineHom : MorphismProperty Scheme.{u}) f where
  hasPullback _ _ := inferInstance

local instance (f : Y ⟶ X) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsAffineHom : MorphismProperty Scheme.{u}) f where
  of_isPullback h hg := isAffineHom_isStableUnderBaseChange.of_isPullback h hg

/-- Pullback of schemes affine over `X` along an arbitrary morphism `f : Y ⟶ X`.

The underlying scheme is the chosen fibre product, and its structure morphism is the second
projection to `Y`. -/
abbrev baseChangeAffineSchemeOver (f : Y ⟶ X) :
    AffineSchemeOver X ⥤ AffineSchemeOver Y :=
  MorphismProperty.Over.pullback (@IsAffineHom : MorphismProperty Scheme.{u}) ⊤ f

/-- The induced map between base changes commutes with projection to the original total spaces. -/
@[simp]
theorem baseChangeAffineSchemeOver_map_left_fst (f : Y ⟶ X) {V W : AffineSchemeOver X}
    (g : V ⟶ W) :
    ((baseChangeAffineSchemeOver f).map g).left ≫ pullback.fst W.hom f =
      pullback.fst V.hom f ≫ g.left :=
  -- The generated `MorphismProperty.Over.pullback_map_left` does not rewrite here: `@IsAffineHom`
  -- only has type `MorphismProperty Scheme` after unfolding the semireducible `MorphismProperty`,
  -- so the rewrite fails to match. The map is identified with `pullback.lift` by unfolding.
  pullback.lift_fst _ _ _

/-- The induced map between base changes lies over the identity of the new base. -/
@[simp]
theorem baseChangeAffineSchemeOver_map_left_snd (f : Y ⟶ X) {V W : AffineSchemeOver X}
    (g : V ⟶ W) :
    ((baseChangeAffineSchemeOver f).map g).left ≫ pullback.snd W.hom f =
      pullback.snd V.hom f :=
  -- Definitional unfolding, as in `baseChangeAffineSchemeOver_map_left_fst`.
  pullback.lift_snd _ _ _

end

end TauCeti.AlgebraicGeometry
