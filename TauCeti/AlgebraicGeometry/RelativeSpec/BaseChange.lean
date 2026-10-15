/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import TauCeti.AlgebraicGeometry.RelativeSpec.Functor

/-!
# Base change of affine schemes over a scheme

An affine morphism remains affine after arbitrary base change. Consequently, pulling back a
scheme affine over `X` along `f : Y ⟶ X` gives a scheme affine over `Y`. This file packages
that construction as the functor `baseChangeAffineSchemeOver` and records its composition
comparison.

This comparison is part of the contravariant pseudofunctoriality of affine schemes over varying
bases. The functor is the geometric input for the theorem that relative spectrum commutes with
arbitrary base change.

The construction specializes Mathlib's pullback functor on morphism-property over-categories to
the property `IsAffineHom`; no new choice of fibre product is made.

## Main declarations

* `TauCeti.AlgebraicGeometry.baseChangeAffineSchemeOver`: base change of affine schemes over a
  fixed base;
* `TauCeti.AlgebraicGeometry.baseChangeAffineSchemeOverComp`: base change along a composite.

## References

* The Stacks Project, Tag 01SD (affine morphisms are stable under base change).
-/

public section

open CategoryTheory Limits
open _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {X Y Z : Scheme.{u}}

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

/-- The total space of a base-changed affine scheme is the fibre product. -/
@[simp]
theorem baseChangeAffineSchemeOver_obj_left (f : Y ⟶ X) (V : AffineSchemeOver X) :
    ((baseChangeAffineSchemeOver f).obj V).left = pullback V.hom f :=
  (rfl)

/-- The structure morphism of a base-changed affine scheme is the second fibre-product
projection. -/
@[simp]
theorem baseChangeAffineSchemeOver_obj_hom (f : Y ⟶ X) (V : AffineSchemeOver X) :
    ((baseChangeAffineSchemeOver f).obj V).hom = pullback.snd V.hom f :=
  (rfl)

/-- Base change sends a morphism over `X` to the induced morphism of fibre products. -/
theorem baseChangeAffineSchemeOver_map_left (f : Y ⟶ X) {V W : AffineSchemeOver X}
    (g : V ⟶ W) :
    ((baseChangeAffineSchemeOver f).map g).left =
      pullback.lift (pullback.fst V.hom f ≫ g.left) (pullback.snd V.hom f)
        (by rw [Category.assoc, MorphismProperty.Over.w g, pullback.condition]) :=
  (rfl)

/-- The induced map between base changes commutes with projection to the original total spaces. -/
@[simp]
theorem baseChangeAffineSchemeOver_map_left_fst (f : Y ⟶ X) {V W : AffineSchemeOver X}
    (g : V ⟶ W) :
    ((baseChangeAffineSchemeOver f).map g).left ≫ pullback.fst W.hom f =
      pullback.fst V.hom f ≫ g.left := by
  rw [baseChangeAffineSchemeOver_map_left]
  exact pullback.lift_fst _ _ _

/-- The induced map between base changes lies over the identity of the new base. -/
@[simp]
theorem baseChangeAffineSchemeOver_map_left_snd (f : Y ⟶ X) {V W : AffineSchemeOver X}
    (g : V ⟶ W) :
    ((baseChangeAffineSchemeOver f).map g).left ≫ pullback.snd W.hom f =
      pullback.snd V.hom f := by
  rw [baseChangeAffineSchemeOver_map_left]
  exact pullback.lift_snd _ _ _

/-- Base change along a composite is naturally isomorphic to successive base change. -/
def baseChangeAffineSchemeOverComp (f : Y ⟶ X) (g : Z ⟶ Y) :
    baseChangeAffineSchemeOver (g ≫ f) ≅
      baseChangeAffineSchemeOver f ⋙ baseChangeAffineSchemeOver g :=
  MorphismProperty.Over.pullbackComp (P := @IsAffineHom) (Q := ⊤) g f

/-- The composition comparison is the canonical associativity isomorphism of fibre products. -/
@[reassoc (attr := simp)]
theorem baseChangeAffineSchemeOverComp_hom_app_left_fst_fst
    (f : Y ⟶ X) (g : Z ⟶ Y) (V : AffineSchemeOver X) :
    ((baseChangeAffineSchemeOverComp f g).hom.app V).left ≫
        pullback.fst (pullback.snd V.hom f) g ≫ pullback.fst V.hom f =
      pullback.fst V.hom (g ≫ f) :=
  MorphismProperty.Over.pullbackComp_left_fst_fst
    (P := @IsAffineHom) (Q := ⊤) g f V

/-- The composition comparison lies over the identity of the final base. -/
@[simp]
theorem baseChangeAffineSchemeOverComp_hom_app_left_snd
    (f : Y ⟶ X) (g : Z ⟶ Y) (V : AffineSchemeOver X) :
    ((baseChangeAffineSchemeOverComp f g).hom.app V).left ≫
        pullback.snd (pullback.snd V.hom f) g =
      pullback.snd V.hom (g ≫ f) :=
  MorphismProperty.Over.w ((baseChangeAffineSchemeOverComp f g).hom.app V)

end

end TauCeti.AlgebraicGeometry
