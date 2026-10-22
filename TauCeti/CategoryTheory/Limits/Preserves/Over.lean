/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.VanKampen
public import Mathlib.CategoryTheory.Extensive

/-!
# Base change preserves universal colimits

For `f : X ⟶ Y`, base change `Over.pullback f : Over Y ⥤ Over X` is a right adjoint, so it
preserves limits, but in general it need not preserve colimits. A colimit cocone in `C` is
*universal* (`CategoryTheory.IsUniversalColimit`) when every base change of it is again a colimit
cocone. This file records that base change of objects over a base preserves colimits of every
shape `J` whose colimits in `C` are universal.

In a finitary pre-extensive category, such as the category of schemes, finite coproducts are
universal, so base change preserves finite coproducts.

## Main results

* `CategoryTheory.Over.isPullback_pullback_map_left`: base change of a morphism over `Y` along
  `f` is a pullback of that morphism.
* `CategoryTheory.Over.preservesColimitsOfShape_pullback`: if colimits of shape `J` in `C` exist
  and are universal, then `Over.pullback f` preserves colimits of shape `J`.
* `CategoryTheory.Over.preservesFiniteCoproducts_pullback`: in a finitary pre-extensive category,
  base change preserves finite coproducts.
-/

public section

universe v u

namespace CategoryTheory

open Limits

namespace Over

variable {C : Type u} [Category.{v} C] {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]

/-- For a morphism `g : A ⟶ B` over `Y`, its base change along `f`, followed by the first
projections to `A` and `B`, is a pullback square:
```
A ×_Y X ⟶ B ×_Y X
   ↓          ↓
   A    ⟶    B
```
-/
theorem isPullback_pullback_map_left {A B : Over Y} (g : A ⟶ B) :
    IsPullback ((pullback f).map g).left (Limits.pullback.fst A.hom f)
      (Limits.pullback.fst B.hom f) g.left :=
  -- Paste with the pullback square of `B.hom` and `f`; the outer rectangle is the pullback
  -- square of `A.hom = g.left ≫ B.hom` and `f`, after `simp` evaluates the composites.
  IsPullback.of_right (by simpa using IsPullback.of_hasPullback A.hom f |>.flip) (by simp)
    (IsPullback.of_hasPullback B.hom f).flip

/-- If colimits of shape `J` in `C` exist and are universal, then base change along `f`
preserves colimits of shape `J`. -/
theorem preservesColimitsOfShape_pullback {J : Type*} [Category J] [HasColimitsOfShape J C]
    (H : ∀ {K : J ⥤ C} {c : Cocone K}, IsColimit c → IsUniversalColimit c) :
    PreservesColimitsOfShape J (pullback f) where
  preservesColimit {K} := ⟨fun {c} hc ↦ ⟨by
    -- Over the base change, the first projections form a natural transformation to the
    -- underlying diagram, all of whose naturality squares are pullbacks.
    let α : (K ⋙ pullback f) ⋙ forget X ⟶ K ⋙ forget Y :=
      { app j := Limits.pullback.fst (K.obj j).hom f
        naturality _ _ g := by simp }
    refine isColimitOfReflects (forget X)
      (H (isColimitOfPreserves (forget Y) hc) _ α (Limits.pullback.fst c.pt.hom f) ?_
        (fun _ _ g ↦ isPullback_pullback_map_left f (K.map g))
        (fun j ↦ isPullback_pullback_map_left f (c.ι.app j))).some
    ext j
    simp [α]⟩⟩

/-- In a finitary pre-extensive category, base change preserves finite coproducts. -/
instance preservesFiniteCoproducts_pullback [FinitaryPreExtensive C] :
    PreservesFiniteCoproducts (pullback f) where
  preserves _ :=
    preservesColimitsOfShape_pullback f FinitaryPreExtensive.isUniversal_finiteCoproducts

end Over

end CategoryTheory
