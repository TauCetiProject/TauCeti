/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Actions on an essentially small category are essentially small

If `V` is essentially small, so is the category `CategoryTheory.Action V G` of `G`-actions on
objects of `V`. The object type of `Action V G` is not small merely because `V` is essentially
small (an object carries an object of `V` together with a monoid homomorphism
`G →* CategoryTheory.End _`), but up to isomorphism it is: `Action V G` is equivalent to a small
category.

The smallness universe is `max v z`, where `V` is essentially small in universe `z` and `G` lives
in `Type v`. It cannot be lowered to `z` in general: for `V` a small model of finite sets and `G`
an elementary abelian `2`-group of large rank, the actions of `G` on a two-element set are the
homomorphisms `G →* Multiplicative (ZMod 2)`, pairwise non-isomorphic and too many to be
`z`-small. The universe `z` is independent of the morphism universe `w` of `V`.

This supplies the smallness hypothesis of `TauCeti.SplitK0` for `FDRep k G`, used by the
representation ring `TauCeti.repRing`.

## Main statements

* `CategoryTheory.Action.essentiallySmall`: actions of a monoid on an essentially small category
  form an essentially small category.

## Implementation notes

Mathlib's `CategoryTheory.Action.functorCategoryEquivalence` identifies `Action V G` with the
functor category `SingleObj G ⥤ V`. Replacing `V` by `CategoryTheory.SmallModel V` along
`CategoryTheory.equivSmallModel` gives a functor category out of a one-object category into a
small one, which is essentially small in universe `max v z` by instance search, and smallness
transports back along `CategoryTheory.essentiallySmall_congr`.
-/

public section

universe u v w z

namespace CategoryTheory

namespace Action

/-- **Actions on an essentially small category are essentially small.** If `V` is essentially
small in universe `z`, then the category of actions on objects of `V` of a monoid `G : Type v` is
essentially small in universe `max v z`. -/
instance essentiallySmall {V : Type u} [Category.{w} V] [EssentiallySmall.{z} V] (G : Type v)
    [Monoid G] : EssentiallySmall.{max v z} (Action V G) :=
  (essentiallySmall_congr ((Action.functorCategoryEquivalence V G).trans
    (equivSmallModel V).congrRight)).2 inferInstance

end Action

end CategoryTheory
