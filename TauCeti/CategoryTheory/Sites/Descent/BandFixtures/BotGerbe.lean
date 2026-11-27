/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.SingleObj
public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import TauCeti.CategoryTheory.Sites.Descent.IsGerbe
public import TauCeti.CategoryTheory.Sites.Descent.IsStack

/-!
# Constant gerbes for the bottom topology

For the bottom Grothendieck topology `⊥` on a category `C`, whose only covering sieves are the
maximal ones, every pseudofunctor is a stack (`Pseudofunctor.isStack_bot`), so the constant
pseudofunctor `Pseudofunctor.constant C D` is a gerbe for `⊥` as soon as `D` is a nonempty groupoid
any two of whose objects are isomorphic (`Pseudofunctor.isGerbe_constant`). In particular, on the
point category `Discrete PUnit`, the constant diagram with fibre the one-object groupoid
`Discrete PUnit × SingleObj G` of a group `G` is a gerbe (`BandFixtures.point_connected_gerbe`):
this is the gerbe `B G` on a point used for the fixtures of the intrinsic band of the Stacks
Project, Lemma 8.11.8 (0CJY).

## Main results

* `CategoryTheory.Pseudofunctor.BandFixtures.point_connected_gerbe`: the constant diagram `B G` on
  the point is a gerbe for `⊥`.

## References

* [The Stacks Project, Definition 8.11.1 (06NZ)](https://stacks.math.columbia.edu/tag/06NZ)
* [The Stacks Project, Lemma 8.11.8 (0CJY)](https://stacks.math.columbia.edu/tag/0CJY)
-/

public section

universe u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.BandFixtures

/-- **The constant diagram `B G` on the point is a gerbe**: on `Discrete PUnit` with the bottom
topology, the constant diagram with fibre `Discrete PUnit × SingleObj G` of a group `G` is a
gerbe. -/
instance point_connected_gerbe (G : Type v') [Group G] :
    (constant (Discrete PUnit.{u + 1}) (Discrete PUnit.{u' + 1} × SingleObj G)).IsGerbe ⊥ :=
  isGerbe_constant ⊥ fun x y ↦ ⟨eqToIso (Subsingleton.elim x y)⟩

end CategoryTheory.Pseudofunctor.BandFixtures
