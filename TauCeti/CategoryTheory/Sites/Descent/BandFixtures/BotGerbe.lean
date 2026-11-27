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
maximal ones, every pseudofunctor is a stack (`Pseudofunctor.isStack_bot`). The constant
pseudofunctor `Pseudofunctor.constant C D` is a gerbe for any topology for which it is a stack, in
particular for `⊥`, as soon as `D` is a nonempty groupoid any two of whose objects are isomorphic
(`BandFixtures.isGerbe_constant`). In particular, on the point category `Discrete PUnit`, the
constant diagram with fibre the one-object groupoid `Discrete PUnit × SingleObj G` of a group `G`
is a gerbe (`BandFixtures.point_connected_gerbe`): this is the gerbe `B G` on a point used for the
fixtures of the intrinsic band of the Stacks Project, Lemma 8.11.8 (0CJY).

## Main results

In the namespace `CategoryTheory.Pseudofunctor.BandFixtures`:

* `isGerbe_constant`: a constant diagram with a nonempty connected groupoid fibre is a gerbe for
  any topology for which it is a stack.
* `point_connected_gerbe`: the constant diagram `B G` on the point is a gerbe for `⊥`.

## References

* [The Stacks Project, Definition 8.11.1 (06NZ)](https://stacks.math.columbia.edu/tag/06NZ)
* [The Stacks Project, Lemma 8.11.8 (0CJY)](https://stacks.math.columbia.edu/tag/0CJY)
-/

public section

universe v u v' u'

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.BandFixtures

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- **A constant diagram with a nonempty connected groupoid fibre is a gerbe** for any topology
`J` for which it is a stack: its fibres are groupoids, the maximal sieve has an object over every
arrow, and any two objects of the fibre are isomorphic. For `J = ⊥` the stack property is
`isStack_bot`. -/
theorem isGerbe_constant (J : GrothendieckTopology C) [(constant C D).IsStack J] [IsGroupoid D]
    [Nonempty D] (h : ∀ x y : D, Nonempty (x ≅ y)) : (constant C D).IsGerbe J where
  isGroupoid _ := inferInstanceAs (IsGroupoid D)
  exists_covering_nonempty U := ⟨⊤, J.top_mem U, fun _ _ _ ↦ inferInstanceAs (Nonempty D)⟩
  exists_covering_iso x y := ⟨⊤, J.top_mem _, fun _ _ _ ↦ h x y⟩

/-- **The constant diagram `B G` on the point is a gerbe**: on `Discrete PUnit` with the bottom
topology, the constant diagram with fibre `Discrete PUnit × SingleObj G` of a group `G` is a
gerbe. -/
instance point_connected_gerbe (G : Type v') [Group G] :
    (constant (Discrete PUnit.{u + 1}) (Discrete PUnit.{u' + 1} × SingleObj G)).IsGerbe ⊥ :=
  isGerbe_constant ⊥ fun x y ↦ ⟨eqToIso (Subsingleton.elim x y)⟩

end CategoryTheory.Pseudofunctor.BandFixtures
