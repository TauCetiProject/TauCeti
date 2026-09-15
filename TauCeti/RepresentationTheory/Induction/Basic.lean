/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Induced

/-!
# General facts about induced representations

Mathlib's `Rep.ind φ` induces a representation along an arbitrary homomorphism of groups
`φ : G →* H`, and `Rep.indMap φ` induces an intertwiner along it. This file collects the
general properties of that construction that Mathlib does not record and that the rest of
`TauCeti/RepresentationTheory/Induction/` needs, independently of any finiteness assumption
on the groups or on the representations.

## Main statements

* `Rep.indMap_add`: inducing an intertwiner along `φ` is additive, and `Rep.indFunctor_additive`:
  the same fact as a `CategoryTheory.Functor.Additive` instance for `Rep.indFunctor`.
-/

public section

open CategoryTheory

universe u v w w'

namespace Rep

/-- **Induction of intertwiners is additive**: for any homomorphism of groups `φ : G →* H`,
`Rep.indMap φ (f + g) = Rep.indMap φ f + Rep.indMap φ g`. -/
theorem indMap_add {k : Type u} {G : Type v} {H : Type w} [CommRing k] [Group G] [Group H]
    (φ : G →* H) {A B : Rep.{w'} k G} (f g : A ⟶ B) :
    Rep.indMap φ (f + g) = Rep.indMap φ f + Rep.indMap φ g := by
  ext h a
  simp [Rep.indMap, Rep.add_hom]

/-- **Induction along a homomorphism of groups is an additive functor**, the functorial form of
`Rep.indMap_add`. -/
instance indFunctor_additive {k : Type u} {G : Type v} {H : Type w} [CommRing k] [Group G]
    [Group H] (φ : G →* H) :
    ((Rep.indFunctor k φ : Rep.{w'} k G ⥤ Rep k H)).Additive where
  map_add {_ _} f g := indMap_add φ f g

end Rep
