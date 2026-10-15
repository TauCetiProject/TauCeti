/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Functoriality of group cohomology

This file evaluates Mathlib's pullback `groupCohomology.mapCocycles₂` of a `2`-cocycle along a
compatible pair `(f, φ)` at a pair of group elements, without unfolding the cochain map.

## Main statements

* `TauCeti.groupCohomology.mapCocycles₂_apply`: the value of a pulled-back `2`-cocycle.
-/

public section

universe u

open Rep

namespace TauCeti.groupCohomology

open _root_.groupCohomology

variable {k G : Type u} [CommRing k] [Group G]

/-- The pullback of a `2`-cocycle `c` along a compatible pair `(f, φ)` takes the value
`φ (c (f g₁, f g₂))` at `(g₁, g₂)`. Not `@[simp]`: `simp` first rewrites the left-hand side by
Mathlib's `groupCohomology.coe_mapCocycles₂`. -/
theorem mapCocycles₂_apply {H : Type u} [Group H] {A : Rep k H} {B : Rep k G}
    (f : G →* H) (φ : res f A ⟶ B) (c : cocycles₂ A) (q : G × G) :
    (mapCocycles₂ f φ c : G × G → B) q = φ.hom (c (f q.1, f q.2)) :=
  (rfl)

end TauCeti.groupCohomology
