/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Isogeny.Basic

/-!
# Base change of group-scheme isogenies

Isogenies of group schemes remain isogenies after arbitrary base change: finiteness, flatness and
surjectivity of the underlying scheme morphism are each stable under base change. The group-scheme
base change is the pullback functor on the over category, lifted to group objects.

## Main declarations

* `TauCeti.GroupScheme.IsIsogeny.baseChange`: isogenies remain isogenies after arbitrary base
  change.

## References

* J. S. Milne, *Algebraic Groups* (2017), §18.a.
-/

-- The base-change argument follows `TauCeti.AlgebraicGeometry.AbelianVariety.IsIsogeny.baseChange`.

public section

open CategoryTheory

namespace TauCeti.GroupScheme

open AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} {G H : Grp (Over X)}

/-- Arbitrary base change preserves group-scheme isogenies. -/
theorem IsIsogeny.baseChange (s : Y ⟶ X) {f : G ⟶ H} (hf : IsIsogeny f) :
    IsIsogeny ((Over.pullback s).mapGrp.map f) := by
  rw [isIsogeny_iff, Functor.mapGrp_map_hom_hom]
  exact ⟨MorphismProperty.overPullbackMap _ _ hf.isFinite,
    MorphismProperty.overPullbackMap _ _ hf.flat,
    MorphismProperty.overPullbackMap _ _ hf.surjective⟩

end TauCeti.GroupScheme
