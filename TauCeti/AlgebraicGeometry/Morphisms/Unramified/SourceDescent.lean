/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Unramified.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.StalkMap

/-!
# Descent of unramifiedness along flat source covers

Let `g : X' ⟶ X` be flat and surjective and let `f : X ⟶ Y` be locally of finite type. If
`g ≫ f` is unramified, then `f` is unramified. No quasi-compactness assumption on `g` is
needed.

The descent takes place on the source, rather than after base change on the target. It is
`AlgebraicGeometry.FormallyUnramified.of_comp_surjective`, which works on stalks: the local flat
map induced by `g` is faithfully flat, and formal unramifiedness descends by
`Scheme.Hom.formallyUnramified_stalkMap_of_comp`. This applies in particular to the map on
singular subschemes induced by an étale surjection of relative curves.

## References

* The Stacks Project, Tag 02G4: unramified morphisms.
* The Stacks Project, Tag 0C58: families of nodal curves.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- Unramifiedness of a morphism locally of finite type descends along a flat surjection
of its source, without a quasi-compactness hypothesis on the cover. -/
theorem Unramified.of_comp_surjective {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Flat g] [Surjective g] [LocallyOfFiniteType f] [Unramified (g ≫ f)] :
    Unramified f where
  toFormallyUnramified := FormallyUnramified.of_comp_surjective g f

end TauCeti.AlgebraicGeometry
