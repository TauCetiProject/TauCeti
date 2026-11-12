/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Descent of reducedness at a point along a flat morphism

A flat morphism induces faithfully flat local homomorphisms on stalks. Consequently,
reducedness of a source stalk implies reducedness of the corresponding target stalk.
This permits checking reducedness using flat neighbourhoods, in particular étale charts.

The faithful-flatness argument on stalks follows Mathlib's `epi_of_flat_of_surjective` in
`Mathlib.AlgebraicGeometry.Morphisms.Flat`.
-/

public section

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- Reducedness descends along the local homomorphism on stalks of a flat morphism. -/
theorem isReduced_stalk_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (x : X) [_root_.IsReduced (X.presheaf.stalk x)] :
    _root_.IsReduced (Y.presheaf.stalk (f x)) := by
  algebraize [(f.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap f x) (f.toLRSHom.prop x)
  exact isReduced_of_injective (f.stalkMap x).hom
    ‹RingHom.FaithfullyFlat (f.stalkMap x).hom›.injective

end AlgebraicGeometry.Scheme.Hom
