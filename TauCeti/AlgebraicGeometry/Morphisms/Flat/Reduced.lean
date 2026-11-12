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
  have := Flat.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := by
    rw [RingHom.algebraMap_toAlgebra]
    infer_instance
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact isReduced_of_injective (algebraMap _ (X.presheaf.stalk x))
    (FaithfulSMul.algebraMap_injective _ _)

end AlgebraicGeometry.Scheme.Hom
