/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Geometric connectedness of affine products

This file proves that the spectrum of a tensor product of commutative algebras is geometrically
connected when the spectra of both factors are geometrically connected and universally open over
the base, as they always are over a field. The tensor product spectrum is identified with the
fibre product of the two spectra over the base.

## Main declarations

* `TauCeti.geometricallyConnected_respectsIso`: geometric connectedness of morphisms of schemes
  respects isomorphisms.
* `TauCeti.geometricallyConnected_tensorProduct`: the tensor product of two commutative algebras
  with geometrically connected, universally open spectra is geometrically connected.
-/

public section

open CategoryTheory Limits
open scoped TensorProduct

namespace TauCeti

open AlgebraicGeometry

universe u

/-- Geometric connectedness of morphisms of schemes respects isomorphisms, being stable under
base change. -/
instance geometricallyConnected_respectsIso :
    MorphismProperty.RespectsIso @GeometricallyConnected :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

variable {k : Type u} [CommRing k]

/-- The spectrum of a tensor product of commutative `k`-algebras is geometrically connected over
`k` when the spectra of both factors are geometrically connected and universally open over `k`.
Universal openness is automatic when `k` is a field. -/
theorem geometricallyConnected_tensorProduct
    (S T : Type u) [CommRing S] [CommRing T] [Algebra k S] [Algebra k T]
    [UniversallyOpen (Spec.map (CommRingCat.ofHom (algebraMap k S)))]
    [UniversallyOpen (Spec.map (CommRingCat.ofHom (algebraMap k T)))]
    (hS : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k S))))
    (hT : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k T)))) :
    GeometricallyConnected
      (Spec.map (CommRingCat.ofHom (algebraMap k (S ⊗[k] T)))) := by
  rw [← MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected
    (pullbackSpecIso k S T).hom, pullbackSpecIso_hom_base]
  exact .comp _ _

end TauCeti
