/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Basic
public import TauCeti.AlgebraicGeometry.AugmentationPoint.Basic

/-!
# The augmentation point of a commutative bialgebra

The counit of a commutative bialgebra over an integral domain defines a point of its prime
spectrum. For a Hopf algebra over a field, this is the identity point of the represented affine
group.

## Main declarations

* `TauCeti.Bialgebra.augmentationPoint`: the point of the affine spectrum defined by the counit.
-/

public section

open AlgebraicGeometry

namespace TauCeti.Bialgebra

universe u v

variable (k : Type u) [CommRing k] [IsDomain k]
variable (H : Type v) [CommRing H] [Bialgebra k H]

/-- The point of `Spec H` defined by the counit of a commutative bialgebra over an integral
domain. For a Hopf algebra over a field, this is the identity point of the represented affine
group. -/
abbrev augmentationPoint : Spec (CommRingCat.of H) :=
  AlgHom.kernelPoint (_root_.Bialgebra.counitAlgHom k H)

end TauCeti.Bialgebra
