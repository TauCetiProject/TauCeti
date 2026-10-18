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

The counit of a commutative bialgebra over a field defines a point of its prime spectrum. For a
Hopf algebra, this is the identity point of the represented affine group.

## Main declarations

* `TauCeti.Bialgebra.augmentationPoint`: the point of the affine spectrum defined by the counit.
-/

public section

open AlgebraicGeometry

namespace TauCeti.Bialgebra

universe u v

variable (k : Type u) [Field k]
variable (H : Type v) [CommRing H] [Bialgebra k H]

/-- The point of `Spec H` defined by the counit of a commutative bialgebra. For a Hopf algebra,
this is the identity point of the represented affine group. -/
abbrev augmentationPoint : Spec (CommRingCat.of H) :=
  AlgHom.kernelPoint (_root_.Bialgebra.counitAlgHom k H)

/-- The augmentation point belongs to a basic open exactly when the counit is nonzero on
its defining element. Use for explicit rewriting; general kernel-point simplification already
handles this case. -/
theorem augmentationPoint_mem_basicOpen_iff (a : H) :
    (augmentationPoint k H : PrimeSpectrum H) ∈ PrimeSpectrum.basicOpen a ↔
      _root_.Bialgebra.counitAlgHom k H a ≠ 0 :=
  _root_.AlgHom.kernelPoint_mem_basicOpen_iff _ a

end TauCeti.Bialgebra
