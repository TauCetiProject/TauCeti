/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Syntomic
public import TauCeti.RingTheory.Node.Syntomic

/-!
# Node charts are syntomic

For any commutative ring `R` and parameter `a`, the structure morphism of
`Spec R[x,y]/(xy-a)` is syntomic of relative dimension one. This includes the crossing
`xy=0` and all smoothing parameters, without reducedness assumptions on the base.
Together with the singular-locus calculation, this is the complete-intersection part
of the nodal-curve criterion.

## References

* Stacks Project, Example 55.14.1, Tag 0CDC.
-/

public section

open AlgebraicGeometry TauCeti.AlgebraicGeometry

namespace TauCeti.NodeAlgebra

universe u

/-- The node chart `xy = a` is syntomic of relative dimension one over any base ring. -/
instance syntomicOfRelativeDimension_spec {R : Type u} [CommRing R] (a : R) :
    SyntomicOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap R (NodeAlgebra R a)))) :=
  syntomicOfRelativeDimension_SpecMap R (NodeAlgebra R a)

end TauCeti.NodeAlgebra
