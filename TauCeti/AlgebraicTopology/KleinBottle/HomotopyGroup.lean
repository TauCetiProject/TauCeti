/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.Geometry.Manifold.Instances.KleinBottle
import TauCeti.Analysis.Complex.Circle.Basic
import TauCeti.AlgebraicTopology.EilenbergMacLane.HomotopyEquiv
import TauCeti.AlgebraicTopology.EilenbergMacLane.MappingTorus
import TauCeti.AlgebraicTopology.UniversalCover.Circle.EilenbergMacLane

/-!
# The Klein bottle is aspherical

The Klein bottle is the smooth mapping torus of complex conjugation of the circle
(`TauCeti.KleinBottle`). Since the circle is aspherical, so is the Klein bottle
(`TauCeti.KleinBottle.isAspherical`, from `TauCeti.IsAspherical.smoothMappingTorus`): all its
homotopy groups of dimension at least two vanish, and every power map, squaring in particular, is
surjective on them (`TauCeti.KleinBottle.surjective_pow_homotopyGroup`). This is the example
showing that the hypothesis of Theorems 5.15 and C of Barraud, Damian, Humilière and Oancea on
closed characteristics in cotangent bundles of non-orientable manifolds, that squaring is not
surjective on some higher homotopy group, is needed: it fails for the Klein bottle, and so does
their conclusion, since the flat unit cotangent bundle of the Klein bottle carries no contractible
closed characteristic (a fact not proved here). For real projective space `RPⁿ` with `n ≥ 2`
the hypothesis holds (`TauCeti.RealProjectiveSpace.not_surjective_pow_homotopyGroup`).

## Main results

* `TauCeti.KleinBottle.isAspherical`: the Klein bottle is aspherical.
* `TauCeti.KleinBottle.surjective_pow_homotopyGroup`: every power map is surjective on the higher
  homotopy groups of the Klein bottle.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.B (`K(G, 1)`
  spaces).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Theorems 5.15 and C.
-/

public section

open scoped Topology Topology.Homotopy

namespace TauCeti

namespace KleinBottle

attribute [local instance] finrank_real_complex_fact'

/-- **The Klein bottle is aspherical**: it is the smooth mapping torus of complex conjugation of
the circle, which is aspherical. -/
theorem isAspherical (z : KleinBottle) : IsAspherical KleinBottle z :=
  ((Circle.isAspherical 1).of_homotopyEquiv Circle.homeomorphSphere.toHomotopyEquiv
    1).smoothMappingTorus conjCircleDiffeomorph z

/-- **Every power map is surjective on the higher homotopy groups of the Klein bottle**, since they
are trivial. For `d = 2` this says that `π_(n + 2)(K) ⊗ ℤ/2` vanishes for the Klein bottle `K`. -/
theorem surjective_pow_homotopyGroup (z : KleinBottle) (n d : ℕ) :
    Function.Surjective fun a : π_ (n + 2) KleinBottle z ↦ a ^ d :=
  (isAspherical z).surjective_pow_homotopyGroup n d

end KleinBottle

end TauCeti
