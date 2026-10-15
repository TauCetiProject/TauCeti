/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.GroupScheme
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Flat

/-!
# Flatness of the integral type-E6 minuscule carrier

The full-weight type-`E₆` minuscule carrier has scalar-torsion-free coordinate algebra and
is consequently flat over `ℤ`. This is a property of the integral carrier itself, before
specializing to any field. It does not assert smoothness of its fibers or identify it with
the pinned simply connected group scheme of type `E₆`.

The result applies the flatness criterion for integral Kostant toral closures to
`TauCeti.E6Minuscule.definingIdeal`.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §26.
* The Stacks Project, [Tag 0AUW](https://stacks.math.columbia.edu/tag/0AUW), for flatness
  of torsion-free modules over Dedekind domains.
-/

public section

namespace TauCeti.E6Minuscule

-- Match the module used by the integral coordinate-algebra quotient.
attribute [local instance high] Algebra.toModule

/-- The integral full-weight type-`E₆` minuscule carrier has no scalar torsion in its
coordinate algebra. In particular its coordinate algebra is flat over `ℤ`. -/
instance isTorsionFree_integralCoordinateHopfAlgebra :
    Module.IsTorsionFree ℤ
      (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ 27) definingIdeal) := by
  rw [definingIdeal_def]
  infer_instance

end TauCeti.E6Minuscule
