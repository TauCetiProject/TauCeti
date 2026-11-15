/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Generated.Basic
public import TauCeti.Algebra.AlgebraicGroup.Smooth.CommHopfAlgCat
import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.Smooth
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Smoothness of the generated short-root type-G2 subgroup after scalar extension

After extending the coordinate maps of the four numbered root subgroups and the rank-two weight
torus of the short-root type-`G₂` carrier over `𝔽₃` to any commutative `𝔽₃`-algebra, their
common-kernel quotient is smooth. It is reduced when the base algebra is reduced.

## Main declarations

In the namespace `TauCeti.G2ShortRoot.PrimeField`:

* `smoothCommHopfAlgProperty_generatedCoordinateHopfAlgebra`: smoothness over any commutative
  `𝔽₃`-algebra.
* `isReduced_generatedCoordinateHopfAlgebra`: reducedness over any reduced commutative
  `𝔽₃`-algebra.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §§26–27.
* J. S. Milne, *Algebraic Groups* (2017), §2.h.

The interface follows the generated-subgroup smoothness construction for the type-`E₇`
minuscule carrier in `TauCeti.Algebra.Lie.E7.Minuscule.Generated.Smooth`.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

universe u

variable (k : Type u) [CommRing k] [Algebra (ZMod 3) k]

/-- The subgroup generated after scalar extension is smooth over any commutative base algebra. -/
theorem smoothCommHopfAlgProperty_generatedCoordinateHopfAlgebra :
    smoothCommHopfAlgProperty k (generatedCoordinateHopfAlgebra k) := by
  apply (smoothCommHopfAlgProperty k).prop_of_iso (coordinateHopfAlgebraGeneratedIso k)
  exact (smoothCommHopfAlgProperty_iff _).mpr inferInstance

/-- The subgroup generated after scalar extension has reduced coordinate algebra when the base
algebra is reduced. -/
theorem isReduced_generatedCoordinateHopfAlgebra [IsReduced k] :
    IsReduced (generatedCoordinateHopfAlgebra k) := by
  let _ : Algebra.Smooth k (generatedCoordinateHopfAlgebra k) :=
    (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_generatedCoordinateHopfAlgebra k)
  exact isReduced_of_smooth k _

end TauCeti.G2ShortRoot.PrimeField
