/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Node.BranchSequence
public import TauCeti.RingTheory.Smooth.GeometricallyReduced
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Reduced coordinate algebras of nodes

The split node over a reduced ring is reduced, since it embeds in the product of its two
polynomial branch algebras. Over a field every smoothing `xy = a` is reduced: the case `a = 0`
is the split node, while for nonzero `a` the algebra is smooth. These facts supply reduced
geometric fibres for the standard nodal chart.

## References

* The Stacks Project, Section 53.19, *Nodal curves*, Tag 0C46.
-/

public section

namespace TauCeti.NodeAlgebra

variable (R : Type*) [CommRing R]

/-- The split node over a reduced ring is reduced. -/
instance isReduced_zero [IsReduced R] : IsReduced (NodeAlgebra R 0) := by
  have : IsReduced (Polynomial R) := isReduced_of_injective
    (MvPolynomial.uniqueAlgEquiv.{_, 0} R PUnit).symm
    (MvPolynomial.uniqueAlgEquiv.{_, 0} R PUnit).symm.injective
  exact isReduced_of_injective (branchMap R) (branchMap_injective R)

/-- Every node smoothing over a field is reduced. -/
instance isReduced_of_field {K : Type*} [Field K] (a : K) : IsReduced (NodeAlgebra K a) := by
  by_cases ha : a = 0
  · subst a
    infer_instance
  · have : Algebra.IsStandardSmooth K (NodeAlgebra K a) :=
      (isStandardSmoothOfRelativeDimension_of_isUnit a (isUnit_iff_ne_zero.mpr ha)).isStandardSmooth
    exact TauCeti.isReduced_of_smooth K (NodeAlgebra K a)

end TauCeti.NodeAlgebra
