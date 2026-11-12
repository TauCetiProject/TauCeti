/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.ProjectiveOrbit.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Orbit
import TauCeti.Algebra.AlgebraicGroup.Smooth.CharZero

/-!
# Smooth adjoint orbits and their relative dimension

For a finite-type affine group over an algebraically closed field of characteristic zero, the
adjoint orbit of `x` is smooth of relative dimension `dim [𝔤, x]`. This concerns the existing
locally closed scheme model of the orbit of `(x, 1)` in the projective completion of `𝔤`, which
represents the homogeneous quotient by the scheme-theoretic centralizer of `x`.

`TauCeti.smoothOfRelativeDimension_adjointOrbit` combines smoothness of the
projective orbit with the adjoint orbit dimension formula. Cartier's theorem supplies the
required reducedness of the acting group. Connectedness, semisimplicity, adjointness, and
nilpotence of `x` are not required. In particular the theorem applies to the zero orbit and to
nilpotent orbits of semisimple groups.

This is a smoothness and dimension statement about the orbit scheme. It does not identify its
tangent map with the bracket, or assert that its inclusion in the Lie algebra is smooth.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, Chapter 1.
* J. E. Humphreys, *Linear Algebraic Groups*, GTM 21, §8.3.
-/

public section

open AlgebraicGeometry

namespace TauCeti

universe u

variable {k H : Type u} [Field k] [IsAlgClosed k] [CharZero k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H]

attribute [local instance] Derivation.adjointComodule Comodule.prodTrivial

/-- The adjoint orbit of `x` is smooth of relative dimension `dim [𝔤, x]`. This holds for any
finite-type affine group in characteristic zero, without assuming it connected or reductive. -/
instance smoothOfRelativeDimension_adjointOrbit
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    SmoothOfRelativeDimension
      (Module.finrank k (LinearMap.range
        (LieAlgebra.ad k (Module.Dual k (Bialgebra.CotangentSpace k H)) x)))
      (Comodule.projectiveOrbitToSpec (H := H)
        ((x, 1) : Module.Dual k (Bialgebra.CotangentSpace k H) × k)
        (Module.isUnimodular_mk_one x)) := by
  have := HopfAlgebra.isReduced_of_charZero k H
  exact (Comodule.smoothOfRelativeDimension_projectiveOrbitToSpec_iff _ _ _).mpr
    (topologicalKrullDim_range_projectiveOrbitMap_mk_one_eq_finrank_range_ad x)

end TauCeti
