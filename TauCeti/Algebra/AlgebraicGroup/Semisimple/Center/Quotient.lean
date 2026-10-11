/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Semisimple.Center.Finite
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.ShortExact
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The central isogeny to the quotient by the center

For a semisimple affine group `G` over a field, the projection `G → G/Z(G)` is a central
isogeny. The quotient is the affine group represented by the coinvariants of the defining
Hopf ideal of the scheme-theoretic center. The normal-quotient theorem identifies its functor
of points with the fppf quotient sheaf; the finite-center theorem makes the projection finite.

The full scheme-theoretic center is used, including its infinitesimal structure in positive
characteristic. Neither perfection of the field nor reducedness of the center is assumed.
This constructs the central isogeny used to obtain the adjoint form. Semisimplicity and
triviality of the center of the quotient are separate statements.

## Main declaration

* `TauCeti.semisimpleCommHopfAlgProperty.isCentralIsogeny_coinvariantsι_centerDefiningIdeal`:
  the projection from a semisimple affine group to its affine center quotient is a central
  isogeny.

## References

* J. S. Milne, *Algebraic Groups* (2017), §21.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§15–16.
-/

public section

namespace TauCeti.semisimpleCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The projection from a semisimple affine group to the affine quotient by its full
scheme-theoretic center is a central isogeny. The quotient coordinate algebra is the
center-coinvariant Hopf subalgebra; the coordinate arrow therefore points towards `H`.
The center may be nonreduced, and the ground field need not be perfect. -/
theorem isCentralIsogeny_coinvariantsι_centerDefiningIdeal
    (hH : semisimpleCommHopfAlgProperty k H) :
    CommHopfAlgCat.IsCentralIsogeny
      (CommHopfAlgCat.coinvariantsι
        (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj).isNormal) := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  exact CommHopfAlgCat.isCentralIsogeny_coinvariantsι
    (CommHopfAlgCat.isCentral_centerDefiningIdeal H.obj) hH.moduleFinite_centerCoordinate

end TauCeti.semisimpleCommHopfAlgProperty
