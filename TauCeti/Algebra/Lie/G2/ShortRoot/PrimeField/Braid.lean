/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.G2.ShortRoot.PrimeField.PointsFunctor
import TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Braid

/-!
# The Weyl braid relation in the characteristic-three short-root G₂ carrier

The numbered rank-one root words of the subgroup generated over `𝔽₃` satisfy the
length-six G₂ braid relation on every commutative value algebra. The integral calculation
in `TauCeti.Algebra.Lie.G2.ShortRoot.IntegralToralClosure.Braid` transfers through the
faithful matrix realizations of the two carriers. It requires neither equality of the
generated carrier with the specialization of the integral closure nor reducedness of
the value algebra.

This is a relation between explicit root words. It does not identify the carrier with
an independently pinned simply connected group scheme.

## References

* R. Steinberg, *Lectures on Chevalley Groups* (1968), §6.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.
-/

public section

namespace TauCeti.G2ShortRoot.PrimeField

open Multiplicative

/-- The pinned rank-one root words of the short-root G₂ carrier over `𝔽₃` satisfy the
length-six braid relation over arbitrary commutative value algebras, including nonreduced ones. -/
theorem rootSubgroupPoints_braid (A : Type*) [CommRing A] [Algebra (ZMod 3) A] :
    let n := fun i : Fin 2 =>
      rootSubgroupPoints (.inl i) A (ofAdd 1) *
        rootSubgroupPoints (.inr i) A (ofAdd (-1)) *
          rootSubgroupPoints (.inl i) A (ofAdd 1)
    (n 0 * n 1) ^ 3 = (n 1 * n 0) ^ 3 := by
  apply Subtype.ext
  simpa only [Subgroup.subtype_apply, Subgroup.coe_pow, Subgroup.coe_mul,
    coe_rootSubgroupPoints] using
    congrArg (IntegralToralClosure.points A).subtype
      (IntegralToralClosure.rootSubgroupPoints_braid A)

end TauCeti.G2ShortRoot.PrimeField
