/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Lie.OfAssociative
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic
public import TauCeti.RepresentationTheory.Spin.Polarization.CliffordAction

/-!
# The algebraic bivector action on spinors

The Fock action of a polarized Clifford algebra is an algebra homomorphism into endomorphisms.
This file records the resulting commutator formula for a normalized Clifford bivector acting on
a vector generator, obtained by transporting the generic algebra-map identity through `spinAction`.

The formula is independent of finite-dimensionality, nondegeneracy, and a choice of basis.

## References

* `CliffordAlgebra.map_bivector_lie_ι` in
  `TauCeti/LinearAlgebra/CliffordAlgebra/Bivector/Basic.lean` transports the Clifford commutator
  through any algebra homomorphism.
* `TauCeti.spinAction_bivector_lie_ι` specializes that identity to the Fock action. -/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [CommRing K] [Invertible (2 : K)]
  {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- The commutator of the Fock operators of a normalized Clifford bivector and a vector generator is
the Fock operator of the infinitesimal rotation
`polar Q b x • a - polar Q a x • b` of `x`. -/
@[grind =]
theorem spinAction_bivector_lie_ι (P : SpinPolarizationData Q) (a b x : V) :
    ⁅spinAction Q P (bivector Q a b), spinAction Q P (ι Q x)⁆ =
      spinAction Q P (ι Q (polar Q b x • a - polar Q a x • b)) := by
  exact CliffordAlgebra.map_bivector_lie_ι Q (spinAction Q P) a b x

end TauCeti
