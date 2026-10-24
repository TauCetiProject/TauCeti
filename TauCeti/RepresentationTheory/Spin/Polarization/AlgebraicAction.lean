/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.OfAssociative
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic
public import TauCeti.RepresentationTheory.Spin.Polarization.CliffordAction

/-!
# The algebraic bivector action on spinors

The Fock action of a polarized Clifford algebra is an algebra homomorphism into endomorphisms.
This file records the resulting commutator formula for a normalized Clifford bivector acting on
a vector generator. It is the coordinate-free bridge from the Clifford commutator calculation to
the creation, contraction, and parity operators on the spinor module.

The formula is independent of finite-dimensionality, nondegeneracy, and a choice of basis. -/

public section

open CliffordAlgebra QuadraticMap

namespace TauCeti

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [CommRing K] [Invertible (2 : K)]
  {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- The Fock action carries the normalized Clifford bivector bracket on a vector generator to the
commutator of the corresponding creation, contraction, and parity operators. -/
theorem spinAction_bivector_lie_ι (P : SpinPolarizationData Q) (a b x : V) :
    ⁅spinAction Q P (bivector Q a b), spinAction Q P (ι Q x)⁆ =
      spinAction Q P (ι Q (polar Q b x • a - polar Q a x • b)) := by
  have h := (spinAction Q P).toLieHom.map_lie (bivector Q a b) (ι Q x)
  rw [bivector_lie_ι] at h
  simpa only [AlgHom.toLieHom_apply] using h.symm

end TauCeti
