/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.TamelyRamified
public import TauCeti.RingTheory.IntegralClosure.Pi
import Mathlib.RingTheory.Etale.Pi

/-!
# Unramified finite products of field extensions

For a finite product of finite separable extensions of the fraction field of a discrete
valuation ring, the integral closure is étale if and only if every field factor is
unramified with respect to that ring. Thus the factorwise convention for unramified finite
separable algebras agrees with the geometric criterion on their normalization.

This also applies to the empty product, whose integral closure is the zero ring.

## References

* The Stacks Project, Section 58.31, https://stacks.math.columbia.edu/tag/0BSE,
  the extension of ramification terminology to finite separable algebras.
-/

public section

namespace TauCeti.Algebra

variable (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  {ι : Type*} [Finite ι] (L : ι → Type*) [∀ i, Field (L i)]
  [∀ i, Algebra A (L i)] [∀ i, Algebra K (L i)] [∀ i, IsScalarTower A K (L i)]
  [∀ i, FiniteDimensional K (L i)] [∀ i, Algebra.IsSeparable K (L i)]

include K in
/-- For a finite separable algebra presented as a finite product of fields, the normalization
is étale exactly when each field factor is unramified with respect to the discrete valuation
ring. -/
theorem etale_integralClosure_pi_iff :
    Algebra.Etale A (integralClosure A (∀ i, L i)) ↔ ∀ i, IsUnramifiedWRT A (L i) := by
  have (i : ι) : Module.Finite A (integralClosure A (L i)) :=
    IsIntegralClosure.finite A K (L i) _
  have (i : ι) : Algebra.FinitePresentation A (integralClosure A (L i)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · have := h
    have : Algebra.FormallyEtale A (∀ i, integralClosure A (L i)) :=
      Algebra.FormallyEtale.of_equiv (integralClosurePiAlgEquiv A L)
    have := (Algebra.FormallyEtale.pi_iff (R := A) (fun i ↦ integralClosure A (L i))).mp
      inferInstance i
    have : Algebra.Etale A (integralClosure A (L i)) := ⟨inferInstance, inferInstance⟩
    exact (isUnramifiedWRT_iff_etale A K (L i)).mpr inferInstance
  · have (i : ι) : Algebra.Etale A (integralClosure A (L i)) :=
      (isUnramifiedWRT_iff_etale A K (L i)).mp (h i)
    exact Algebra.Etale.of_equiv (integralClosurePiAlgEquiv A L).symm

end TauCeti.Algebra
