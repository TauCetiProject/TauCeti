/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Spin.Polarization.TypeB.CartanWeights

/-!
# The formal character of the type-B spinor module

The exterior spinor module for a polarized odd-dimensional quadratic space has formal character
equal to the sum of all half-integer sign-vector weights, each with multiplicity one. Here the
weights are linear forms on the concrete diagonal Cartan, through `typeBWeightEquiv`, and the
character is the canonical `TauCeti.formalCharacter`, defined by generalized weight-space
dimensions. Thus this formula connects the Clifford construction to the Lie-module character API.

The formula holds over any field in which two is invertible, including positive characteristic.
No choice of a positive root system or highest vector is needed. It includes rank zero, when the
exterior algebra is the ground field and its only weight is zero.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), §20.1–20.2.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I §5.
-/

public section

open LieModule Module

namespace TauCeti.SpinPolarizationData

universe u v w

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} (P : SpinPolarizationData Q)
  {ι : Type w} [Fintype ι] [LinearOrder ι] (b : Module.Basis ι K P.W)
  (z : P.line) (hz : Q (z : V) = 1) [Invertible (2 : K)]

/-- The type-`B` spinor character is the sum of all half-integer sign-vector weights, each
with multiplicity one, regarded as linear forms on the diagonal Cartan. -/
theorem formalCharacter_typeBSpinLieRep :
    letI : LieRingModule (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
      LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    letI : LieModule K (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
      LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
    letI : Module.Finite K (ExteriorAlgebra K P.W) :=
      Module.Finite.of_basis b.ExteriorAlgebra
    formalCharacter K (typeBDiagonalCartan K ι) (ExteriorAlgebra K P.W) =
      ∑ s : Finset ι, AddMonoidAlgebra.single (typeBWeightEquiv (spinWeight K s)) (1 : ℤ) := by
  let _ : LieRingModule (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
    LieRingModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  let _ : LieModule K (LieAlgebra.Orthogonal.typeB ι K) (ExteriorAlgebra K P.W) :=
    LieModule.compLieHom _ (P.typeBSpinLieRep b z hz)
  let _ : Module.Finite K (ExteriorAlgebra K P.W) :=
    Module.Finite.of_basis b.ExteriorAlgebra
  apply b.ExteriorAlgebra.formalCharacter_eq_sum_single_of_weight_basis
    (μ := fun s => typeBWeightEquiv (spinWeight K s))
  intro s A
  exact P.typeBSpinLieRep_apply_cartan_exteriorBasis b z hz A s

end TauCeti.SpinPolarizationData
