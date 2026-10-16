/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Split.Basic
public import TauCeti.NumberTheory.IntegralLattice.Binary.Orientation
public import TauCeti.NumberTheory.IntegralLattice.Binary.Examples

/-!
# The hyperbolic plane's principal split proper class

Every orientation of a binary lattice with primitive discriminant one gives the principal
proper class of the split product order. In particular the existing hyperbolic plane has
this class. The computation uses its primitive norm form and the existing proper-class
quotient; it does not pass through a number-field order.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7 (proper-equivalence conventions).
-/

public section
noncomputable section

open Module
open scoped MatrixGroups

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- A binary lattice of primitive discriminant one has the principal split proper class
in every orientation. -/
theorem binaryProperClass_eq_splitPrincipalForm_of_discriminant_eq_one
    (L : IntegralLattice V) (hV : Module.finrank ℚ V = 2)
    (hD : L.binaryDiscriminant hV = 1) (o : Orientation ℤ L (Fin 2)) :
    L.binaryProperClass hV o = Quotient.mk'' BinaryQuadraticForm.splitPrincipalForm := by
  let b := (Module.finBasisOfFinrankEq ℤ L
    (L.finrank_carrier.trans hV)).adjustToOrientation o
  rw [L.binaryProperClass_eq_mk b hV o (Basis.orientation_adjustToOrientation _ _)]
  apply BinaryQuadraticForm.properClass_eq_splitPrincipalForm_of_discrim_eq_one
  exact (L.binaryDiscriminant_eq_discrim_primPart b hV).symm.trans hD

/-- The hyperbolic plane has the principal split proper class, for either orientation. -/
@[simp] theorem hyperbolicPlane_binaryProperClass
    (o : Orientation ℤ hyperbolicPlane (Fin 2)) :
    hyperbolicPlane.binaryProperClass (by simp) o =
      Quotient.mk'' BinaryQuadraticForm.splitPrincipalForm :=
  binaryProperClass_eq_splitPrincipalForm_of_discriminant_eq_one _ _ (by simp) o

end TauCeti.IntegralLattice
