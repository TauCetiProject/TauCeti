/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Split.Composition
public import TauCeti.NumberTheory.IntegralLattice.Binary.Orientation
public import TauCeti.NumberTheory.IntegralLattice.Binary.Examples

/-!
# The hyperbolic plane's principal split proper class

Every orientation of a binary lattice with primitive discriminant one gives the principal
proper class of the split product order. In particular the existing hyperbolic plane has
this class. The primitive norm form also defines a class in the primitive split quotient,
whose forgetful image is the existing oriented proper class. For the hyperbolic plane this
is the triangular principal class with coefficients `1, 1`, the composition identity, and its module
is the unit module over the actual product order. No number-field order is used.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7 (proper-equivalence conventions).
-/

public section
noncomputable section

open Module
open scoped MatrixGroups

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The primitive norm form of an oriented binary lattice of nonzero square discriminant,
as a split proper class. -/
def binarySplitProperClass (L : IntegralLattice V) (hV : Module.finrank ℚ V = 2)
    (s : ℕ) [NeZero s] (hD : L.binaryDiscriminant hV = (s : ℤ) ^ 2)
    (o : Orientation ℤ L (Fin 2)) : BinaryQuadraticForm.SplitProperClass s := by
  let b := (Module.finBasisOfFinrankEq ℤ L
    (L.finrank_carrier.trans hV)).adjustToOrientation o
  have hd : (L.binaryNormForm b).primPart.discrim = (s : ℤ) ^ 2 :=
    (L.binaryDiscriminant_eq_discrim_primPart b hV).symm.trans hD
  refine Quotient.mk _ ⟨(L.binaryNormForm b).primPart,
    (BinaryQuadraticForm.mem_primitiveForms _ _).mpr ⟨hd, ?_⟩⟩
  apply BinaryQuadraticForm.isPrimitive_primPart
  intro hz
  have hs : (s : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr (NeZero.ne s))
  apply hs
  simpa [hz, BinaryQuadraticForm.discrim_def, discrim] using hd.symm

/-- Forgetting the square-discriminant restriction recovers the existing oriented proper class. -/
@[simp] theorem binarySplitProperClass_toProperClass
    (L : IntegralLattice V) (hV : Module.finrank ℚ V = 2) (s : ℕ) [NeZero s]
    (hD : L.binaryDiscriminant hV = (s : ℤ) ^ 2) (o : Orientation ℤ L (Fin 2)) :
    BinaryQuadraticForm.splitProperClassToProperClass s (L.binarySplitProperClass hV s hD o) =
      L.binaryProperClass hV o := by
  let b := (Module.finBasisOfFinrankEq ℤ L
    (L.finrank_carrier.trans hV)).adjustToOrientation o
  simpa only [binarySplitProperClass, b,
    BinaryQuadraticForm.splitProperClassToProperClass_mk] using
    (L.binaryProperClass_eq_mk b hV o (Basis.orientation_adjustToOrientation _ _)).symm

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

/-- The hyperbolic plane's primitive norm form gives the principal triangular split class. -/
theorem hyperbolicPlane_binarySplitProperClass (o : Orientation ℤ hyperbolicPlane (Fin 2)) :
    hyperbolicPlane.binarySplitProperClass (by simp) 1 (by simp) o =
      BinaryQuadraticForm.splitProperClassMk 1 1 isCoprime_one_right := by
  apply BinaryQuadraticForm.splitProperClassToProperClass_injective 1
  rw [binarySplitProperClass_toProperClass, hyperbolicPlane_binaryProperClass,
    BinaryQuadraticForm.splitProperClassToProperClass_splitProperClassMk]
  simpa only [Nat.cast_one, BinaryQuadraticForm.splitPrincipalForm_def,
    BinaryQuadraticForm.splitTriangularForm_def] using
    (BinaryQuadraticForm.properClass_splitTriangularForm_eq_iff 1 0 1 one_ne_zero).mpr
      (one_dvd _)

/-- The existing raw proper class of the hyperbolic plane is the image of its principal
split proper class. -/
theorem hyperbolicPlane_binaryProperClass_eq_splitProperClassMk
    (o : Orientation ℤ hyperbolicPlane (Fin 2)) :
    hyperbolicPlane.binaryProperClass (by simp) o =
      BinaryQuadraticForm.splitProperClassToProperClass 1
        (BinaryQuadraticForm.splitProperClassMk 1 1 isCoprime_one_right) := by
  rw [← binarySplitProperClass_toProperClass hyperbolicPlane (by simp) 1 (by simp) o,
    hyperbolicPlane_binarySplitProperClass]

/-- The hyperbolic plane gives the identity for split proper-class composition. -/
@[simp] theorem hyperbolicPlane_binarySplitProperClass_eq_one
    (o : Orientation ℤ hyperbolicPlane (Fin 2)) :
    hyperbolicPlane.binarySplitProperClass (by simp) 1 (by simp) o = 1 := by
  rw [hyperbolicPlane_binarySplitProperClass, BinaryQuadraticForm.splitProperClassMk_one]

/-- The hyperbolic plane's split class maps to the actual product order's unit module. -/
theorem hyperbolicPlane_splitProperClassModule
    (o : Orientation ℤ hyperbolicPlane (Fin 2)) :
    BinaryQuadraticForm.splitProperClassModule 1
      (hyperbolicPlane.binarySplitProperClass (by simp) 1 (by simp) o) = 1 := by
  rw [hyperbolicPlane_binarySplitProperClass_eq_one, map_one]

end TauCeti.IntegralLattice
