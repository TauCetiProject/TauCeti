/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.BottPeriodicity
public import TauCeti.LinearAlgebra.CliffordAlgebra.Zero
public import TauCeti.LinearAlgebra.Matrix.Pauli
public import TauCeti.Algebra.Quaternion.ComplexMatrix

/-!
# Pauli models of the real Clifford planes

The positive plane has a real matrix model with ordered generators
`X = !![0, 1; 1, 0]` and `Z = !![1, 0; 0, -1]`. The universal Clifford map is an
isomorphism: every real two-by-two matrix is a unique combination of `1, X, Z, XZ`.
`realCliffordTwoZeroEquivPauli_symm_apply` gives its inverse in these coordinates.
After complexifying its matrix entries, its vector formula agrees with the existing
Pauli map. This is exactly the signature-switch classifier after removing its scalar tensor factor.

For the negative plane, the existing quaternion classifier followed by
`Quaternion.toComplexMatrix` sends the ordered generators to `iZ, iY`, and their
product to `iX`. Thus the two plane models use the same Pauli convention while
retaining their different real algebras and signs.

The positive model uses `TauCeti.realCliffordSignatureSwitchRecurrenceEquiv` and
`CliffordAlgebra.equivOfSubsingleton`. The negative comparison uses
`TauCeti.realCliffordZeroTwoEquivQuaternion`, `Quaternion.toComplexMatrix` and `TauCeti.pauli`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §§1 and 4.
-/

public section

open Matrix CliffordAlgebra

namespace TauCeti

local instance : Subsingleton (Fin (0 + 0) → ℝ) :=
  ⟨fun _ _ ↦ funext fun i ↦ Fin.elim0 i⟩

/-- The real Pauli model of the positive Clifford plane, with generators `e₁ ↦ X`,
`e₂ ↦ Z`. In particular the ordered bivector maps to `XZ = !![0, -1; 1, 0]`.
This is the signature-switch model with its scalar tensor factor removed. -/
noncomputable def realCliffordTwoZeroEquivPauli :
    CliffordAlgebra (realCliffordForm 2 0) ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  (realCliffordSignatureSwitchRecurrenceEquiv 0 0).trans
    ((Algebra.TensorProduct.congr (R := ℝ) (S := ℝ)
      (equivOfSubsingleton (realCliffordForm 0 0))
      (AlgEquiv.refl : Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] _)).trans
      (Algebra.TensorProduct.lid ℝ _))

/-- The Pauli model agrees exactly with the signature-switch classifier, after the canonical
identifications `Cl(0,0) ≃ ℝ` and `ℝ ⊗ M₂(ℝ) ≃ M₂(ℝ)`. -/
theorem realCliffordTwoZeroEquivPauli_eq_signatureSwitch
    (a : CliffordAlgebra (realCliffordForm 2 0)) :
    realCliffordTwoZeroEquivPauli a =
      (Algebra.TensorProduct.lid ℝ (Matrix (Fin 2) (Fin 2) ℝ))
        ((Algebra.TensorProduct.congr (R := ℝ) (S := ℝ)
          (equivOfSubsingleton (realCliffordForm 0 0))
          (AlgEquiv.refl : Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] _))
          (realCliffordSignatureSwitchRecurrenceEquiv 0 0 a)) := (rfl)

/-- The positive-plane Pauli model on an arbitrary real vector. -/
@[simp]
theorem realCliffordTwoZeroEquivPauli_ι (v : Fin 2 → ℝ) :
    realCliffordTwoZeroEquivPauli (ι (realCliffordForm 2 0) v) =
      !![v 1, v 0; v 0, -v 1] := by
  -- The coordinate lemmas use cast indices. Specialize them to the two coordinates before
  -- simplifying the scalar tensor factor and the matrix product in the classifier.
  have hb (w : Fin 2 → ℝ) : (realBottSplitIsometry 0 0 w).2 = w := by
    ext i
    fin_cases i
    · exact realBottSplitIsometry_snd_zero 0 0 w
    · exact realBottSplitIsometry_snd_one 0 0 w
  have hs (x : Fin 1 → ℝ) (r : ℝ) :
      realCliffordSignSwitchStandardIsometry 1 0 (x, r) = ![r, x 0] := by
    ext i
    fin_cases i
    · exact realCliffordSignSwitchStandardIsometry_last_pos 1 0 x r
    · exact realCliffordSignSwitchStandardIsometry_neg_of_pos 1 0 x r 0
  have hp0 : (realCliffordPositiveSplitIsometry 1 0 v).1 0 = v 0 :=
    realCliffordPositiveSplitIsometry_fst_pos 1 0 v 0
  have hp1 : (realCliffordPositiveSplitIsometry 1 0 v).2 = v 1 :=
    realCliffordPositiveSplitIsometry_snd 1 0 v
  rw [realCliffordTwoZeroEquivPauli_eq_signatureSwitch,
    realCliffordSignatureSwitchRecurrenceEquiv_ι]
  simp only [realCliffordBottEquiv_ι, hb, hs]
  simp [hp0, hp1]

/-- The inverse Pauli model expresses a matrix in the Clifford basis `1, e₁, e₂, e₁e₂`. -/
theorem realCliffordTwoZeroEquivPauli_symm_apply (A : Matrix (Fin 2) (Fin 2) ℝ) :
    realCliffordTwoZeroEquivPauli.symm A =
      ((A 0 0 + A 1 1) / 2) • 1 +
      ((A 0 1 + A 1 0) / 2) • ι (realCliffordForm 2 0) (Pi.single 0 1) +
      ((A 0 0 - A 1 1) / 2) • ι (realCliffordForm 2 0) (Pi.single 1 1) +
      ((A 1 0 - A 0 1) / 2) •
        (ι (realCliffordForm 2 0) (Pi.single 0 1) *
          ι (realCliffordForm 2 0) (Pi.single 1 1)) := by
  apply realCliffordTwoZeroEquivPauli.injective
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp <;> ring

/-- Entrywise scalar extension of the positive-plane model gives the existing Pauli map
on the `X,Z` coordinate plane. -/
theorem map_realCliffordTwoZeroEquivPauli_ι (v : Fin 2 → ℝ) :
    (realCliffordTwoZeroEquivPauli (ι (realCliffordForm 2 0) v)).map
        (algebraMap ℝ ℂ) = pauli ![v 0, 0, v 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli_apply]

/-- The quaternion model of the negative plane has Pauli generators `e₁ ↦ iZ`, `e₂ ↦ iY`.
The map is an embedding of real algebras, rather than an isomorphism onto all complex matrices. -/
theorem toComplexMatrix_realCliffordZeroTwoEquivQuaternion_ι (v : Fin 2 → ℝ) :
    Quaternion.toComplexMatrix
        (realCliffordZeroTwoEquivQuaternion (ι (realCliffordForm 0 2) v)) =
      Complex.I • pauli ![0, v 1, v 0] := by
  rw [realCliffordZeroTwoEquivQuaternion_ι, Quaternion.toComplexMatrix_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauli_apply, Complex.ext_iff]

/-- The ordered negative-plane bivector maps to `iX`, fixing the order of the Pauli triple. -/
theorem toComplexMatrix_realCliffordZeroTwoEquivQuaternion_ι_mul_ι :
    Quaternion.toComplexMatrix (realCliffordZeroTwoEquivQuaternion
      (ι (realCliffordForm 0 2) (Pi.single 0 1) *
        ι (realCliffordForm 0 2) (Pi.single 1 1))) =
      Complex.I • pauli ![1, 0, 0] := by
  rw [map_mul, map_mul, toComplexMatrix_realCliffordZeroTwoEquivQuaternion_ι,
    toComplexMatrix_realCliffordZeroTwoEquivQuaternion_ι]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli_apply, Matrix.mul_apply, Fin.sum_univ_two]

end TauCeti
