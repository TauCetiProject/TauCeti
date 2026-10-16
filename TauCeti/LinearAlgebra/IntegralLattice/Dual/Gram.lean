/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Dual.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.Gram
public import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.LinearAlgebra.BilinearMap.GramCongruence

/-!
# Gram matrices of dual carriers

The dual carrier of an integral lattice need not have an integral form. Its Gram matrix is
therefore taken over `ℚ`, in the rational extension of an integral basis of the dual carrier.
In the basis dual to a carrier basis, this matrix is the inverse of the original integral
Gram matrix, with its entries cast to `ℚ`.

The signed determinant of the dual Gram matrix is the reciprocal of the signed determinant
of the original lattice. This holds for every integral basis of the dual carrier, including
bases with a different index type. It does not hold for an arbitrary rational ambient basis:
the integral basis hypothesis is what makes the change-of-basis determinant have square one.

## Main results

* `TauCeti.IntegralLattice.extendOfIsLattice_dualCarrierBasis`: the extended dual-carrier basis
  is the bilinear dual of the extended carrier basis.
* `TauCeti.IntegralLattice.toMatrix_dualCarrierBasis`: the inverse Gram matrix identity.
* `TauCeti.IntegralLattice.det_toMatrix_dualCarrier`: the reciprocal determinant in any
  integral basis of the actual dual carrier.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.

The proofs use `LinearMap.BilinForm.toMatrix_dualBasis` and the integral change-of-basis
theorem `LinearMap.det_toMatrix₂Aux_eq_det_toMatrix₂Aux`.
-/

public section

open Module Matrix

namespace TauCeti.IntegralLattice

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (L : IntegralLattice V) [L.IsNondegenerate]

open Classical in
/-- Extending the integral basis of the dual carrier gives the bilinear dual basis of the
extended original carrier basis. -/
@[simp]
theorem extendOfIsLattice_dualCarrierBasis {ι : Type*} [Finite ι]
    (b : Basis ι ℤ L) :
    (L.dualCarrierBasis b).extendOfIsLattice ℚ =
      L.form.dualBasis L.form_nondegenerate (b.extendOfIsLattice ℚ) := by
  classical
  ext i
  simp only [Basis.extendOfIsLattice_apply, dualCarrierBasis_apply, coe_dualBasisElem]

/-- The rational Gram matrix in the actual dual-carrier basis is the inverse of the
integral Gram matrix, with its entries cast to `ℚ`. -/
theorem toMatrix_dualCarrierBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ L) :
    LinearMap.BilinForm.toMatrix ((L.dualCarrierBasis b).extendOfIsLattice ℚ) L.form =
      ((L.gramMatrix b).map (algebraMap ℤ ℚ))⁻¹ := by
  -- The dual-carrier basis uses classical equality on its index type.
  cases Subsingleton.elim ‹DecidableEq ι› (Classical.decEq ι)
  classical
  rw [L.extendOfIsLattice_dualCarrierBasis,
    LinearMap.BilinForm.toMatrix_dualBasis L.form L.form_nondegenerate (b.extendOfIsLattice ℚ),
    ← L.map_gramMatrix b, ← Matrix.transpose_map, (L.isSymm_gramMatrix b).eq]

/-- In any integral basis of the dual carrier, the rational Gram determinant is the
reciprocal of the original signed determinant. No definiteness assumption is needed. -/
theorem det_toMatrix_dualCarrier {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Basis ι ℤ L.dualCarrier) :
    (LinearMap.BilinForm.toMatrix (c.extendOfIsLattice ℚ) L.form).det =
      (L.determinant : ℚ)⁻¹ := by
  -- Align the matrix operations with the classical index equality used by the dual basis.
  cases Subsingleton.elim ‹DecidableEq ι› (Classical.decEq ι)
  classical
  let b := Module.Free.chooseBasis ℤ L
  let B := (L.form.restrictScalars₁₂ ℤ ℤ).compl₁₂
    L.dualCarrier.subtype L.dualCarrier.subtype
  -- Use integral change of basis on the rational-valued restriction, rather than treating
  -- the dual as an integral lattice (its self-pairings may have denominators).
  have hdet : (LinearMap.BilinForm.toMatrix (c.extendOfIsLattice ℚ) L.form).det =
      (LinearMap.BilinForm.toMatrix
        ((L.dualCarrierBasis b).extendOfIsLattice ℚ) L.form).det := by
    convert LinearMap.det_toMatrix₂Aux_eq_det_toMatrix₂Aux B (L.dualCarrierBasis b) c
      using 1 <;> congr 1 <;> ext i j <;>
      simp [B, LinearMap.BilinForm.toMatrix_apply, LinearMap.toMatrix₂Aux_apply]
  rw [hdet, L.toMatrix_dualCarrierBasis, Matrix.det_nonsing_inv,
    L.map_gramMatrix b, ← L.intCast_gramDet b,
    ← L.determinant_eq_gramDet b]
  exact Ring.inverse_eq_inv _

end TauCeti.IntegralLattice
