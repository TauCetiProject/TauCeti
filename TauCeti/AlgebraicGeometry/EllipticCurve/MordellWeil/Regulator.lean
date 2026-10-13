/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.PointModTorsion
-- The Gram-congruence lemmas are used only inside the proofs below, so the import is private:
-- nothing in this module's exported statements mentions `toMatrix₂Aux`.
import TauCeti.LinearAlgebra.BilinearMap.GramCongruence
import TauCeti.LinearAlgebra.Matrix.Northcott

/-!
# The regulator of an elliptic curve

The regulator is the absolute value of the determinant of the Néron-Tate pairing's Gram matrix
on a basis of the points modulo torsion. It does not depend on the basis chosen: a change of
basis transforms the Gram matrix by congruence, `G' = Mᵀ G M`, along the integer change-of-basis
matrix `M`. The two bases need not be indexed by the same type, in which case `M` is rectangular
and has no determinant; the absolute determinant is invariant all the same, because the index
types of two bases of the same module are equivalent.

## Main definitions

* `WeierstrassCurve.Affine.regulator`: the regulator of a curve whose points modulo torsion are
  finitely generated as a `ℤ`-module.

## Main results

* `WeierstrassCurve.Affine.neronTateGramMatrix_basis_change`: a change of basis acts on the
  Gram matrix by congruence.
* `WeierstrassCurve.Affine.abs_det_neronTateGramMatrix_basis_change`: the absolute determinant is
  independent of the basis, including of its index type.
* `WeierstrassCurve.Affine.regulator_eq_abs_det_neronTateGramMatrix`: the regulator is computed
  by any basis whatsoever.
* `WeierstrassCurve.Affine.regulator_eq_one_of_finrank_eq_zero`: the rank-zero convention.
* `WeierstrassCurve.Affine.regulator_nonneg`: the regulator is non-negative.
* `WeierstrassCurve.Affine.regulator_pos`: under Northcott finiteness, the regulator is positive.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.9, where the canonical
  height and its associated pairing are constructed; the regulator is the determinant of that
  pairing's Gram matrix on a basis of the free quotient.
-/

public section

open Height Matrix

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : Affine F} [AdmissibleAbsValues F] [DecidableEq F]

-- `neronTateGramMatrix` is defined as exactly this `toMatrix₂Aux`, but its body is not exposed
-- across the module boundary, so the identification is not `rfl` here: it goes through the
-- public entrywise characterisation `neronTateGramMatrix_apply`.
private theorem neronTateGramMatrix_eq_toMatrix₂Aux [W.toAffine.IsElliptic] {ι : Type*}
    (b : Module.Basis ι ℤ (PointModTorsion W)) :
    neronTateGramMatrix W b =
      LinearMap.toMatrix₂Aux ℤ (b : ι → PointModTorsion W) (b : ι → PointModTorsion W)
        (neronTatePairingModTorsion W) := by
  ext i j
  simp

/-- A change of basis acts on the Gram matrix of the Néron-Tate pairing by congruence, along the
integer change-of-basis matrix. The two bases need not share an index type: the change-of-basis
matrix is then rectangular, and the congruence still typechecks. -/
theorem neronTateGramMatrix_basis_change [W.toAffine.IsElliptic] {ι ι' : Type*} [Fintype ι]
    (b : Module.Basis ι ℤ (PointModTorsion W)) (b' : Module.Basis ι' ℤ (PointModTorsion W)) :
    neronTateGramMatrix W b' = ((b.toMatrix b').map Int.cast)ᵀ * neronTateGramMatrix W b *
      ((b.toMatrix b').map Int.cast) := by
  simp only [neronTateGramMatrix_eq_toMatrix₂Aux]
  simpa [algebraMap_int_eq] using
    (LinearMap.toMatrix₂Aux_mul_map_basis_toMatrix (neronTatePairingModTorsion W) b b b' b').symm

/-- The absolute determinant of the Gram matrix does not depend on the basis, nor on its index
type. -/
theorem abs_det_neronTateGramMatrix_basis_change [W.toAffine.IsElliptic] {ι ι' : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (b : Module.Basis ι ℤ (PointModTorsion W)) (b' : Module.Basis ι' ℤ (PointModTorsion W)) :
    |(neronTateGramMatrix W b').det| = |(neronTateGramMatrix W b).det| := by
  simp only [neronTateGramMatrix_eq_toMatrix₂Aux]
  exact congrArg abs
    (LinearMap.det_toMatrix₂Aux_eq_det_toMatrix₂Aux (neronTatePairingModTorsion W) b b')

variable (W)

/-- **The regulator** of an elliptic curve whose points modulo torsion are finitely generated as a
`ℤ`-module: the absolute determinant of the Gram matrix of the Néron-Tate pairing on any basis of
that quotient. For a curve of rank zero this is the empty determinant, namely `1`. -/
noncomputable def regulator [W.toAffine.IsElliptic] [Module.Finite ℤ (PointModTorsion W)] : ℝ :=
  |(neronTateGramMatrix W (Module.finBasis ℤ (PointModTorsion W))).det|

/-- The regulator is computed by any basis of the points modulo torsion. -/
theorem regulator_eq_abs_det_neronTateGramMatrix [W.toAffine.IsElliptic]
    [Module.Finite ℤ (PointModTorsion W)] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ (PointModTorsion W)) :
    regulator W = |(neronTateGramMatrix W b).det| :=
  abs_det_neronTateGramMatrix_basis_change b _

/-- **The rank-zero convention.** A curve whose points modulo torsion have rank zero has
regulator `1`, the determinant of the empty matrix. -/
@[simp]
theorem regulator_eq_one_of_finrank_eq_zero [W.toAffine.IsElliptic]
    [Module.Finite ℤ (PointModTorsion W)] (h : Module.finrank ℤ (PointModTorsion W) = 0) :
    regulator W = 1 := by
  have : IsEmpty (Fin (Module.finrank ℤ (PointModTorsion W))) := by rw [h]; infer_instance
  rw [regulator_eq_abs_det_neronTateGramMatrix W (Module.finBasis ℤ (PointModTorsion W)),
    Matrix.det_isEmpty, abs_one]

/-- The regulator is non-negative. -/
theorem regulator_nonneg [W.toAffine.IsElliptic] [Module.Finite ℤ (PointModTorsion W)] :
    0 ≤ regulator W :=
  abs_nonneg _

/-- The Gram matrix of the Néron–Tate pairing has nonzero determinant under Northcott finiteness.
This gives nondegeneracy of the height pairing over `ℝ`. -/
theorem det_neronTateGramMatrix_ne_zero [W.toAffine.IsElliptic]
    [Northcott (Point.canonicalHeight (W := W))] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ (PointModTorsion W)) : (neronTateGramMatrix W b).det ≠ 0 := by
  have heval (z : ι → ℤ) :
      (fun i ↦ (z i : ℝ)) ⬝ᵥ neronTateGramMatrix W b *ᵥ (fun i ↦ (z i : ℝ)) =
        neronTatePairingModTorsion W (b.equivFun.symm z) (b.equivFun.symm z) := by
    rw [← LinearMap.sum_repr_mul_repr_mul b b (b.equivFun.symm z) (b.equivFun.symm z)]
    have hz (i : ι) : b.repr (b.equivFun.symm z) i = z i := by
      simpa only [Module.Basis.equivFun_apply] using congrFun (b.equivFun.apply_symm_apply z) i
    rw [Finsupp.sum_fintype _ _ (fun _ ↦ by simp)]
    simp only [dotProduct, Matrix.mulVec, neronTateGramMatrix_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finsupp.sum_fintype _ _ (fun _ ↦ by simp)]
    simp only [hz, zsmul_eq_mul]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  let : Northcott (fun z : ι → ℤ ↦
      (fun i ↦ (z i : ℝ)) ⬝ᵥ neronTateGramMatrix W b *ᵥ (fun i ↦ (z i : ℝ))) := by
    refine ⟨fun C ↦ ?_⟩
    simp_rw [heval]
    exact (Northcott.finite_le (h := fun x : PointModTorsion W ↦
      neronTatePairingModTorsion W x x) C).preimage b.equivFun.symm.injective.injOn
  exact (isSymm_neronTateGramMatrix b).det_ne_zero_of_northcott

/-- The regulator is strictly positive under Northcott finiteness, including in rank zero,
where it equals `1`. In particular this applies to elliptic curves over number fields. -/
theorem regulator_pos [W.toAffine.IsElliptic] [Module.Finite ℤ (PointModTorsion W)]
    [Northcott (Point.canonicalHeight (W := W))] : 0 < regulator W := by
  rw [regulator_eq_abs_det_neronTateGramMatrix W (Module.finBasis ℤ (PointModTorsion W))]
  exact abs_pos.mpr (det_neronTateGramMatrix_ne_zero W _)

end WeierstrassCurve.Affine
