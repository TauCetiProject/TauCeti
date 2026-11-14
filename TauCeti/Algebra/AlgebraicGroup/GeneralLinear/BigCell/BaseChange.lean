/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.BigCell.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Base change of the block big cell

The block big-cell coordinate algebra commutes with arbitrary scalar extension. The
comparison preserves the universal matrix and its three regular LDU factors. Thus the
regular inverse to block LDU multiplication is compatible with base change, including
specialization to finite fields and nonreduced rings. No assertion that these ambient
matrix factors belong to a specified Chevalley subgroup is made here.

The algebra comparison follows `GeneralLinear.coordinateRingBaseChangeAlgEquiv`: use
Mathlib's localization and multivariate-polynomial scalar-extension equivalences. Factor
compatibility uses the existing uniqueness of regular block LDU factors.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 5, Theorem 7.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open scoped TensorProduct

namespace TauCeti.GeneralLinear

open Matrix

universe u v

variable {n α : Type*} [Fintype n] [DecidableEq n] [LinearOrder α]
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] (b : n → α)

private noncomputable def localizedBlockPolynomialBaseChangeEquiv :
    Localization.Away ((1 : S) ⊗ₜ[R] blockBigCellDenominator R b) ≃ₐ[S]
      BlockBigCellCoordinateAlgebra S b :=
  IsLocalization.algEquivOfAlgEquiv _ _ (MvPolynomial.algebraTensorAlgEquiv R S) (by
    rw [Submonoid.map_powers, MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul,
      map_blockBigCellDenominator R b (algebraMap R S)])

/-- Scalar extension of the block big-cell coordinate algebra is the block big-cell
coordinate algebra over the new base ring. No flatness hypothesis is required. -/
noncomputable def blockBigCellBaseChangeAlgEquiv :
    S ⊗[R] BlockBigCellCoordinateAlgebra R b ≃ₐ[S] BlockBigCellCoordinateAlgebra S b :=
  (IsLocalization.Away.tensorProductEquivTMulRight R S
    (blockBigCellDenominator R b) (BlockBigCellCoordinateAlgebra R b)).trans
      (localizedBlockPolynomialBaseChangeEquiv R S b)

/-- On polynomial coordinates, scalar extension changes the coefficients and multiplies by
the tensor's scalar factor. -/
-- Prefer the polynomial normal form over the general pure-tensor rule.
@[simp high]
theorem blockBigCellBaseChangeAlgEquiv_tmul_algebraMap (s : S)
    (p : MvPolynomial (n × n) R) :
    blockBigCellBaseChangeAlgEquiv R S b (s ⊗ₜ[R] algebraMap _ _ p) =
      s • algebraMap (MvPolynomial (n × n) S) (BlockBigCellCoordinateAlgebra S b)
        (MvPolynomial.map (algebraMap R S) p) := by
  rw [blockBigCellBaseChangeAlgEquiv, AlgEquiv.trans_apply,
    IsLocalization.Away.tensorProductEquivTMulRight_tmul,
    localizedBlockPolynomialBaseChangeEquiv, IsLocalization.algEquivOfAlgEquiv_eq]
  have hc : algebraMap (MvPolynomial (n × n) S) (BlockBigCellCoordinateAlgebra S b)
      (MvPolynomial.C s) = algebraMap S (BlockBigCellCoordinateAlgebra S b) s := by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  simp only [MvPolynomial.algebraTensorAlgEquiv_tmul, Algebra.smul_def,
    MvPolynomial.algebraMap_eq, map_mul, hc]

/-- The inverse base-change comparison recovers a polynomial coordinate as a pure tensor. -/
@[simp]
theorem blockBigCellBaseChangeAlgEquiv_symm_algebraMap (p : MvPolynomial (n × n) R) :
    (blockBigCellBaseChangeAlgEquiv R S b).symm
      (algebraMap (MvPolynomial (n × n) S) (BlockBigCellCoordinateAlgebra S b)
        (MvPolynomial.map (algebraMap R S) p)) =
      1 ⊗ₜ[R] algebraMap (MvPolynomial (n × n) R) (BlockBigCellCoordinateAlgebra R b) p := by
  apply (blockBigCellBaseChangeAlgEquiv R S b).injective
  simp

/-- The coefficient-change map on block big-cell coordinates, obtained from the canonical
scalar-extension comparison. -/
noncomputable def blockBigCellBaseChangeMap :
    BlockBigCellCoordinateAlgebra R b →ₐ[R] BlockBigCellCoordinateAlgebra S b :=
  ((blockBigCellBaseChangeAlgEquiv R S b).toAlgHom.restrictScalars R).comp
    Algebra.TensorProduct.includeRight

/-- The coefficient-change map is the comparison composed with the right tensor inclusion. -/
theorem blockBigCellBaseChangeMap_def :
    blockBigCellBaseChangeMap R S b =
      ((blockBigCellBaseChangeAlgEquiv R S b).toAlgHom.restrictScalars R).comp
        Algebra.TensorProduct.includeRight :=
  (rfl)

/-- On arbitrary regular coordinates, scalar extension multiplies the coefficient-change
map by the tensor's scalar factor. -/
@[simp]
theorem blockBigCellBaseChangeAlgEquiv_tmul (s : S)
    (x : BlockBigCellCoordinateAlgebra R b) :
    blockBigCellBaseChangeAlgEquiv R S b (s ⊗ₜ[R] x) =
      s • blockBigCellBaseChangeMap R S b x := by
  simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    blockBigCellBaseChangeMap, AlgHom.comp_apply, AlgHom.coe_restrictScalars',
    Algebra.TensorProduct.includeRight_apply, AlgEquiv.coe_toAlgHom] using
    (map_smul (blockBigCellBaseChangeAlgEquiv R S b) s (1 ⊗ₜ[R] x))

/-- The coefficient-change map agrees with polynomial coefficient extension. -/
@[simp]
theorem blockBigCellBaseChangeMap_algebraMap (p : MvPolynomial (n × n) R) :
    blockBigCellBaseChangeMap R S b (algebraMap _ _ p) =
      algebraMap (MvPolynomial (n × n) S) (BlockBigCellCoordinateAlgebra S b)
        (MvPolynomial.map (algebraMap R S) p) := by
  simp only [blockBigCellBaseChangeMap, AlgHom.comp_apply, AlgHom.coe_restrictScalars',
    Algebra.TensorProduct.includeRight_apply, AlgEquiv.coe_toAlgHom,
    blockBigCellBaseChangeAlgEquiv_tmul_algebraMap, one_smul]

/-- The inverse comparison sends coefficient-changed regular coordinates to pure tensors. -/
@[simp]
theorem blockBigCellBaseChangeAlgEquiv_symm_baseChangeMap
    (x : BlockBigCellCoordinateAlgebra R b) :
    (blockBigCellBaseChangeAlgEquiv R S b).symm (blockBigCellBaseChangeMap R S b x) =
      1 ⊗ₜ[R] x := by
  apply (blockBigCellBaseChangeAlgEquiv R S b).injective
  simp

/-- The inverse comparison restricts to the right tensor inclusion on original coordinates. -/
@[simp]
theorem blockBigCellBaseChangeAlgEquiv_symm_comp_baseChangeMap :
    ((blockBigCellBaseChangeAlgEquiv R S b).symm.toAlgHom.restrictScalars R).comp
      (blockBigCellBaseChangeMap R S b) = Algebra.TensorProduct.includeRight := by
  apply AlgHom.ext
  intro x
  exact blockBigCellBaseChangeAlgEquiv_symm_baseChangeMap R S b x

/-- The inverse comparison sends a matrix variable to its original pure tensor. -/
@[simp]
theorem blockBigCellBaseChangeAlgEquiv_symm_X (ij : n × n) :
    (blockBigCellBaseChangeAlgEquiv R S b).symm
      (algebraMap (MvPolynomial (n × n) S) (BlockBigCellCoordinateAlgebra S b)
        (MvPolynomial.X ij)) =
      1 ⊗ₜ[R] algebraMap (MvPolynomial (n × n) R) (BlockBigCellCoordinateAlgebra R b)
        (MvPolynomial.X ij) := by
  simpa only [MvPolynomial.map_X] using
    blockBigCellBaseChangeAlgEquiv_symm_algebraMap R S b (MvPolynomial.X ij)

/-- The inverse comparison places a constant in the scalar tensor factor. -/
@[simp]
theorem blockBigCellBaseChangeAlgEquiv_symm_C (s : S) :
    (blockBigCellBaseChangeAlgEquiv R S b).symm
      (algebraMap (MvPolynomial (n × n) S) (BlockBigCellCoordinateAlgebra S b)
        (MvPolynomial.C s)) = s ⊗ₜ[R] 1 := by
  rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  exact (blockBigCellBaseChangeAlgEquiv R S b).symm.commutes s

/-- The inverse comparison separates a monomial's new coefficient from its original variables. -/
@[simp]
theorem blockBigCellBaseChangeAlgEquiv_symm_monomial (m : (n × n) →₀ ℕ) (s : S) :
    (blockBigCellBaseChangeAlgEquiv R S b).symm
      (algebraMap (MvPolynomial (n × n) S) (BlockBigCellCoordinateAlgebra S b)
        (MvPolynomial.monomial m s)) =
      s ⊗ₜ[R] algebraMap (MvPolynomial (n × n) R) (BlockBigCellCoordinateAlgebra R b)
        (MvPolynomial.monomial m 1) := by
  apply (blockBigCellBaseChangeAlgEquiv R S b).injective
  simp only [AlgEquiv.apply_symm_apply, blockBigCellBaseChangeAlgEquiv_tmul_algebraMap,
    MvPolynomial.map_monomial, map_one, Algebra.smul_def]
  rw [IsScalarTower.algebraMap_apply S (MvPolynomial (n × n) S)
    (BlockBigCellCoordinateAlgebra S b), MvPolynomial.algebraMap_eq,
    ← map_mul, MvPolynomial.C_mul_monomial, mul_one]

/-- Coefficient change preserves the universal matrix. -/
@[simp]
theorem map_blockBigCellMatrix_baseChange :
    (blockBigCellMatrix R b).map (blockBigCellBaseChangeMap R S b) =
      blockBigCellMatrix S b := by
  ext i j
  simp

/-- Coefficient change is evaluation at the universal matrix over the new base. -/
theorem blockBigCellBaseChangeMap_eq_eval :
    blockBigCellBaseChangeMap R S b = blockBigCellEval (R := R) (blockBigCellMatrix S b)
      isUnit_det_toSquareBlockProp_blockBigCellMatrix := by
  apply blockBigCell_algHom_ext
  rw [map_blockBigCellMatrix_baseChange, map_blockBigCellMatrix]

private theorem map_blockBigCell_factors_baseChange :
    (blockBigCellLower R b).map (blockBigCellBaseChangeMap R S b) = blockBigCellLower S b ∧
    (blockBigCellDiag R b).map (blockBigCellBaseChangeMap R S b) = blockBigCellDiag S b ∧
    (blockBigCellUpper R b).map (blockBigCellBaseChangeMap R S b) = blockBigCellUpper S b := by
  rw [blockBigCellBaseChangeMap_eq_eval]
  exact map_blockBigCell_factors _ _ (blockUnitriangular_blockBigCellLower S b)
    (blockTriangular_blockBigCellDiag S b) (blockTriangular_blockBigCellDiag_toDual S b)
    (blockUnitriangular_blockBigCellUpper S b)
    (blockBigCellMatrix_eq_blockBigCellLower_mul_blockBigCellDiag_mul_blockBigCellUpper S b)

/-- Coefficient change preserves the regular lower LDU factor. -/
@[simp]
theorem map_blockBigCellLower_baseChange :
    (blockBigCellLower R b).map (blockBigCellBaseChangeMap R S b) =
      blockBigCellLower S b :=
  (map_blockBigCell_factors_baseChange R S b).1

/-- Coefficient change preserves the regular diagonal LDU factor. -/
@[simp]
theorem map_blockBigCellDiag_baseChange :
    (blockBigCellDiag R b).map (blockBigCellBaseChangeMap R S b) =
      blockBigCellDiag S b :=
  (map_blockBigCell_factors_baseChange R S b).2.1

/-- Coefficient change preserves the regular upper LDU factor. -/
@[simp]
theorem map_blockBigCellUpper_baseChange :
    (blockBigCellUpper R b).map (blockBigCellBaseChangeMap R S b) =
      blockBigCellUpper S b :=
  (map_blockBigCell_factors_baseChange R S b).2.2

/-- Coefficient change preserves each entry of the regular lower LDU factor. -/
@[simp]
theorem blockBigCellBaseChangeMap_lower (i j : n) :
    blockBigCellBaseChangeMap R S b (blockBigCellLower R b i j) =
      blockBigCellLower S b i j :=
  congrFun (congrFun (map_blockBigCellLower_baseChange R S b) i) j

/-- Coefficient change preserves each entry of the regular diagonal LDU factor. -/
@[simp]
theorem blockBigCellBaseChangeMap_diag (i j : n) :
    blockBigCellBaseChangeMap R S b (blockBigCellDiag R b i j) =
      blockBigCellDiag S b i j :=
  congrFun (congrFun (map_blockBigCellDiag_baseChange R S b) i) j

/-- Coefficient change preserves each entry of the regular upper LDU factor. -/
@[simp]
theorem blockBigCellBaseChangeMap_upper (i j : n) :
    blockBigCellBaseChangeMap R S b (blockBigCellUpper R b i j) =
      blockBigCellUpper S b i j :=
  congrFun (congrFun (map_blockBigCellUpper_baseChange R S b) i) j

/-- The inverse comparison recovers each original lower-factor entry as a pure tensor. -/
@[simp]
theorem blockBigCellBaseChangeAlgEquiv_symm_lower (i j : n) :
    (blockBigCellBaseChangeAlgEquiv R S b).symm (blockBigCellLower S b i j) =
      1 ⊗ₜ[R] blockBigCellLower R b i j := by
  rw [← blockBigCellBaseChangeMap_lower R S b,
    blockBigCellBaseChangeAlgEquiv_symm_baseChangeMap]

/-- The inverse comparison recovers each original diagonal-factor entry as a pure tensor. -/
@[simp]
theorem blockBigCellBaseChangeAlgEquiv_symm_diag (i j : n) :
    (blockBigCellBaseChangeAlgEquiv R S b).symm (blockBigCellDiag S b i j) =
      1 ⊗ₜ[R] blockBigCellDiag R b i j := by
  rw [← blockBigCellBaseChangeMap_diag R S b,
    blockBigCellBaseChangeAlgEquiv_symm_baseChangeMap]

/-- The inverse comparison recovers each original upper-factor entry as a pure tensor. -/
@[simp]
theorem blockBigCellBaseChangeAlgEquiv_symm_upper (i j : n) :
    (blockBigCellBaseChangeAlgEquiv R S b).symm (blockBigCellUpper S b i j) =
      1 ⊗ₜ[R] blockBigCellUpper R b i j := by
  rw [← blockBigCellBaseChangeMap_upper R S b,
    blockBigCellBaseChangeAlgEquiv_symm_baseChangeMap]

/-- Changing coefficients along the identity leaves every regular coordinate unchanged. -/
@[simp]
theorem blockBigCellBaseChangeMap_self :
    blockBigCellBaseChangeMap R R b = AlgHom.id R _ := by
  apply blockBigCell_algHom_ext
  simp

variable {T : Type*} [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/-- Successive coefficient changes agree with coefficient change along the composite. -/
@[simp]
theorem blockBigCellBaseChangeMap_trans (R : Type u) (S : Type v) (T : Type*)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] (b : n → α) :
    ((blockBigCellBaseChangeMap S T b).restrictScalars R).comp
      (blockBigCellBaseChangeMap R S b) = blockBigCellBaseChangeMap R T b := by
  apply blockBigCell_algHom_ext
  simp only [AlgHom.coe_comp, ← Matrix.map_map, AlgHom.coe_restrictScalars',
    map_blockBigCellMatrix_baseChange]

/-- Successive coefficient changes simplify entrywise to the composite coefficient change. -/
@[simp]
theorem blockBigCellBaseChangeMap_baseChangeMap (x : BlockBigCellCoordinateAlgebra R b) :
    blockBigCellBaseChangeMap S T b (blockBigCellBaseChangeMap R S b x) =
      blockBigCellBaseChangeMap R T b x :=
  DFunLike.congr_fun (blockBigCellBaseChangeMap_trans R S T b) x

/-- Evaluating after coefficient extension agrees with evaluating the original coordinates.
This describes the base-change comparison on arbitrary algebra-valued points. -/
@[simp]
theorem blockBigCellEval_comp_baseChangeMap (M : Matrix n n T)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det) :
    ((blockBigCellEval (R := S) M hM).restrictScalars R).comp
      (blockBigCellBaseChangeMap R S b) = blockBigCellEval (R := R) M hM := by
  apply blockBigCell_algHom_ext
  simp only [AlgHom.coe_comp, ← Matrix.map_map, AlgHom.coe_restrictScalars',
    map_blockBigCellMatrix_baseChange, map_blockBigCellMatrix]

/-- Evaluation of a coefficient-changed regular coordinate is its original evaluation. -/
@[simp]
theorem blockBigCellEval_baseChangeMap (M : Matrix n n T)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det)
    (x : BlockBigCellCoordinateAlgebra R b) :
    blockBigCellEval (R := S) M hM (blockBigCellBaseChangeMap R S b x) =
      blockBigCellEval (R := R) M hM x :=
  DFunLike.congr_fun (blockBigCellEval_comp_baseChangeMap R S b M hM) x

/-- Restricting a point along coefficient change preserves its represented matrix. -/
@[simp]
theorem blockBigCellPointsEquiv_comp_baseChangeMap
    (f : BlockBigCellCoordinateAlgebra S b →ₐ[S] T) :
    blockBigCellPointsEquiv R b T ((f.restrictScalars R).comp
      (blockBigCellBaseChangeMap R S b)) = blockBigCellPointsEquiv S b T f := by
  apply Subtype.ext
  simp only [blockBigCellPointsEquiv_apply, AlgHom.coe_comp, ← Matrix.map_map,
    AlgHom.coe_restrictScalars', map_blockBigCellMatrix_baseChange]

end TauCeti.GeneralLinear
