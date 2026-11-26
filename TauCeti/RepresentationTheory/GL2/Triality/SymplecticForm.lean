/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import TauCeti.LinearAlgebra.Matrix.Determinant.Polarization
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic.Ring
import TauCeti.LinearAlgebra.BilinearForm.TensorProduct
import TauCeti.LinearAlgebra.PerfectPairing.Basis

/-!
# The symplectic form for GL₂ triality

The tensor product of the two-by-two determinant pairing with the standard area form on
`R²` is alternating and perfect over any commutative ring. On pure tensors it pairs the
matrix factors by determinant polarization and the vector factors by their wedge.

This is the form of Gal Dor, [*Exotic Monoidal Structures and Abstractly Automorphic
Representations for GL(2)*](https://doi.org/10.1017/fmp.2023.18), Construction 2.7.
-/

public section

namespace TauCeti.GL2Triality

open LinearMap (BilinForm)
open scoped Matrix Kronecker TensorProduct

variable {R : Type*} [CommRing R]

/-- The symplectic form on `M₂(R) ⊗[R] R²` obtained from the determinant pairing and the
standard area form. -/
noncomputable def symplecticForm (R : Type*) [CommRing R] :
    BilinForm R (Matrix (Fin 2) (Fin 2) R ⊗[R] (Fin 2 → R)) :=
  (Matrix.detFinTwoBilin R).tmul (Matrix.toBilin' !![0, 1; -1, 0])

/-- On pure tensors, the symplectic form multiplies the determinant pairing by the wedge
of the two vectors. -/
@[simp]
theorem symplecticForm_tmul_tmul (A B : Matrix (Fin 2) (Fin 2) R) (x y : Fin 2 → R) :
    symplecticForm R (A ⊗ₜ[R] x) (B ⊗ₜ[R] y) =
      Matrix.detFinTwoBilin R A B * (x 0 * y 1 - x 1 * y 0) := by
  rw [symplecticForm, BilinForm.tensorDistrib_tmul]
  simp [Matrix.toBilin'_apply, Fin.sum_univ_two]
  ring

private theorem toMatrix_symplecticForm :
    (symplecticForm R).toMatrix ((Matrix.stdBasis R (Fin 2) (Fin 2)).tensorProduct
      (Pi.basisFun R (Fin 2))) =
      (Matrix.detFinTwoBilin R).toMatrix (Matrix.stdBasis R (Fin 2) (Fin 2)) ⊗ₖ
        !![0, 1; -1, 0] := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [BilinForm.toMatrix_apply, Module.Basis.tensorProduct_apply, Pi.basisFun_apply,
    symplecticForm, BilinForm.tensorDistrib_tmul, Matrix.toBilin'_single, smul_eq_mul,
    Matrix.kronecker_apply]
  exact mul_comm _ _

/-- The triality form is alternating, including in characteristic two. -/
theorem isAlt_symplecticForm : (symplecticForm R).IsAlt := by
  rw [symplecticForm]
  apply Matrix.isSymm_detFinTwoBilin.tmul_isAlt
  intro x
  simp [Matrix.toBilin'_apply, Fin.sum_univ_two]
  ring

/-- The triality form identifies the tensor product with its linear dual. -/
instance instIsPerfPairSymplecticForm : (symplecticForm R).IsPerfPair := by
  let b := (Matrix.stdBasis R (Fin 2) (Fin 2)).tensorProduct (Pi.basisFun R (Fin 2))
  refine b.isPerfPair_of_isUnit_det b _ ?_
  rw [← BilinForm.toMatrix, toMatrix_symplecticForm, Matrix.det_kronecker,
    Matrix.det_toMatrix_detFinTwoBilin, Matrix.det_fin_two_of]
  simp

end TauCeti.GL2Triality
