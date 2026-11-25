/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Matrix.EuclideanCLM
public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace
public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic

/-!
# The normalized trace and 2-norm through Hilbert–Schmidt norms

For an operator `T : ℂᵏ →L[ℂ] K` out of `ℂᵏ = EuclideanSpace ℂ n` into a Hilbert space, the
matrix of `T† ∘L T` has normalized trace `tr_k(T⋆T) = k⁻¹ ‖T‖²_HS`
(`CStarMatrix.normalizedTrace_toEuclideanCLM_symm_adjoint_comp_self`), where `‖·‖_HS` is
`ContinuousLinearMap.hilbertSchmidtNorm`. Consequently the normalized 2-norm of a matrix is
`k^{-1/2}` times the Hilbert–Schmidt norm of its operator
(`CStarMatrix.normalizedTwoNorm_toEuclideanCLM_symm`).
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace CStarMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

open ContinuousLinearMap in
/-- The normalized trace of the matrix of `T† ∘L T` is `k⁻¹ ‖T‖²_HS`. -/
theorem normalizedTrace_toEuclideanCLM_symm_adjoint_comp_self
    (T : EuclideanSpace ℂ n →L[ℂ] K) :
    normalizedTrace (toEuclideanCLM.symm (T.adjoint ∘L T)) =
      (((Fintype.card n : ℝ)⁻¹ * T.hilbertSchmidtNorm ^ 2 : ℝ) : ℂ) := by
  rw [normalizedTrace_eq_sum, T.sq_hilbertSchmidtNorm (EuclideanSpace.basisFun n ℂ).toHilbertBasis,
    hilbertSchmidtEnergy_def, tsum_fintype,
    ENNReal.toReal_sum fun _ _ => ENNReal.pow_ne_top eNorm_ne_top]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← inner_single_toEuclideanCLM_single (toEuclideanCLM.symm (T.adjoint ∘L T)) i,
    StarAlgEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply, adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  simp [OrthonormalBasis.coe_toHilbertBasis, ENNReal.toReal_pow]

/-- The normalized 2-norm of a matrix is `k^{-1/2}` times the Hilbert–Schmidt norm of its
operator. -/
theorem normalizedTwoNorm_toEuclideanCLM_symm
    (Z : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    normalizedTwoNorm (toEuclideanCLM.symm Z) =
      √(Fintype.card n : ℝ)⁻¹ * Z.hilbertSchmidtNorm := by
  rw [normalizedTwoNorm_def, ← toEuclideanCLM_symm_adjoint_comp,
    normalizedTrace_toEuclideanCLM_symm_adjoint_comp_self, Complex.ofReal_re,
    Real.sqrt_mul (by positivity), Real.sqrt_sq Z.hilbertSchmidtNorm_nonneg]

end CStarMatrix
