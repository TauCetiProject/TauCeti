/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SymmetricFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Agreement of the finite and continuous functional calculi

On a finite-dimensional complex inner product space, the spectral functional calculus of a
symmetric linear map equals Mathlib's continuous functional calculus of the corresponding bounded
operator. The symbol may be any real function: the spectrum is finite, so its restriction is
continuous. This lets explicit spectral sums and the abstract calculus share the same operator,
in particular when comparing square-root constructions.

The central matrix comparison is `Matrix.IsHermitian.cfc_eq` from
`Mathlib.Analysis.Matrix.HermitianFunctionalCalculus`, by Jon Bannon and Jireh Loreaux.
This file transports that result to symmetric operators through an orthonormal basis.
-/

public section

open scoped InnerProductSpace

namespace LinearMap.IsSymmetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E}

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E

/-- The finite spectral calculus of a symmetric complex operator agrees with the continuous
functional calculus of its bounded-operator presentation. No continuity hypothesis is needed
because the spectrum is finite. -/
theorem cfc_eq (hT : T.IsSymmetric) (f : ℝ → ℝ) :
    (hT.cfc f).toContinuousLinearMap = _root_.cfc f T.toContinuousLinearMap := by
  classical
  let b := stdOrthonormalBasis ℂ E
  let A := T.toMatrix b.toBasis b.toBasis
  have hA : A.IsHermitian := (T.isHermitian_toMatrix_iff b).mpr hT
  -- Transport the matrix comparison back to E through the basis isometry.
  let φ := b.repr.symm.conjStarAlgEquiv.toStarAlgHom.comp
    Matrix.toEuclideanCLM.toStarAlgHom
  have hφ (M : Matrix (Fin (Module.finrank ℂ E)) (Fin (Module.finrank ℂ E)) ℂ)
      (x : EuclideanSpace ℂ (Fin (Module.finrank ℂ E))) :
      φ M (b.repr.symm x) = b.repr.symm (Matrix.toEuclideanCLM (𝕜 := ℂ) M x) := by
    simp [φ]
  have hTmatrix : φ A = T.toContinuousLinearMap := by
    ext x
    apply b.repr.injective
    apply WithLp.ofLp_injective
    have hb (y : E) : (b.toBasis.repr y : _ → ℂ) = WithLp.ofLp (b.repr y) :=
      funext (b.coe_toBasis_repr_apply y)
    simpa [φ, A, Matrix.ofLp_toEuclideanCLM, hb] using
      T.toMatrix_mulVec_repr b.toBasis b.toBasis x
  have hmap := φ.map_cfc f A
    (by rw [hA.spectrum_real_eq_range_eigenvalues]; exact (Set.finite_range _).continuousOn f)
    φ.toAlgHom.toLinearMap.continuous_of_finiteDimensional hA.isSelfAdjoint
    (by
      rw [hTmatrix]
      exact T.isSelfAdjoint_toContinuousLinearMap_iff.mpr
        (T.isSymmetric_iff_isSelfAdjoint.mp hT))
  rw [hA.cfc_eq, hTmatrix] at hmap
  rw [← hmap]
  apply ContinuousLinearMap.coe_injective
  -- Compare eigenvector actions in the transported matrix basis.
  refine (hA.eigenvectorBasis.toBasis.map b.repr.symm.toLinearEquiv).ext fun i ↦ ?_
  -- Normalize the mapped basis vector and linear-map coercions to their applications.
  change hT.cfc f (b.repr.symm (hA.eigenvectorBasis i)) =
    φ (hA.cfc f) (b.repr.symm (hA.eigenvectorBasis i))
  have heig : T (b.repr.symm (hA.eigenvectorBasis i)) =
      (hA.eigenvalues i : ℂ) • b.repr.symm (hA.eigenvectorBasis i) := by
    -- View the same application as a bounded operator so the transport equation can rewrite it.
    change T.toContinuousLinearMap (b.repr.symm (hA.eigenvectorBasis i)) = _
    rw [← hTmatrix, hφ, ← map_smul]
    congr 1
    apply WithLp.ofLp_injective
    simpa [Matrix.ofLp_toEuclideanCLM, RCLike.real_smul_eq_coe_smul] using
      hA.mulVec_eigenvectorBasis i
  rw [hT.cfc_apply_of_apply_eq_smul f heig, hφ, ← map_smul]
  congr 1
  apply WithLp.ofLp_injective
  rw [Matrix.ofLp_toEuclideanCLM, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hA.star_eigenvectorUnitary_mulVec, Matrix.diagonal_mulVec_single]
  ext j
  simp only [Complex.coe_algebraMap, Complex.coe_smul, PiLp.smul_apply, Complex.real_smul,
    Function.comp_apply, mul_one, Matrix.mulVec_single, hA.eigenvectorUnitary_col_eq,
    Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
  exact mul_comm _ _

end LinearMap.IsSymmetric
