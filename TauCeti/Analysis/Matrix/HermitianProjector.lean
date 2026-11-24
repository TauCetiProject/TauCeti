/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Matrix.L2OpNorm
public import TauCeti.LinearAlgebra.Projectivization.HermitianProjector
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import TauCeti.Analysis.Calculus.Bilinear
import TauCeti.Analysis.Matrix.DotProduct

/-!
# Smoothness and derivative of the rank-one Hermitian projector

For a finite index type `n` and an `RCLike` field `𝕜`, `TauCeti.rankOneHermitianProjector` sends
`v : n → 𝕜` to `(star v ⬝ᵥ v)⁻¹ • Matrix.vecMulVec v (star v)`. We prove that this map is `C^m`
over `ℝ` for every `m : ℕ∞ω` (in particular real-analytic, `C^ω`) at every nonzero `v`, and compute
its strict and applied Fréchet derivatives over `ℝ`.

To state or use `TauCeti.contDiffAt_rankOneHermitianProjector`,
`open scoped Matrix.Norms.L2Operator` and enable
`attribute [local instance] Matrix.l2OpNormedAlgebraReal`. By contrast,
`TauCeti.hasStrictFDerivAt_rankOneHermitianProjector` and
`TauCeti.fderiv_rankOneHermitianProjector_apply` use only `instTopologicalSpaceMatrix` (requiring
neither `DecidableEq n` nor a choice of matrix norm).

## Main results

* `TauCeti.contDiffAt_rankOneHermitianProjector`: `C^m` smoothness over `ℝ` at any nonzero `v`.
* `TauCeti.hasStrictFDerivAt_rankOneHermitianProjector`: strict Fréchet derivative over `ℝ`.
* `TauCeti.fderiv_rankOneHermitianProjector_apply`: applied Fréchet derivative over `ℝ`.
-/

public section

noncomputable section

open Matrix
open scoped ContDiff ComplexOrder

namespace TauCeti

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

private def reInnerBilin (𝕜 n : Type*) [RCLike 𝕜] [Fintype n] :
    (n → 𝕜) →L[ℝ] (n → 𝕜) →L[ℝ] ℝ :=
  (((dotProductBilin ℝ ℝ).comp (starLinearEquiv ℝ).toLinearMap).compr₂
    RCLike.reLm).toContinuousBilinearMap

private def vecMulVecStarBilin (𝕜 n : Type*) [RCLike 𝕜] [Fintype n] :
    (n → 𝕜) →L[ℝ] (n → 𝕜) →L[ℝ] Matrix n n 𝕜 :=
  ((vecMulVecBilin ℝ ℝ).compl₂ (starLinearEquiv ℝ).toLinearMap).toContinuousBilinearMap

private theorem rankOneHermitianProjector_eq_inv_smul_bilin :
    (rankOneHermitianProjector : (n → 𝕜) → Matrix n n 𝕜) =
      fun u ↦ (reInnerBilin 𝕜 n u u)⁻¹ • vecMulVecStarBilin 𝕜 n u u := by
  ext u i j
  simp [reInnerBilin, vecMulVecStarBilin, rankOneHermitianProjector_eq_real_smul]

private theorem reInnerBilin_self_ne_zero {v : n → 𝕜} (hv : v ≠ 0) :
    reInnerBilin 𝕜 n v v ≠ 0 :=
  fun h0 ↦ dotProduct_star_self_eq_zero.not.mpr hv
    (by rw [← Matrix.ofReal_re_dotProduct_star_self v]; simpa [reInnerBilin] using h0)

section L2Operator

open scoped Matrix.Norms.L2Operator

attribute [local instance] Matrix.l2OpNormedAlgebraReal

/-- `TauCeti.rankOneHermitianProjector` is `C^m` over `ℝ` at every nonzero vector `v : n → 𝕜`. -/
theorem contDiffAt_rankOneHermitianProjector [DecidableEq n] {v : n → 𝕜} (hv : v ≠ 0) {m : ℕ∞ω} :
    ContDiffAt ℝ m (rankOneHermitianProjector : (n → 𝕜) → Matrix n n 𝕜) v := by
  rw [rankOneHermitianProjector_eq_inv_smul_bilin]
  exact (((reInnerBilin 𝕜 n).contDiff_apply_self (n := m)).contDiffAt.inv
    (reInnerBilin_self_ne_zero hv)).smul
    ((vecMulVecStarBilin 𝕜 n).contDiff_apply_self (n := m)).contDiffAt

private theorem hasStrictFDerivAt_rankOneHermitianProjector_aux {v : n → 𝕜} (hv : v ≠ 0) :
    HasStrictFDerivAt (rankOneHermitianProjector : (n → 𝕜) → Matrix n n 𝕜)
      ((RCLike.re (star v ⬝ᵥ v))⁻¹ •
        ((vecMulVecBilin ℝ ℝ).flip (star v) +
          (vecMulVecBilin ℝ ℝ v).comp (starL' ℝ).toLinearMap -
          (2 : ℝ) • ((RCLike.reLm.comp (dotProductBilin ℝ ℝ (star v))).smulRight
            (rankOneHermitianProjector v))).toContinuousLinearMap) v := by
  classical
  rw [rankOneHermitianProjector_eq_inv_smul_bilin]
  have hinv := HasStrictDerivAt.comp_hasStrictFDerivAt (f := fun z ↦ reInnerBilin 𝕜 n z z) v
    (hasStrictDerivAt_inv (reInnerBilin_self_ne_zero hv))
    ((reInnerBilin 𝕜 n).hasStrictFDerivAt_apply_self v)
  refine (hinv.smul ((vecMulVecStarBilin 𝕜 n).hasStrictFDerivAt_apply_self v)).congr_fderiv ?_
  ext y i j
  have hre : RCLike.re (star y ⬝ᵥ v) = RCLike.re (star v ⬝ᵥ y) := by
    rw [star_dotProduct, RCLike.star_def, RCLike.conj_re]
  simp only [reInnerBilin, vecMulVecStarBilin, Function.comp_apply, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.flip_apply,
    LinearMap.toContinuousBilinearMap_apply, LinearMap.coe_toContinuousLinearMap',
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.flip_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
    LinearMap.smulRight_apply, LinearEquiv.coe_coe, starLinearEquiv_apply,
    ContinuousLinearEquiv.coe_toLinearEquiv, starL'_apply, RCLike.reLm_coe,
    dotProductBilin_apply_apply, vecMulVecBilin_apply_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, RCLike.real_smul_eq_coe_mul (K := 𝕜),
    hre, sq, mul_inv]
  push_cast
  ring

end L2Operator

/-- Strict Fréchet derivative of `TauCeti.rankOneHermitianProjector` over `ℝ` at any nonzero
vector `v : n → 𝕜`. -/
theorem hasStrictFDerivAt_rankOneHermitianProjector {v : n → 𝕜} (hv : v ≠ 0) :
    HasStrictFDerivAt (rankOneHermitianProjector : (n → 𝕜) → Matrix n n 𝕜)
      ((RCLike.re (star v ⬝ᵥ v))⁻¹ •
        ((vecMulVecBilin ℝ ℝ).flip (star v) +
          (vecMulVecBilin ℝ ℝ v).comp (starL' ℝ).toLinearMap -
          (2 : ℝ) • ((RCLike.reLm.comp (dotProductBilin ℝ ℝ (star v))).smulRight
            (rankOneHermitianProjector v))).toContinuousLinearMap) v :=
  hasStrictFDerivAt_rankOneHermitianProjector_aux hv

/-- Applied Fréchet derivative of `TauCeti.rankOneHermitianProjector` over `ℝ` at any nonzero
vector `v : n → 𝕜` in direction `y`. -/
theorem fderiv_rankOneHermitianProjector_apply {v : n → 𝕜} (hv : v ≠ 0) (y : n → 𝕜) :
    fderiv ℝ (rankOneHermitianProjector : (n → 𝕜) → Matrix n n 𝕜) v y =
      (RCLike.re (star v ⬝ᵥ v))⁻¹ •
        (Matrix.vecMulVec y (star v) + Matrix.vecMulVec v (star y) -
          (2 * RCLike.re (star v ⬝ᵥ y)) • rankOneHermitianProjector v) := by
  rw [(hasStrictFDerivAt_rankOneHermitianProjector hv).hasFDerivAt.fderiv]
  simp [smul_smul]

end TauCeti
