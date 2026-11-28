/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Abs
public import TauCeti.Analysis.Calculus.FDeriv.Det.Rpow
public import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Normed.Operator.FiniteDimensional
import TauCeti.LinearAlgebra.Matrix.Nonsingular.Inverse
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Differentiability of norm determinant powers

For a nonsingular real endomorphism, a real power of the norm determinant is differentiable.
This differentiates the determinant root along a nonsingular operator curve. A curve starting
at zero with identity initial velocity has determinant root with right derivative one.
-/

public section

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Every real power of the norm determinant is differentiable at a nonsingular operator. -/
theorem DifferentiableAt.normDet_rpow {J : G → F →L[ℝ] F} {t : G} {z : ℝ}
    (hJ : DifferentiableAt ℝ J t) (hi : (J t).IsInvertible) :
    DifferentiableAt ℝ (fun r ↦ (J r).toLinearMap.normDet ^ z) t := by
  have hne := hi.det_ne_zero
  have hd := (ContinuousLinearMap.contDiff_det (𝕜 := ℝ) (E := F) (r := 1)).differentiable
    (by simp)
  simpa only [LinearMap.normDet_eq_abs_det, Function.comp_def] using
    ((hd.differentiableAt.comp t hJ).abs hne).rpow_const
      (Or.inl (abs_ne_zero.mpr hne))

open Filter Set ContinuousLinearMap
open scoped Topology Matrix.Norms.Operator

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A differentiable velocity makes every determinant-power derivative differentiable before
singularity. No equation identifying the acceleration is required. -/
theorem differentiableAt_deriv_normDet_rpow
    {J V : ℝ → F →L[ℝ] F} {t z : ℝ}
    (hJ : ∀ᶠ r in 𝓝 t, HasDerivAt J (V r) r)
    (hV : DifferentiableAt ℝ V t) (hi : (J t).IsInvertible) :
    DifferentiableAt ℝ (deriv (fun r ↦ (J r).toLinearMap.normDet ^ z)) t := by
  let b := stdOrthonormalBasis ℝ F
  have hJM : ∀ᶠ r in 𝓝 t,
      HasDerivAt (fun q ↦ toMatrixCLM b.toBasis (J q))
        (toMatrixCLM b.toBasis (V r)) r :=
    hJ.mono fun r hr ↦ (toMatrixCLM b.toBasis).hasFDerivAt.comp_hasDerivAt r hr
  have hne : ((toMatrixCLM b.toBasis) (J t)).det ≠ 0 := by
    rw [ContinuousLinearMap.toMatrixCLM_apply, LinearMap.det_toMatrix]
    exact hi.det_ne_zero
  have hR := ((toMatrixCLM b.toBasis).differentiableAt.comp t
    (hV.clm_comp (hJ.self_of_nhds.differentiableAt.clm_inverse_of_completeSpace hi))).hasDerivAt
  have hh := hR.matrix_trace
  simp only [Function.comp_def] at hh
  simp only [toMatrixCLM_comp_inverse] at hh
  simp only [toMatrixCLM_apply] at hh
  simp only [ContinuousLinearMap.toMatrixCLM_apply] at hJM hne
  have hd := Matrix.hasDerivAt_deriv_abs_det_rpow (r := z) hJM hne hh
  simpa only [toMatrixCLM_apply, LinearMap.det_toMatrix, LinearMap.normDet_eq_abs_det]
    using hd.differentiableAt

/-- A curve in positive dimension starting at zero with identity initial velocity has
determinant root with right derivative one. -/
theorem hasDerivWithinAt_normDet_rpow_zero {J : ℝ → F →L[ℝ] F}
    (hm : 0 < Module.finrank ℝ F) (hzero : J 0 = 0)
    (hJ : HasDerivWithinAt J (ContinuousLinearMap.id ℝ F) (Ici 0) 0) :
    HasDerivWithinAt (fun t ↦ (J t).toLinearMap.normDet ^
      (1 / (Module.finrank ℝ F : ℝ))) 1 (Ici 0) 0 := by
  let m := Module.finrank ℝ F
  have hf0 : (J 0).toLinearMap.normDet ^ (1 / (m : ℝ)) = 0 := by
    simp only [hzero, ContinuousLinearMap.toLinearMap_zero, LinearMap.normDet_zero,
      zero_pow hm.ne', Real.zero_rpow (by positivity : (1 / (m : ℝ)) ≠ 0)]
  have hs : Tendsto (fun t ↦ t⁻¹ • J t) (𝓝[>] 0)
      (𝓝 (ContinuousLinearMap.id ℝ F)) := by
    have hslope := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).mp
      (hJ.mono Ioi_subset_Ici_self)
    exact hslope.congr' (.of_forall fun t ↦ by rw [slope_def_module, hzero, sub_zero, sub_zero])
  have hn := (ContinuousLinearMap.continuous_normDet.tendsto _).comp hs
  have hp : Tendsto (fun t ↦ (t⁻¹ • J t).toLinearMap.normDet ^ (1 / (m : ℝ)))
      (𝓝[>] 0) (𝓝 1) := by
    simpa only [Function.comp_def, ContinuousLinearMap.coe_id, LinearMap.normDet_id,
      Real.one_rpow] using
      hn.rpow_const (Or.inl (by simp :
        (ContinuousLinearMap.id ℝ F).toLinearMap.normDet ≠ 0))
  have heq : (fun t ↦ (J t).toLinearMap.normDet ^ (1 / (m : ℝ)) / t) =ᶠ[𝓝[>] 0]
      (fun t ↦ (t⁻¹ • J t).toLinearMap.normDet ^ (1 / (m : ℝ))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [ContinuousLinearMap.toLinearMap_smul, LinearMap.normDet_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht),
      Real.mul_rpow (pow_nonneg (inv_nonneg.mpr ht.le) _) (J t).toLinearMap.normDet_nonneg,
      one_div, Real.pow_rpow_inv_natCast (inv_nonneg.mpr ht.le) hm.ne']
    exact div_eq_inv_mul _ _
  have hd : HasDerivWithinAt (fun t ↦ (J t).toLinearMap.normDet ^ (1 / (m : ℝ)))
      1 (Ioi 0) 0 := by
    apply (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).mpr
    apply (hp.congr' heq.symm).congr'
    exact .of_forall fun t ↦ by rw [slope_def_field, hf0, sub_zero, sub_zero]
  exact hd.Ici_of_Ioi

end TauCeti
