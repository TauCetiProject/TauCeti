/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Comparison.Area.Basic
public import TauCeti.Analysis.Green.DifferentialForm
public import TauCeti.Topology.Algebra.Module.Alternating.TopDegree

/-!
# The planar exterior derivative as an actual area form

The curl coefficient determines the entire top form, by the determinant formula in an actual
tangent basis. Thus the exterior derivative of the circulation form is the curl times the
canonical manifold area form, rather than merely agreeing on one chosen tuple.
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti.Green

/-- The actual planar manifold exterior derivative is curl times the normalized area form. -/
theorem _root_.DifferentiableAt.mextDeriv_manifoldOneForm_eq_smul_area {P Q : ℂ → ℝ} {z : ℂ}
    (hP : DifferentiableAt ℝ P z) (hQ : DifferentiableAt ℝ Q z) :
    mextDeriv (manifoldOneForm P Q) z = curl P Q z • manifoldAreaForm z := by
  let ω : ℂ [⋀^Fin 2]→L[ℝ] ℝ :=
    (mextDeriv (manifoldOneForm P Q) z).compContinuousLinearMap
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) z).symm.toContinuousLinearMap
  have hc : ω Complex.basisOneI = curl P Q z := by
    simp only [ω, ContinuousAlternatingMap.compContinuousLinearMap_apply,
      ContinuousLinearEquiv.coe_coe, Complex.coe_basisOneI]
    exact DifferentiableAt.mextDeriv_manifoldOneForm_apply hP hQ
  have he : ω = curl P Q z • complexAreaForm := by
    ext v
    rw [ContinuousAlternatingMap.apply_eq_det_mul (ω := ω) (b := Complex.basisOneI),
      ContinuousAlternatingMap.smul_apply,
      ContinuousAlternatingMap.apply_eq_det_mul (ω := complexAreaForm)
        (b := Complex.basisOneI), hc, Complex.coe_basisOneI, complexAreaForm_one_I, mul_one,
      smul_eq_mul]
    ring
  ext v
  have hv := congrArg (fun L : ℂ [⋀^Fin 2]→L[ℝ] ℝ ↦
    L (fun i ↦ NormedSpace.fromTangentSpace (𝕜 := ℝ) z (v i))) he
  simp only [ω, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousAlternatingMap.smul_apply] at hv
  exact hv.trans (congrArg (fun r : ℝ ↦ curl P Q z • r)
    (manifoldAreaForm_apply z v).symm)

end TauCeti.Green
