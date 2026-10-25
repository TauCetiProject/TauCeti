/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.SingularSubspace.Basic
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Corollaries
public import TauCeti.Analysis.InnerProductSpace.Gram.Perturbation

/-!
# Gram perturbation bounds for singular subspaces

The right and left singular subspaces of a rectangular map are the spectral subspaces
of its source and target Gram operators. An interval/exterior spectral gap for two
corresponding Gram subspaces therefore bounds their directed sine by the change in
the rectangular map:

`delta * norm(sinTheta) <= (norm B + norm A) * norm(B - A)`.

The proof combines the interval/exterior Davis--Kahan theorem with the Gram
perturbation estimate. The spectral sets select squared singular values and may
be arbitrary and different for the two maps.

## References

* Y. Yu, T. Wang, R. J. Samworth, *A useful variant of the Davis--Kahan
  theorem for statisticians*, Biometrika **102** (2015), 315--323.
* Adapted from the Kitware DKPS formalization (Apache-2.0),
  `YuWangSamworth2015/Core/SingularSubspace.lean`.
-/

public section

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- Under an interval/exterior gap between right Gram spectral blocks, the directed
sine of the selected right singular subspaces is controlled by the rectangular
operator perturbation. The two spectral selections may be arbitrary and distinct. -/
theorem mul_norm_sinThetaMap_rightSingularSubspace_le (A B : E →ₗ[𝕜] F)
    {s t : Set ℝ} {a b δ : ℝ}
    (hgap : Module.End.PointIntervalExteriorGap (A.adjoint ∘ₗ A)
      (A.rightSingularSubspace s) (B.adjoint ∘ₗ B)
      (B.rightSingularSubspace t)ᗮ a b δ) :
    δ * ‖(A.rightSingularSubspace s).sinThetaMap (B.rightSingularSubspace t)‖ ≤
      (‖B.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
        ‖B.toContinuousLinearMap - A.toContinuousLinearMap‖ := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  let P : E →L[𝕜] E := (A.adjoint ∘ₗ A).toContinuousLinearMap
  let Q : E →L[𝕜] E := (B.adjoint ∘ₗ B).toContinuousLinearMap
  have hP : (P : E →ₗ[𝕜] E).IsSymmetric := by
    simpa only [P, coe_toContinuousLinearMap] using A.isSymmetric_adjoint_comp_self
  have hQ : (Q : E →ₗ[𝕜] E).IsSymmetric := by
    simpa only [Q, coe_toContinuousLinearMap] using B.isSymmetric_adjoint_comp_self
  have hU : ∀ x ∈ A.rightSingularSubspace s, P x ∈ A.rightSingularSubspace s := by
    intro x hx
    simpa only [P, coe_toContinuousLinearMap'] using
      (A.map_rightSingularSubspace_le s) (Submodule.mem_map_of_mem hx)
  have hV : ∀ x ∈ B.rightSingularSubspace t, Q x ∈ B.rightSingularSubspace t := by
    intro x hx
    simpa only [Q, coe_toContinuousLinearMap'] using
      (B.map_rightSingularSubspace_le t) (Submodule.mem_map_of_mem hx)
  have hgap' : Module.End.PointIntervalExteriorGap (P : E →ₗ[𝕜] E)
      (A.rightSingularSubspace s) (Q : E →ₗ[𝕜] E)
      (B.rightSingularSubspace t)ᗮ a b δ := by
    simpa only [P, Q, coe_toContinuousLinearMap] using hgap
  have hdk := Submodule.mul_norm_sinThetaMap_le_norm_sub_of_pointIntervalExteriorGap
    (A.rightSingularSubspace s) (B.rightSingularSubspace t) hP hQ hU hV hgap'
  refine hdk.trans ?_
  simpa only [P, Q, toContinuousLinearMap_comp, adjoint_toContinuousLinearMap] using
    (ContinuousLinearMap.norm_adjoint_comp_self_sub_adjoint_comp_self_le
      B.toContinuousLinearMap A.toContinuousLinearMap)

/-- Under an interval/exterior gap between left Gram spectral blocks, the directed
sine of the selected left singular subspaces is controlled by the rectangular
operator perturbation. The two spectral selections may be arbitrary and distinct. -/
theorem mul_norm_sinThetaMap_leftSingularSubspace_le (A B : E →ₗ[𝕜] F)
    {s t : Set ℝ} {a b δ : ℝ}
    (hgap : Module.End.PointIntervalExteriorGap (A ∘ₗ A.adjoint)
      (A.leftSingularSubspace s) (B ∘ₗ B.adjoint)
      (B.leftSingularSubspace t)ᗮ a b δ) :
    δ * ‖(A.leftSingularSubspace s).sinThetaMap (B.leftSingularSubspace t)‖ ≤
      (‖B.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
        ‖B.toContinuousLinearMap - A.toContinuousLinearMap‖ := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  let : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  have h := mul_norm_sinThetaMap_rightSingularSubspace_le
    A.adjoint B.adjoint (s := s) (t := t)
    (by simpa only [adjoint_adjoint, rightSingularSubspace_adjoint] using hgap)
  simpa only [rightSingularSubspace_adjoint, adjoint_toContinuousLinearMap,
    ← ContinuousLinearMap.adjoint.map_sub, ContinuousLinearMap.adjoint.norm_map] using h

end LinearMap
