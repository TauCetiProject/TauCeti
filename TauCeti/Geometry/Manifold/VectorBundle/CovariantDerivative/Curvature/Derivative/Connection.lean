/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative.Smoothness
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The induced connection on the curvature tensor

The curvature tensor is a section of `Hom(TM, Hom(TM, End(V)))`. The connections on
`TM` and `V` induce a connection on this bundle by three applications of
`CovariantDerivative.hom`. Its derivative of curvature agrees with
`CovariantDerivative.derivCurvatureTensorCLM`.

This comparison permits further covariant differentiation of curvature using the native
Hom-bundle connections, while retaining the existing pointwise tensor and its identities.
Neither metric compatibility nor vanishing torsion is required.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 4 and 7
  (induced tensor connections and covariant derivatives of curvature).
-/

public noncomputable section

open Bundle FiberBundle
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- The covariant derivative of curvature is the derivative for the connection induced on
`Hom(TM, Hom(TM, End(V)))`. The tangent connection need not be torsion-free or smooth. -/
theorem derivCurvatureTensorCLM_eq_hom (x : M) :
    cov.derivCurvatureTensorCLM covT x =
      (covT.hom (covT.hom (cov.hom cov))) cov.curvatureTensorCLM x := by
  -- Cache the nested operator norms to bound instance search for the Hom-bundle evaluations.
  let _ : NormedAddCommGroup (F →L[ℝ] F) := inferInstance
  let _ : NormedSpace ℝ (F →L[ℝ] F) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] F →L[ℝ] F) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] F →L[ℝ] F) := inferInstance
  let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F →L[ℝ] F) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F →L[ℝ] F) := inferInstance
  ext v u w z
  obtain ⟨Y, hY, rfl⟩ := exists_contMDiff_section_eq I E ∞ u
  obtain ⟨Z, hZ, rfl⟩ := exists_contMDiff_section_eq I E ∞ w
  obtain ⟨σ, hσ, rfl⟩ := exists_contMDiff_section_eq I F ∞ z
  have hR : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] F →L[ℝ] F)) ∞
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] F →L[ℝ] F) y
        (cov.curvatureTensorCLM y)) := cov.contMDiff_curvatureTensorCLM
  have hRY := hR.clm_bundle_apply hY
  have hRYZ := hRY.clm_bundle_apply hZ
  rw [derivCurvatureTensorCLM_apply, cov.derivCurvatureTensor_apply covT x v hY hZ hσ,
    hom_apply _ _ (hR.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp)),
    sub_apply, sub_apply,
    hom_apply _ _ (hRY.mdifferentiableAt (by simp)) (hZ.mdifferentiableAt (by simp)),
    sub_apply,
    hom_apply _ _ (hRYZ.mdifferentiableAt (by simp)) (hσ.mdifferentiableAt (by simp))]
  simp only [curvatureTensorCLM_apply]
  have heq : (fun y ↦ cov.curvatureTensor y (Y y) (Z y) (σ y)) =
      cov.curvatureOperator Y Z σ := by
    ext y
    exact cov.curvatureTensor_apply y hY hZ hσ
  rw [heq]
  abel

end CovariantDerivative
