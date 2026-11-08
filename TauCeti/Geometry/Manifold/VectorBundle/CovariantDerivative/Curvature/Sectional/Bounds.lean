/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
/-!
# Sectional-curvature bounds with one fixed direction

A sectional-curvature upper or lower bound on the two-planes containing a fixed vector is
equivalent to the corresponding bound on all curvature numerators with that vector in the
second slot. Dependent pairs have zero curvature numerator and Gram determinant, so the
numerator formulation covers them as well. This is the interface for radial curvature bounds.
-/

public noncomputable section
open Bundle
open scoped ContDiff InnerProductSpace Manifold Matrix
namespace CovariantDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)

omit [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)] in
/-- For a linearly dependent pair, the curvature numerator and the Gram determinant vanish. -/
private theorem inner_curvatureTensor_eq_zero_and_det_gram_eq_zero {x : M}
    {u v : TangentSpace I x} (huv : ¬LinearIndependent ℝ ![u, v]) :
    inner ℝ (curvature x u v v) u = 0 ∧ (Matrix.gram ℝ ![u, v]).det = 0 := by
  by_cases hu : u = 0
  · simp [hu, Matrix.real_det_gram_fin_two]
  · obtain ⟨c, hc⟩ := not_forall.mp ((LinearIndependent.pair_iff' hu).not.mp huv)
    rw [← not_not.mp hc]
    simp only [map_smul, cov.curvatureTensor_self, LinearMap.zero_apply, smul_zero,
      inner_zero_left, Matrix.real_det_gram_fin_two, real_inner_smul_left,
      real_inner_smul_right, true_and]
    ring

/-- An upper sectional bound on planes through a fixed vector bounds every curvature numerator. -/
theorem forall_sectionalCurvature_le_fixed_iff (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov) (x : M) (v : TangentSpace I x) (κ : ℝ) :
    (∀ u : TangentSpace I x, LinearIndependent ℝ ![u, v] →
      cov.sectionalCurvature hcov x u v ≤ κ) ↔
    ∀ u : TangentSpace I x,
      inner ℝ (curvature x u v v) u ≤ κ * (Matrix.gram ℝ ![u, v]).det := by
  refine ⟨fun h u ↦ ?_, fun h u huv ↦ ?_⟩
  · by_cases huv : LinearIndependent ℝ ![u, v]
    · have hh := h u huv
      rw [sectionalCurvature_apply] at hh
      exact (div_le_iff₀ (Matrix.posDef_gram_of_linearIndependent huv).det_pos).1 hh
    · obtain ⟨h₁, h₂⟩ := cov.inner_curvatureTensor_eq_zero_and_det_gram_eq_zero huv
      rw [h₁, h₂, mul_zero]
  · rw [sectionalCurvature_apply]
    exact (div_le_iff₀ (Matrix.posDef_gram_of_linearIndependent huv).det_pos).2 (h u)

/-- A lower sectional bound on planes through a fixed vector bounds every curvature numerator. -/
theorem forall_le_sectionalCurvature_fixed_iff (hcov : CovariantDerivative.IsMetricCompatible
    (V := fun x : M ↦ TangentSpace I x) cov) (x : M) (v : TangentSpace I x) (κ : ℝ) :
    (∀ u : TangentSpace I x, LinearIndependent ℝ ![u, v] →
      κ ≤ cov.sectionalCurvature hcov x u v) ↔
    ∀ u : TangentSpace I x,
      κ * (Matrix.gram ℝ ![u, v]).det ≤ inner ℝ (curvature x u v v) u := by
  refine ⟨fun h u ↦ ?_, fun h u huv ↦ ?_⟩
  · by_cases huv : LinearIndependent ℝ ![u, v]
    · have hh := h u huv
      rw [sectionalCurvature_apply] at hh
      exact (le_div_iff₀ (Matrix.posDef_gram_of_linearIndependent huv).det_pos).1 hh
    · obtain ⟨h₁, h₂⟩ := cov.inner_curvatureTensor_eq_zero_and_det_gram_eq_zero huv
      rw [h₁, h₂, mul_zero]
  · rw [sectionalCurvature_apply]
    exact (le_div_iff₀ (Matrix.posDef_gram_of_linearIndependent huv).det_pos).2 (h u)

end CovariantDerivative
