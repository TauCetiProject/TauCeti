/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Riemann
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# The pointwise `(0, 4)` curvature tensor

Pairing the `(1, 3)` curvature tensor with the fibre inner product via
`r ![u, v, z, w] = ⟪R(u, v)w, z⟫` defines `CovariantDerivative.curvatureFourTensor cov x`.
Its algebraic Ricci and scalar contractions match `CovariantDerivative.ricciTensor` and
`CovariantDerivative.scalarCurvature`.

## Main definitions & statements

* `CovariantDerivative.curvatureFourTensor`
* `CovariantDerivative.curvatureFourTensor_eq_riemannCurvatureTensor`
* `CovariantDerivative.curvatureFourTensor_apply`
* `CovariantDerivative.ricci_curvatureFourTensor`
* `CovariantDerivative.scalar_curvatureFourTensor`
* `CovariantDerivative.curvatureFourTensor_eq_smul_constantCurvature`

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer (2018), Chapters 7–8.
-/

public section

open Bundle TauCeti TauCeti.FourTensor
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace CovariantDerivative

section FourTensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
  [ContMDiffCovariantDerivative cov ∞]

/-- The pointwise `(0, 4)` curvature tensor `r ![u, v, z, w] = ⟪R(u, v)w, z⟫`. -/
def curvatureFourTensor (x : M) : FourTensor (TangentSpace I x) :=
  ofLinearMap₄ <| LinearMap.mk₂ ℝ (fun u v ↦ (cov.riemannCurvatureTensor x u v).flip)
    (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp)
    (fun _ _ _ ↦ by ext; simp) (fun _ _ _ ↦ by ext; simp)

/-- `curvatureFourTensor` agrees with `riemannCurvatureTensor` with the last two slots swapped. -/
theorem curvatureFourTensor_eq_riemannCurvatureTensor (x : M) (u v z w : TangentSpace I x) :
    cov.curvatureFourTensor x ![u, v, z, w] = cov.riemannCurvatureTensor x u v w z := by
  simp [curvatureFourTensor]

/-- Evaluation of `curvatureFourTensor` on `![u, v, z, w]`. -/
@[simp]
theorem curvatureFourTensor_apply (x : M) (u v z w : TangentSpace I x) :
    cov.curvatureFourTensor x ![u, v, z, w] = inner ℝ (cov.curvatureTensor x u v w) z := by
  rw [cov.curvatureFourTensor_eq_riemannCurvatureTensor, cov.riemannCurvatureTensor_apply]

/-- The algebraic Ricci contraction of `curvatureFourTensor` is `ricciTensor`. -/
@[simp]
theorem ricci_curvatureFourTensor (x : M) :
    ricci (cov.curvatureFourTensor x) = cov.ricciTensor x := by
  ext u v; let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [ricci_apply_orthonormalBasis b, cov.ricciTensor_eq_sum_riemannCurvatureTensor x b]
  simp [cov.curvatureFourTensor_eq_riemannCurvatureTensor]

/-- The algebraic scalar contraction of `curvatureFourTensor` is `scalarCurvature`. -/
@[simp]
theorem scalar_curvatureFourTensor (x : M) :
    scalar (cov.curvatureFourTensor x) = cov.scalarCurvature x := by
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [scalar_apply_orthonormalBasis b, cov.scalarCurvature_eq_sum_riemannCurvatureTensor x b]
  simp [cov.curvatureFourTensor_eq_riemannCurvatureTensor]

/-- If the curvature of `cov` at `x` has the constant-curvature form
`R(w, u)v = κ (⟪u, v⟫ w - ⟪w, v⟫ u)`, its curvature four-tensor is `κ` times the
constant-curvature tensor. -/
theorem curvatureFourTensor_eq_smul_constantCurvature (x : M) {κ : ℝ}
    (h : ∀ w u v : TangentSpace I x,
      cov.curvatureTensor x w u v = κ • (⟪u, v⟫_ℝ • w - ⟪w, v⟫_ℝ • u)) :
    cov.curvatureFourTensor x = κ • constantCurvature (TangentSpace I x) := by
  refine ext_vec fun u v z w ↦ ?_
  rw [_root_.smul_apply, curvatureFourTensor_apply, smul_eq_mul]
  exact inner_eq_mul_constantCurvature h _ _ _ _

end FourTensor

end CovariantDerivative
