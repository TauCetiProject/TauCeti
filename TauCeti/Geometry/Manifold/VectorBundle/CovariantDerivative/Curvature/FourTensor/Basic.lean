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
* `CovariantDerivative.curvatureFourTensor_antisymm_first`
* `CovariantDerivative.ricci_curvatureFourTensor`
* `CovariantDerivative.scalar_curvatureFourTensor`
* `CovariantDerivative.curvatureFourTensor_eq_smul_constantCurvature`
* `CovariantDerivative.IsMetricCompatible.curvatureFourTensor_antisymm_last`
* `CovariantDerivative.IsMetricCompatible.isAlgebraicCurvature_curvatureFourTensor`
* `CovariantDerivative.IsMetricCompatible.algebraicCurvature`
* `CovariantDerivative.IsMetricCompatible.coe_algebraicCurvature`
* `CovariantDerivative.curvatureFourTensor_leviCivitaConnection_mem_algebraicCurvatureSubmodule`

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

/-- `curvatureFourTensor` is antisymmetric in its first pair of arguments. -/
theorem curvatureFourTensor_antisymm_first (x : M) (u v z w : TangentSpace I x) :
    cov.curvatureFourTensor x ![u, v, z, w] = -cov.curvatureFourTensor x ![v, u, z, w] := by
  simpa only [cov.curvatureFourTensor_eq_riemannCurvatureTensor] using
    cov.riemannCurvatureTensor_antisymm_first x u v w z

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

section MetricCompatible

variable [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]

/-- For a metric-compatible connection, `curvatureFourTensor` is antisymmetric in its last pair
of arguments. -/
theorem IsMetricCompatible.curvatureFourTensor_antisymm_last
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (x : M) (u v z w : TangentSpace I x) :
    cov.curvatureFourTensor x ![u, v, z, w] = -cov.curvatureFourTensor x ![u, v, w, z] := by
  simpa only [cov.curvatureFourTensor_eq_riemannCurvatureTensor] using
    hcov.riemannCurvatureTensor_antisymm_last cov x u v w z

/-- For a metric-compatible torsion-free connection, `curvatureFourTensor x` satisfies the
algebraic curvature symmetries. -/
theorem IsMetricCompatible.isAlgebraicCurvature_curvatureFourTensor
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) : IsAlgebraicCurvature (cov.curvatureFourTensor x) where
  antisymm_first := cov.curvatureFourTensor_antisymm_first x
  antisymm_last := hcov.curvatureFourTensor_antisymm_last cov x
  swap_pairs u v z w := by
    simp only [cov.curvatureFourTensor_eq_riemannCurvatureTensor]
    rw [hcov.riemannCurvatureTensor_swap_pairs cov ht x u v w z,
      cov.riemannCurvatureTensor_antisymm_first x w z u v,
      hcov.riemannCurvatureTensor_antisymm_last cov x z w u v, neg_neg]
  cyclic_eq_zero u v z w := by
    simp only [cov.curvatureFourTensor_eq_riemannCurvatureTensor]
    linarith [cov.riemannCurvatureTensor_cyclic_eq_zero ht x u v z w,
      hcov.riemannCurvatureTensor_antisymm_last cov x u v w z,
      hcov.riemannCurvatureTensor_antisymm_last cov x v z w u,
      hcov.riemannCurvatureTensor_antisymm_last cov x z u w v]

/-- `curvatureFourTensor x` bundled in `algebraicCurvatureSubmodule (TangentSpace I x)`. -/
def IsMetricCompatible.algebraicCurvature
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) : algebraicCurvatureSubmodule (TangentSpace I x) :=
  ⟨cov.curvatureFourTensor x, mem_algebraicCurvatureSubmodule.2
    (hcov.isAlgebraicCurvature_curvatureFourTensor cov ht x)⟩

/-- Coercion of `IsMetricCompatible.algebraicCurvature` to `FourTensor`. -/
@[simp]
theorem IsMetricCompatible.coe_algebraicCurvature
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) :
    (hcov.algebraicCurvature cov ht x).val = cov.curvatureFourTensor x := (rfl)

end MetricCompatible

/-- The curvature four-tensor of the Levi-Civita connection of the fibre metric is an algebraic
curvature tensor at every point. -/
theorem curvatureFourTensor_leviCivitaConnection_mem_algebraicCurvatureSubmodule
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] (x : M) :
    (leviCivitaConnection I M).curvatureFourTensor x ∈
      algebraicCurvatureSubmodule (TangentSpace I x) :=
  mem_algebraicCurvatureSubmodule.mpr <|
    (isMetricCompatible_leviCivitaConnection I).isAlgebraicCurvature_curvatureFourTensor _
      (torsion_leviCivitaConnection_eq_zero I) x

end FourTensor

end CovariantDerivative
