/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
import TauCeti.LinearAlgebra.Multilinear.SectionalPolarization

/-!
# The metric-lowered Riemann curvature tensor

Pairing the output of the pointwise `(1,3)` curvature tensor with the metric gives the
`(0,4)` Riemann curvature tensor

`Rm(u, v, w, z) = ⟨R(u, v)w, z⟩`.

This file bundles that expression as a quadrilinear map and records its algebraic symmetries.
Every connection gives antisymmetry in the first pair. Metric compatibility gives antisymmetry
in the last pair, torsion-freeness gives the first Bianchi identity, and together these imply
pair-interchange symmetry. The latter symmetry also makes the Ricci contraction symmetric.
By polarization, these symmetries determine `Rm` from its values `Rm(u, v, v, u)` on linearly
independent pairs `u, v`, the numerators of the sectional curvatures.

The sign and argument conventions follow J. M. Lee, *Introduction to Riemannian Manifolds*,
2nd ed., Springer GTM 176 (2018), Chapter 7.

## Main declarations

* `CovariantDerivative.riemannCurvatureTensor`: the metric-lowered curvature tensor.
* `CovariantDerivative.IsMetricCompatible.riemannCurvatureTensor_swap_pairs`:
  pair-interchange symmetry.
* `CovariantDerivative.IsMetricCompatible.riemannCurvatureTensor_eq_of_forall_linearIndependent`:
  `Rm` is the unique tensor with the curvature symmetries and the same values `T(u, v, v, u)` on
  linearly independent pairs.
* `CovariantDerivative.IsMetricCompatible.ricciTensor_comm` and
  `CovariantDerivative.IsMetricCompatible.ricciTensor_isSymm`: symmetry of Ricci curvature.
* `CovariantDerivative.ricciTensor_eq_sum_riemannCurvatureTensor` and
  `CovariantDerivative.scalarCurvature_eq_sum_riemannCurvatureTensor`: the Ricci and scalar
  contractions in an orthonormal basis.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)

/-- The metric-lowered Riemann curvature tensor, with convention
`Rm(u, v, w, z) = ⟨R(u, v)w, z⟩`. -/
def riemannCurvatureTensor (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ]
      TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v ↦ LinearMap.BilinForm.compLeft (innerₗ (TangentSpace I x)) (curvature x u v))
    (fun u u' v ↦ by ext w z; simp)
    (fun c u v ↦ by ext w z; simp)
    (fun u v v' ↦ by ext w z; simp)
    (fun c u v ↦ by ext w z; simp)

/-- Evaluation of the metric-lowered Riemann curvature tensor. -/
@[simp]
theorem riemannCurvatureTensor_apply (x : M) (u v w z : TangentSpace I x) :
    cov.riemannCurvatureTensor x u v w z = inner ℝ (curvature x u v w) z :=
  (rfl)

/-- In an orthonormal basis, Ricci curvature is the contraction of the first and fourth
arguments of the Riemann curvature tensor. -/
theorem ricciTensor_eq_sum_riemannCurvatureTensor {i : Type*} [Fintype i] (x : M)
    (b : OrthonormalBasis i ℝ (TangentSpace I x)) (u v : TangentSpace I x) :
    cov.ricciTensor x u v = ∑ j, cov.riemannCurvatureTensor x (b j) u v (b j) := by
  rw [cov.ricciTensor_eq_sum_inner x b u v]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [riemannCurvatureTensor_apply, real_inner_comm]

/-- In an orthonormal basis, scalar curvature is the double contraction of the Riemann
curvature tensor. -/
theorem scalarCurvature_eq_sum_riemannCurvatureTensor {i : Type*} [Fintype i] (x : M)
    (b : OrthonormalBasis i ℝ (TangentSpace I x)) :
    cov.scalarCurvature x =
      ∑ j, ∑ k, cov.riemannCurvatureTensor x (b k) (b j) (b j) (b k) := by
  rw [cov.scalarCurvature_eq_sum_inner_curvatureTensor x b]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  rw [riemannCurvatureTensor_apply, real_inner_comm]

/-- The Riemann curvature tensor is antisymmetric in its first pair of arguments. -/
theorem riemannCurvatureTensor_antisymm_first (x : M) (u v w z : TangentSpace I x) :
    cov.riemannCurvatureTensor x u v w z =
      -cov.riemannCurvatureTensor x v u w z := by
  rw [riemannCurvatureTensor_apply, riemannCurvatureTensor_apply,
    cov.curvatureTensor_antisymm x u v, LinearMap.neg_apply, inner_neg_left]

/-- For a torsion-free connection, the cyclic sum of the first three arguments of the Riemann
curvature tensor vanishes. -/
theorem riemannCurvatureTensor_cyclic_eq_zero (ht : cov.torsion = 0)
    (x : M) (u v w z : TangentSpace I x) :
    cov.riemannCurvatureTensor x u v w z +
        cov.riemannCurvatureTensor x v w u z +
      cov.riemannCurvatureTensor x w u v z = 0 := by
  simpa only [riemannCurvatureTensor_apply, inner_add_left, inner_zero_left] using
    congrArg (fun q ↦ inner ℝ q z) (cov.curvatureTensor_cyclic_eq_zero ht x u v w)

variable [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

/-- For a metric-compatible connection, the Riemann curvature tensor is antisymmetric in its
last pair of arguments. -/
theorem IsMetricCompatible.riemannCurvatureTensor_antisymm_last
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov)
    (x : M) (u v w z : TangentSpace I x) :
    cov.riemannCurvatureTensor x u v w z =
      -cov.riemannCurvatureTensor x u v z w := by
  simpa only [riemannCurvatureTensor_apply, real_inner_comm] using
    hcov.inner_curvatureTensor_eq_neg x u v w z

/-- The Riemann curvature tensor of a metric-compatible torsion-free connection is unchanged
when its two pairs of arguments are interchanged. -/
theorem IsMetricCompatible.riemannCurvatureTensor_swap_pairs
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (x : M) (u v w z : TangentSpace I x) :
    cov.riemannCurvatureTensor x u v w z =
      cov.riemannCurvatureTensor x w z u v := by
  simpa only [riemannCurvatureTensor_apply] using
    hcov.inner_curvatureTensor_swap_pairs ht x u v w z

variable {cov} in
/-- For a metric-compatible torsion-free connection, the Riemann curvature tensor at `x` is the
only quadrilinear form with the algebraic symmetries of a curvature tensor whose values
`T(u, v, v, u)` on linearly independent pairs are the sectional-curvature numerators
`⟨R(u, v)v, u⟩`. -/
theorem IsMetricCompatible.riemannCurvatureTensor_eq_of_forall_linearIndependent
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0) (x : M)
    {T : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ]
      TangentSpace I x →ₗ[ℝ] ℝ}
    (h₁ : ∀ u v w z, T u v w z = -T v u w z) (h₂ : ∀ u v w z, T u v w z = -T u v z w)
    (h₃ : ∀ u v w z, T u v w z + T v w u z + T w u v z = 0)
    (hT : ∀ u v, LinearIndependent ℝ ![u, v] → cov.riemannCurvatureTensor x u v v u = T u v v u) :
    cov.riemannCurvatureTensor x = T :=
  LinearMap.eq_of_cyclic_eq_zero_of_linearIndependent (by norm_num)
    (cov.riemannCurvatureTensor_antisymm_first x)
    (IsMetricCompatible.riemannCurvatureTensor_antisymm_last cov hcov x)
    (cov.riemannCurvatureTensor_cyclic_eq_zero ht x) h₁ h₂ h₃ hT

end CovariantDerivative
