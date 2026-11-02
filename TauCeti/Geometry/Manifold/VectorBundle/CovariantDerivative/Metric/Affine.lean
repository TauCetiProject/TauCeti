/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic

/-!
# Affine operations on metric connections

On a real Riemannian vector bundle, adding an endomorphism-valued one-form to a metric
connection preserves metric compatibility exactly when its endomorphisms are skew-adjoint.
Equivalently, the difference of two metric connections is skew-adjoint in each tangent
direction. These statements describe the affine freedom in choosing a metric connection;
no torsion condition is imposed, even when the bundle is the tangent bundle.

We use Mathlib's `CovariantDerivative.addOneForm`, `CovariantDerivative.difference` and
`CovariantDerivative.derivMetricTensor`. Their argument order puts the section vector before
the tangent vector: the endomorphism in direction `X` is `(A x).flip X`.
Skew-adjointness is expressed by the real inner-product identity, without choosing a frame.
The metric defect is affine in the connection, so arbitrary point-dependent affine
combinations of metric connections are metric. No regularity of the weights is needed for
metric compatibility; regularity of the resulting connection is a separate question.

## Main results

* `CovariantDerivative.IsMetricCompatible.addOneForm_iff`: the skew-adjoint criterion.
* `CovariantDerivative.isMetricCompatible_iff_inner_difference_add_inner_difference_eq_zero`:
  the difference criterion relative to a fixed metric connection.
* `CovariantDerivative.IsMetricCompatible.inner_difference_add_inner_difference_eq_zero`:
  the difference of metric connections is skew-adjoint.
* `CovariantDerivative.IsMetricCompatible.affineCombination`: affine combinations preserve
  metric compatibility.

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I, Chapter II
  (differences of connections and metric connections).
-/

public section

noncomputable section

open Bundle FiberBundle
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  [IsContMDiffRiemannianBundle I 1 F V]
  {cov cov' : CovariantDerivative I F V}

/-- Adding an endomorphism-valued one-form changes the metric defect by the negative of
twice its symmetric part. The tangent direction is the last argument of `A`. -/
@[simp]
theorem derivMetricTensor_addOneForm (cov : CovariantDerivative I F V)
    (A : Π x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x)
    (x : M) (u v : V x) (X : TangentSpace I x) :
    (cov.addOneForm A).derivMetricTensor x u v X =
      cov.derivMetricTensor x u v X - inner ℝ (A x u X) v - inner ℝ u (A x v X) := by
  simp only [derivMetricTensor_apply_eq_extend, addOneForm_apply, add_apply,
    extend_apply_self, inner_add_left, inner_add_right]
  abel

/-- A perturbation of a metric connection by an endomorphism-valued one-form is metric
exactly when that one-form is skew-adjoint in every tangent direction. -/
theorem IsMetricCompatible.addOneForm_iff (hcov : cov.IsMetricCompatible)
    (A : Π x : M, V x →L[ℝ] TangentSpace I x →L[ℝ] V x) :
    (cov.addOneForm A).IsMetricCompatible ↔
      ∀ (x : M) (X : TangentSpace I x) (u v : V x),
        inner ℝ (A x u X) v + inner ℝ u (A x v X) = 0 := by
  rw [isMetricCompatible_iff_derivMetricTensor_eq_zero] at hcov ⊢
  constructor
  · intro h x X u v
    have heq := congrArg (fun T ↦ T x u v X) h
    simp only [derivMetricTensor_addOneForm, hcov, zero_apply] at heq
    linarith
  · intro h
    ext x u v X
    simp only [derivMetricTensor_addOneForm, hcov, zero_apply]
    linarith [h x X u v]

/-- The metric defect is affine in the connection, including for weights depending on the
base point. No derivative of the weight occurs. -/
@[simp]
theorem derivMetricTensor_affineCombination (cov cov' : CovariantDerivative I F V)
    (f : M → ℝ) (x : M) (u v : V x) (X : TangentSpace I x) :
    (cov.affineCombination cov' f).derivMetricTensor x u v X =
      f x * cov.derivMetricTensor x u v X + (1 - f x) * cov'.derivMetricTensor x u v X := by
  simp only [derivMetricTensor_apply_eq_extend, affineCombination_toFun, Pi.add_apply,
    Pi.smul_apply', Pi.sub_apply, Pi.one_apply, add_apply, smul_apply,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  ring

/-- Every point-dependent affine combination of metric connections is metric. The weights
need not be nonnegative. -/
theorem IsMetricCompatible.affineCombination (hcov : cov.IsMetricCompatible)
    (hcov' : cov'.IsMetricCompatible) (f : M → ℝ) :
    (cov.affineCombination cov' f).IsMetricCompatible := by
  rw [isMetricCompatible_iff_derivMetricTensor_eq_zero] at hcov hcov' ⊢
  ext x u v X
  simp only [derivMetricTensor_affineCombination, hcov, hcov', zero_apply, mul_zero, add_zero]

/-- Twice the symmetric part of the difference of two connections is the difference of their
metric defects, with the order reversed. -/
theorem inner_difference_add_inner_difference (cov cov' : CovariantDerivative I F V)
    (x : M) (X : TangentSpace I x) (u v : V x) :
    inner ℝ (cov.difference cov' x u X) v + inner ℝ u (cov.difference cov' x v X) =
      cov'.derivMetricTensor x u v X - cov.derivMetricTensor x u v X := by
  simp only [difference_apply_eq_extend, sub_apply, inner_sub_left, inner_sub_right,
    derivMetricTensor_apply_eq_extend]
  abel

/-- Relative to a fixed metric connection, a connection is metric exactly when their
endomorphism-valued difference is skew-adjoint in every tangent direction. -/
theorem isMetricCompatible_iff_inner_difference_add_inner_difference_eq_zero
    (hcov' : cov'.IsMetricCompatible) :
    cov.IsMetricCompatible ↔
      ∀ (x : M) (X : TangentSpace I x) (u v : V x),
        inner ℝ (cov.difference cov' x u X) v +
          inner ℝ u (cov.difference cov' x v X) = 0 := by
  rw [isMetricCompatible_iff_derivMetricTensor_eq_zero] at hcov' ⊢
  simp only [inner_difference_add_inner_difference, hcov', zero_apply, zero_sub, neg_eq_zero]
  constructor
  · intro h x X u v
    simp only [h, zero_apply]
  · intro h
    ext x u v X
    exact h x X u v

/-- The difference of two metric connections is a skew-adjoint endomorphism in every
tangent direction. -/
theorem IsMetricCompatible.inner_difference_add_inner_difference_eq_zero
    (hcov : cov.IsMetricCompatible) (hcov' : cov'.IsMetricCompatible)
    (x : M) (X : TangentSpace I x) (u v : V x) :
    inner ℝ (cov.difference cov' x u X) v + inner ℝ u (cov.difference cov' x v X) = 0 :=
  (isMetricCompatible_iff_inner_difference_add_inner_difference_eq_zero hcov').mp hcov x X u v

end CovariantDerivative
