/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative.Basic
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear

/-!
# The covariant derivative of the curvature as a two-form

Let `∇` be a smooth connection on a vector bundle `V` with curvature `R`, and let `∇ᵀ` be a
connection on the tangent bundle. At a point `x`, the covariant derivative `∇_v R` of the curvature
(`CovariantDerivative.derivCurvatureTensor`) is antisymmetric in its two curvature arguments, so it
is a two-form on `T_x M` with values in the endomorphisms of `V x`,
`CovariantDerivative.derivCurvatureForm`, with `u ∧ w ↦ (∇_v R)(u, w)`, depending linearly on `v`.
This is the same packaging that `CovariantDerivative.curvatureForm` gives the curvature itself.

For a smooth torsion-free `∇ᵀ`, the second Bianchi identity
`(∇_u R)(v, w) + (∇_v R)(w, u) + (∇_w R)(u, v) = 0`
(`CovariantDerivative.derivCurvatureTensor_cyclic_eq_zero`) becomes a cyclic identity for these
two-forms. No metric, orientation or dimension assumption is needed here.

## Main definitions

* `CovariantDerivative.derivCurvatureForm`: the covariant derivative `∇_v R` of the curvature at a
  point, as an endomorphism-valued two-form.

## Main results

* `CovariantDerivative.derivCurvatureForm_apply_ιMulti`: `(∇_v R)(u ∧ w) = (∇_v R)(u, w)`.
* `CovariantDerivative.derivCurvatureForm_cyclic_eq_zero`: the second Bianchi identity for these
  forms.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 7.
-/

public section

open Bundle exteriorPower
open scoped ContDiff Manifold

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  (cov : CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  (covT : CovariantDerivative I E (TangentSpace I : M → Type _))

/-- The covariant derivative `∇_v R` of the curvature of `∇` at `x`, as a two-form on `T_x M`
with values in the endomorphisms of `V x`: `u ∧ w ↦ (∇_v R)(u, w)`, depending linearly on `v`. -/
def derivCurvatureForm (x : M) :
    TangentSpace I x →ₗ[ℝ] ⋀[ℝ]^2 (TangentSpace I x) →ₗ[ℝ] (V x →ₗ[ℝ] V x) where
  toFun v := alternatingMapLinearEquiv
    (LinearMap.IsAlt.toAlternatingMap
      -- `IsAlt` unfolds to `∀ u, B u u = 0`, the statement of `derivCurvatureTensor_self`.
      (show (cov.derivCurvatureTensor covT x v).IsAlt from cov.derivCurvatureTensor_self covT x v))
  map_add' v v' := by
    rw [← map_add]
    congr 1
    ext w
    simp
  map_smul' c v := by
    rw [← map_smul]
    congr 1
    ext w
    simp

/-- The two-form `∇_v R` evaluates on `u ∧ w` to `(∇_v R)(u, w)`. -/
@[simp]
theorem derivCurvatureForm_apply_ιMulti (x : M) (v u w : TangentSpace I x) :
    cov.derivCurvatureForm covT x v (ιMulti ℝ 2 ![u, w]) =
      cov.derivCurvatureTensor covT x v u w := by
  simp [derivCurvatureForm, alternatingMapLinearEquiv_apply_ιMulti]

/-- **The second Bianchi identity** for the two-forms `∇_v R`:
`(∇_u R)(v ∧ w) + (∇_v R)(w ∧ u) + (∇_w R)(u ∧ v) = 0`, for a smooth torsion-free `∇ᵀ`. -/
theorem derivCurvatureForm_cyclic_eq_zero [ContMDiffCovariantDerivative covT ∞]
    (ht : covT.torsion = 0) (x : M) (u v w : TangentSpace I x) :
    cov.derivCurvatureForm covT x u (ιMulti ℝ 2 ![v, w]) +
        cov.derivCurvatureForm covT x v (ιMulti ℝ 2 ![w, u]) +
      cov.derivCurvatureForm covT x w (ιMulti ℝ 2 ![u, v]) = 0 := by
  simpa using cov.derivCurvatureTensor_cyclic_eq_zero covT ht x u v w

end CovariantDerivative
