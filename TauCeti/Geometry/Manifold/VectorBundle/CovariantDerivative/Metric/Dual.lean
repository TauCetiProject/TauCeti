/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Dual

/-!
# Metric duality and the induced covector connection

Lowering a vector-bundle section with a regular metric preserves its regularity. For a
metric-compatible connection, lowering also commutes with the induced Hom connection to the
trivial real line. Thus the duals of sections parallel at a point are parallel there too.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 4
  (induced connections and metric duality).
-/

public noncomputable section

open Bundle FiberBundle
open scoped ContDiff Manifold

namespace CovariantDerivative.IsMetricCompatible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  [IsContMDiffRiemannianBundle I 1 F V]
  {cov : CovariantDerivative I F V} {σ : Π x, V x} {x : M}

/-- Metric duality commutes with covariant differentiation for a metric-compatible connection.
The covector connection is the native Hom connection to the canonically trivial real line. -/
theorem hom_trivial_innerSL (hcov : cov.IsMetricCompatible) (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    cov.hom (CovariantDerivative.trivial (I := I) ℝ) (fun y ↦ innerSL ℝ (σ y)) x v =
      innerSL ℝ (cov σ x v) := by
  ext w
  let τ := extend F w
  have hτ : MDiffAt (T% τ) x := mdifferentiableAt_extend I F w
  have hw : τ x = w := extend_apply_self ..
  rw [← hw, hom_apply _ _ hσ.innerSL_bundle hτ, CovariantDerivative.trivial_apply]
  simp only [innerSL_apply_apply]
  rw [hcov.mvfderiv_inner_eq (fun _ ↦ v) hσ hτ]
  abel

end CovariantDerivative.IsMetricCompatible
