/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Nondegenerate.Basic
public import TauCeti.Analysis.InnerProductSpace.Trace.Inverse
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Scalar curvature as the inverse-metric trace of Ricci curvature

The scalar curvature operation is the existing positive-metric scalar curvature. This file
compares its canonical Levi-Civita connection with any smooth Levi-Civita connection of the
same metric and identifies the trace used in metric variation.

## References

* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, CUP (2006), §2.3.
* [Poincaré Conjecture](https://github.com/frenzymath/PoincareConjecture).
* [Lean evaluation submissions](https://github.com/frenzymath/lean-eval-submissions).
-/

public section

open Bundle
open scoped Manifold ContDiff
noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- The scalar curvature of a positive metric is the inverse-metric trace of the Ricci
tensor of any of its smooth Levi-Civita connections. -/
theorem scalarCurvature_eq_trace_inverse_ricciTensor
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hcov : g.toNondegenerateMetric.IsLeviCivitaConnection cov) (x : M) :
    g.scalarCurvature x = TauCeti.traceCLM ℝ E
      ((g.toNondegenerateMetric x).inverse ∘L (cov.ricciTensor x).toContinuousBilinearMap) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _) :=
    inferInstance
  have hg (y : M) (v w : TangentSpace I y) : g.toNondegenerateMetric y v w = Inner.inner ℝ v w := by
    rw [g.toNondegenerateMetric_apply]
    rfl
  have hcurv : cov.curvatureTensor x =
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x := by
    apply CovariantDerivative.curvatureTensor_congr
    intro σ hσ y
    ext v
    exact hcov.uniqueness
      ((g.toNondegenerateMetric.isLeviCivitaConnection_iff_of_apply_eq_inner hg).mpr
        (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I))
      (hσ.mdifferentiableAt (by simp)) v
  have hRic : cov.ricciTensor x = (CovariantDerivative.leviCivitaConnection I M).ricciTensor x := by
    ext u v
    simp only [CovariantDerivative.ricciTensor_apply, hcurv]
  have htr := ContinuousLinearMap.traceCLM_inverse_comp_eq_metricTrace
    (g.toNondegenerateMetric x) (hg x) (cov.ricciTensor x).toContinuousBilinearMap
  -- Read the trace in the tangent fibre to apply the intrinsic metric contraction law.
  change g.scalarCurvature x = TauCeti.traceCLM ℝ (TangentSpace I x)
    ((g.toNondegenerateMetric x).inverse ∘L (cov.ricciTensor x).toContinuousBilinearMap)
  rw [htr, LinearMap.BilinForm.toBilinForm_toContinuousBilinearMap, hRic]
  rw [g.scalarCurvature_eq_scalarCurvature_leviCivitaConnection rfl,
    CovariantDerivative.scalarCurvature_apply]

end Bundle.ContMDiffRiemannianMetric
