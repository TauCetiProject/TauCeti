/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.ChartGram.Family

/-!
# Chart Gram matrices for families of metric-indexed manifolds

The chart Gram matrix on `WithMetric g` is jointly continuous in the metric parameter and
the spatial point wherever the metric tensor is jointly continuous in a fixed chart.
-/

public noncomputable section

open Bundle Set Riemannian.Tensor
open scoped ContDiff Manifold Topology

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

variable {A : Type*} [TopologicalSpace A] {n : ℕ∞ω}

/-- The full chart Gram matrix on the metric-indexed copy is jointly continuous on any set
where the metric family is continuous and the points lie in a fixed chart base set. -/
theorem continuousOn_chartGramMatrix_toWithMetric_family
    (g : A → ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _))
    {S : Set (A × M)}
    (hg : ContinuousOn (fun q : A × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
      q.2 ((g q.1).inner q.2)) S)
    (α : M) (hS : ∀ q ∈ S, q.2 ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ContinuousOn (fun q : A × M ↦ chartGramMatrix (I := I)
      (WithMetric.toWithMetric (g q.1) α) (WithMetric.toWithMetric (g q.1) q.2)) S := by
  refine continuousOn_pi.mpr fun i ↦ continuousOn_pi.mpr fun j ↦ ?_
  refine (continuousOn_chartGramMatrix_family
    (fun a ↦ (g a).toContinuousRiemannianMetric) hg α hS i j).congr fun q _ ↦ ?_
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨(g q.1).toRiemannianMetric⟩
  -- Reduce the local metric instance, then transport both coefficients by the named identities.
  dsimp only
  rw [ContMDiffRiemannianMetric.chartGramMatrix_toWithMetric, Matrix.of_apply,
    chartGramMatrix_apply]
  exact (ContMDiffRiemannianMetric.inner_riemannianBundle (g q.1) _ _ _).symm

end TauCeti.Manifold
