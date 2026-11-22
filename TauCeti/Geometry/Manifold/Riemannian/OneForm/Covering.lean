/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Covering
public import TauCeti.Geometry.Manifold.Riemannian.OneForm.Pullback

/-!
# Metric-dual flows on Riemannian coverings

Along a Riemannian covering, a one-form pulled back from the base has the same maximal
metric-dual trajectory interval through a point as the original form has through its image.
The flows agree after projection on that common interval. A constant real rescaling includes
both the ascending and descending flows of a closed one-form. The descending comparison
lets one study trajectories on a period cover using a primitive of the pulled-back form.
-/

public section

open Bundle
open scoped ContDiff Manifold

namespace TauCeti.IsLocalRiemannianIsometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [BoundarylessManifold I M]
  {F G N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] {p : M → N}

variable [IsManifold J 1 N] in
/-- A Riemannian covering preserves the maximal time interval of a metric-dual trajectory.
The scalar `c` gives both signs of the flow and the stationary flow at `c = 0`. -/
theorem maximalIntegralCurveInterval_smul_metricDual_mpullback
    (hp : IsLocalRiemannianIsometry I J p) (hcov : IsCoveringMap p)
    (α : RoughForm J N ℝ 1) (c : ℝ) (x : M) :
    maximalIntegralCurveInterval (c • (mpullback I J p α).metricDual) x =
      maximalIntegralCurveInterval (c • α.metricDual) (p x) := by
  let : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  exact hcov.maximalIntegralCurveInterval_eq_of_isLocalDiffeomorph
    (hp.isLocalDiffeomorph (n := 1) le_rfl (by simp)) (by simp)
    (fun y ↦ by simp only [Pi.smul_apply, map_smul, hp.mfderiv_metricDual_mpullback]) x

variable [T2Space N] [BoundarylessManifold J N] [IsManifold J 2 N]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]

/-- The flow of the scaled metric dual upstairs projects to the corresponding base flow
at every time for which the base flow exists. -/
theorem apply_flowOf_smul_metricDual_mpullback
    (hp : IsLocalRiemannianIsometry I J p) (hcov : IsCoveringMap p)
    {α : RoughForm J N ℝ 1} (hα : IsSmoothForm J 1 α) (c : ℝ) {t : ℝ} {x : M}
    (ht : t ∈ maximalIntegralCurveInterval (c • α.metricDual) (p x)) :
    p (flowOf (c • (mpullback I J p α).metricDual) t x) =
      flowOf (c • α.metricDual) t (p x) := by
  have : IsManifold J ((1 : ℕ∞ω) + 1) N := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold J 2 N)
  have hfield := (hα.smul c).contMDiff_metricDual
  have ht' : t ∈ maximalIntegralCurveInterval (c • (mpullback I J p α).metricDual) x := by
    rwa [hp.maximalIntegralCurveInterval_smul_metricDual_mpullback hcov]
  exact (hp.contMDiff.mdifferentiable (by simp)).apply_flowOf
    (by simpa only [RoughForm.metricDual_smul] using hfield)
    (fun y ↦ by simp only [Pi.smul_apply, map_smul, hp.mfderiv_metricDual_mpullback])
    (mem_flowDomain.mpr ht')

end TauCeti.IsLocalRiemannianIsometry
