/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Topology
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Jet

/-!
# Scalar curvature in the chart C² and C∞ topologies on metrics

Equip the smooth Riemannian metrics on a finite-dimensional manifold without boundary with the
chart C² topology `Bundle.ContMDiffRiemannianMetric.chartC2Topology`, in which convergence is
uniform convergence on compact chart sets of the coordinate derivatives of orders zero, one and
two. Scalar curvature is a second-order differential expression in the metric: in a chart it is a
continuous function of the Gram matrix and its first two derivatives wherever the Gram matrix is
invertible (`ContinuousAt.scalarCurvatureOfJet`). Hence the scalar curvature `Scal(g)(x)` depends
jointly continuously on the metric `g` in the chart C² topology and on the point `x`.

On a compact manifold this gives the C² openness of positive scalar curvature: the metrics of
positive scalar curvature form an open set. Moreover, a compact set of metrics of positive scalar
curvature, such as the image of a continuous path of such metrics, has a common positive lower
bound for its scalar curvature.

The chart C∞ topology `Bundle.ContMDiffRiemannianMetric.chartCInftyTopology` is finer than the
chart C² topology, so the same three statements hold for it.

## Main results

* `Bundle.ContMDiffRiemannianMetric.continuous_scalarCurvature_chartC2`: `(g, x) ↦ Scal(g)(x)` is
  continuous for the chart C² topology on metrics.
* `Bundle.ContMDiffRiemannianMetric.isOpen_setOf_hasPositiveScalarCurvature_chartC2`: on a compact
  manifold, positive scalar curvature is an open condition in the chart C² topology.
* `IsCompact.exists_pos_forall_le_scalarCurvature_chartC2`: on a compact manifold, the metrics in a
  C²-compact set of metrics of positive scalar curvature have scalar curvature bounded below by a
  common positive constant.
* `Bundle.ContMDiffRiemannianMetric.continuous_scalarCurvature_chartCInfty`,
  `Bundle.ContMDiffRiemannianMetric.isOpen_setOf_hasPositiveScalarCurvature_chartCInfty` and
  `IsCompact.exists_pos_forall_le_scalarCurvature_chartCInfty`: the same statements for the chart
  C∞ topology.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive
  scalar curvature*, Ann. of Math. 111 (1980), 423–434.
-/

open Bundle Filter Set TauCeti.Manifold
open scoped ContDiff Manifold Topology

public section

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace Bundle.ContMDiffRiemannianMetric

-- Cache the canonical operator-space instances, as in the definition of the chart C² topology:
-- otherwise instance search for the algebraic and topological structure on the nested operator
-- spaces receiving the derivatives of chart metrics fails.
private local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

section ChartC2

open scoped TauCeti.MetricC2

/-- **Scalar curvature is continuous in the chart C² topology.** The scalar curvature `Scal(g)(x)`
of a smooth Riemannian metric `g` at a point `x` depends jointly continuously on `g`, in the chart
C² topology, and on `x`. -/
theorem continuous_scalarCurvature_chartC2 :
    Continuous (fun q : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) × M ↦
      q.1.scalarCurvature q.2) := by
  let b := Module.finBasis ℝ E
  refine continuous_iff_continuousAt.2 fun ⟨g₀, y₀⟩ ↦ ?_
  have hz₀ := mem_extChartAt_target (I := I) y₀
  -- Each entry of a chart derivative of order at most two, evaluated on basis vectors, varies
  -- continuously.
  have hJ (n : ℕ) (hn : (n : ℕ∞) ≤ 2) (v : Fin n → E) (i j : Fin (Module.finrank ℝ E)) :
      ContinuousAt (fun q : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) × E ↦
        iteratedFDeriv ℝ n (q.1.toNondegenerateMetric.chartMetric y₀) q.2 v (b i) (b j))
        (g₀, extChartAt I y₀ y₀) :=
    (((continuous_eval_const v).continuousAt.comp
      (continuousAt_iteratedFDeriv_chartMetric 2 y₀ hn g₀ hz₀)).clm_apply
        continuousAt_const).clm_apply continuousAt_const
  -- Near `(g₀, extChartAt I y₀ y₀)` the chart point stays in the open chart target, where each
  -- chart metric is smooth.
  have hev : ∀ᶠ q : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) × E in
      𝓝 (g₀, extChartAt I y₀ y₀), q.2 ∈ (extChartAt I y₀).target :=
    continuousAt_snd.preimage_mem_nhds ((isOpen_extChartAt_target y₀).mem_nhds hz₀)
  have hsmooth {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)} {z : E}
      (hz : z ∈ (extChartAt I y₀).target) :
      ContDiffAt ℝ ∞ (g.toNondegenerateMetric.chartMetric y₀) z :=
    (g.toNondegenerateMetric.contDiffOn_chartMetric y₀).contDiffAt
      ((isOpen_extChartAt_target y₀).mem_nhds hz)
  refine continuousAt_scalarCurvature_of_continuousAt_chartMetric b id
    (by simp [ModelWithCorners.Boundaryless.range_eq_univ]) ?_ ?_ ?_
  · -- The Gram matrix is read off from the derivative of order zero.
    refine continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ ?_
    refine (hJ 0 (by norm_num) 0 i j).congr (Eventually.of_forall fun q ↦ ?_)
    simp [LinearMap.toMatrix₂_apply]
  · -- First derivatives of the Gram entries are read off from the derivative of order one.
    refine continuousAt_pi.2 fun k ↦ continuousAt_pi.2 fun i ↦ continuousAt_pi.2 fun j ↦ ?_
    refine (hJ 1 (by norm_num) ![b k] i j).congr ?_
    filter_upwards [hev] with q hq
    simp only [id_eq, iteratedFDeriv_one_apply, Matrix.cons_val_zero]
    rw [TauCeti.fderiv_clm_apply_const_apply₂ ((hsmooth hq).differentiableAt (by simp))]
  · -- Second derivatives of the Gram entries are read off from the derivative of order two.
    refine continuousAt_pi.2 fun m ↦ continuousAt_pi.2 fun k ↦ continuousAt_pi.2 fun i ↦
      continuousAt_pi.2 fun j ↦ ?_
    refine (hJ 2 (by norm_num) ![b m, b k] i j).congr ?_
    filter_upwards [hev] with q hq
    set f := q.1.toNondegenerateMetric.chartMetric y₀
    have hdf : DifferentiableAt ℝ (fderiv ℝ f) q.2 :=
      ((hsmooth hq).fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
    -- Near `q.2` the first derivative of a Gram entry is the corresponding entry of `fderiv f`.
    have heq : (fun z ↦ fderiv ℝ (fun z' ↦ f z' (b i) (b j)) z (b k)) =ᶠ[𝓝 q.2]
        fun z ↦ fderiv ℝ f z (b k) (b i) (b j) := by
      filter_upwards [(isOpen_extChartAt_target y₀).mem_nhds hq] with z hz
      exact TauCeti.fderiv_clm_apply_const_apply₂ ((hsmooth hz).differentiableAt (by simp)) _ _ _
    simp only [id_eq, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [heq.fderiv_eq,
      TauCeti.fderiv_clm_apply_const_apply₂ (hdf.clm_apply (differentiableAt_const _)),
      TauCeti.fderiv_clm_apply_const_apply hdf]

/-- **Positive scalar curvature is C²-open.** On a compact manifold without boundary, the smooth
Riemannian metrics of positive scalar curvature form an open set in the chart C² topology. -/
theorem isOpen_setOf_hasPositiveScalarCurvature_chartC2 [CompactSpace M] :
    IsOpen {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) |
      g.HasPositiveScalarCurvature} := by
  refine isOpen_iff_mem_nhds.2 fun g₀ hg₀ ↦ ?_
  filter_upwards [isCompact_univ.eventually_forall_of_forall_eventually
    (P := fun g x ↦ 0 < g.scalarCurvature x) fun x _ ↦
    continuousAt_const.eventually_lt continuous_scalarCurvature_chartC2.continuousAt
      ((hasPositiveScalarCurvature_iff _).1 hg₀ x)] with g hg
  exact (hasPositiveScalarCurvature_iff _).2 fun x ↦ hg x (mem_univ x)

end ChartC2

section ChartCInfty

open scoped TauCeti.MetricCInfty

/-- **Scalar curvature is continuous in the chart C∞ topology.** The scalar curvature `Scal(g)(x)`
depends jointly continuously on the metric `g`, in the chart C∞ topology, and on `x`. -/
theorem continuous_scalarCurvature_chartCInfty :
    Continuous (fun q : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) × M ↦
      q.1.scalarCurvature q.2) :=
  -- Precompose the chart C² statement with the identity, continuous from the finer chart C∞
  -- topology; the two topologies on the metric factor are passed explicitly.
  @Continuous.comp _ _ _ (@instTopologicalSpaceProd _ _ chartCInftyTopology _)
    (@instTopologicalSpaceProd _ _ chartC2Topology _) _ _ _
    continuous_scalarCurvature_chartC2
    (@Continuous.prodMap _ _ _ _ chartC2Topology _ chartCInftyTopology _ _ _
      (continuous_id_of_le chartCInftyTopology_le_chartC2Topology) continuous_id)

/-- **Positive scalar curvature is C∞-open.** On a compact manifold without boundary, the smooth
Riemannian metrics of positive scalar curvature form an open set in the chart C∞ topology. -/
theorem isOpen_setOf_hasPositiveScalarCurvature_chartCInfty [CompactSpace M] :
    IsOpen {g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) |
      g.HasPositiveScalarCurvature} :=
  isOpen_setOf_hasPositiveScalarCurvature_chartC2.mono chartCInftyTopology_le_chartC2Topology

end ChartCInfty

end Bundle.ContMDiffRiemannianMetric

open scoped TauCeti.MetricC2 in
/-- **A uniform scalar gap on C²-compact sets of metrics.** On a compact manifold without boundary,
let `K` be a set of smooth Riemannian metrics of positive scalar curvature that is compact in the
chart C² topology, such as the image of a continuous path of such metrics. Then the scalar
curvatures of the metrics in `K` are bounded below by a common positive constant. -/
theorem IsCompact.exists_pos_forall_le_scalarCurvature_chartC2 [CompactSpace M]
    {K : Set (ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))} (hK : IsCompact K)
    (hpos : ∀ g ∈ K, g.HasPositiveScalarCurvature) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ K, ∀ x, ε ≤ g.scalarCurvature x := by
  obtain ⟨ε, hε, hle⟩ := (hK.prod isCompact_univ).exists_forall_le'
    ContMDiffRiemannianMetric.continuous_scalarCurvature_chartC2.continuousOn
    fun q hq ↦ (ContMDiffRiemannianMetric.hasPositiveScalarCurvature_iff _).1 (hpos q.1 hq.1) q.2
  exact ⟨ε, hε, fun g hg x ↦ hle (g, x) ⟨hg, mem_univ x⟩⟩

open scoped TauCeti.MetricCInfty in
/-- **A uniform scalar gap on C∞-compact sets of metrics.** On a compact manifold without
boundary, the scalar curvatures of the metrics in a set of metrics of positive scalar curvature
that is compact in the chart C∞ topology are bounded below by a common positive constant. -/
theorem IsCompact.exists_pos_forall_le_scalarCurvature_chartCInfty [CompactSpace M]
    {K : Set (ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))} (hK : IsCompact K)
    (hpos : ∀ g ∈ K, g.HasPositiveScalarCurvature) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ K, ∀ x, ε ≤ g.scalarCurvature x :=
  -- `K` is also compact in the coarser chart C² topology.
  (hK.chartCk_of_le (k := 2) le_top).exists_pos_forall_le_scalarCurvature_chartC2 hpos
