/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Restriction.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Topology
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.Riemannian.Pullback.Topology

/-!
# Restriction of continuous families of Riemannian metrics

Restriction to an open submanifold is continuous in every chart Cᵏ topology, including C² and
C∞. The coordinate metric of a restriction is the ambient coordinate metric on the inherited
chart target, so all its coordinate derivatives agree there as well. No compactness of the
manifold or parameter space is needed.

The coordinate computation uses `chartMetric_pullback`: for the open inclusion the transition
map between inherited and ambient charts is the identity. The topology is the compact-open
derivative topology of Hirsch, *Differential Topology*, Chapter 2, §1.
-/

public section

open Bundle Set Filter TopologicalSpace
open scoped ContDiff Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- On an inherited chart target, the coordinate metric of the restriction is the ambient
coordinate metric. -/
theorem chartMetric_restrictOpenTangentSpace
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (U : Opens M) (x : U) {z : E} (hz : z ∈ (extChartAt I x).target) :
    (g.restrictOpenTangentSpace U).toNondegenerateMetric.chartMetric x z =
      g.toNondegenerateMetric.chartMetric (x : M) z := by
  have hτ : EqOn (extChartAt I (x : M) ∘ (Subtype.val : U → M) ∘
      (extChartAt I x).symm) id (extChartAt I x).target := by
    intro y hy
    simp only [Function.comp_apply, U.coe_extChartAt_symm_apply x hy, id_eq]
    exact (extChartAt I (x : M)).right_inv (U.extChartAt_target_subset x hy)
  have hzRange := extChartAt_target_subset_range x hz
  have hd := (hτ.eventuallyEq_of_mem
    (extChartAt_target_mem_nhdsWithin_of_mem hz)).fderivWithin_eq_of_mem (𝕜 := ℝ) hzRange
  have hsource : ((extChartAt I x).symm z : M) ∈ (extChartAt I (x : M)).source := by
    rw [U.coe_extChartAt_symm_apply x hz]
    exact (extChartAt I (x : M)).map_target (U.extChartAt_target_subset x hz)
  rw [restrictOpenTangentSpace_eq_pullback,
    chartMetric_pullback g contMDiff_subtype_val
      (TauCeti.Manifold.mfderiv_subtype_val_injective (I := I)) hz hsource,
    hd, fderivWithin_id (I.uniqueDiffOn _ hzRange)]
  have hτz := hτ hz
  simp only [Function.comp_apply, id_eq] at hτz
  rw [hτz]
  ext v w
  simp only [ContinuousLinearMap.precomp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]

variable [I.Boundaryless]

-- Cache the canonical operator-space instances, as in the definition of chart Cᵏ topologies.
private local instance : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
private local instance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

/-- All coordinate derivatives of a restricted metric agree with the ambient derivatives on
the inherited chart target. -/
theorem iteratedFDeriv_chartMetric_restrictOpenTangentSpace
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (U : Opens M) (x : U) (m : ℕ) {z : E} (hz : z ∈ (extChartAt I x).target) :
    -- Use the canonical operator norms in the public signature, not the private cached instances.
    letI : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
    letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedAddCommGroup
    letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
    iteratedFDeriv ℝ m ((g.restrictOpenTangentSpace U).toNondegenerateMetric.chartMetric x) z =
      iteratedFDeriv ℝ m (g.toNondegenerateMetric.chartMetric (x : M)) z := by
  have h : (g.restrictOpenTangentSpace U).toNondegenerateMetric.chartMetric x =ᶠ[𝓝 z]
      g.toNondegenerateMetric.chartMetric (x : M) :=
    Filter.eventuallyEq_of_mem ((isOpen_extChartAt_target x).mem_nhds hz)
      (fun y hy ↦ g.chartMetric_restrictOpenTangentSpace U x hy)
  exact (h.iteratedFDeriv ℝ m).self_of_nhds

/-- Restriction to an open submanifold is continuous for every chart Cᵏ topology. In particular,
a C²- or C∞-continuous family restricts to a family continuous in the same topology. -/
theorem continuous_restrictOpenTangentSpace (k : ℕ∞) (U : Opens M) :
    letI := chartCkTopology (I := I) (M := M) k
    letI := chartCkTopology (I := I) (M := U) k
    Continuous (fun g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x) ↦
      g.restrictOpenTangentSpace U) := by
  let _ := chartCkTopology (I := I) (M := M) k
  let _ := chartCkTopology (I := I) (M := U) k
  simpa only [restrictOpenTangentSpace_eq_pullback] using
    (continuous_pullback_chartCk k (f := (Subtype.val : U → M)) contMDiff_subtype_val
      (TauCeti.Manifold.mfderiv_subtype_val_injective (I := I)))

end Bundle.ContMDiffRiemannianMetric
