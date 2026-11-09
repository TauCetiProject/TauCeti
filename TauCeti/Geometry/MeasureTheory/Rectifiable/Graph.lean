/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.TangentCone.Graph
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Approximate tangency of differentiable normal graphs

At every differentiability point of a normal graph, the classical tangent plane also satisfies
the measure-theoretic cone condition: the normalized Hausdorff measure of the graph outside
any cone about that plane, divided by the volume of a parameter ball, tends to zero.

In fact the part outside the cone is empty in a sufficiently small ball. Consequently this
comparison does not need local finiteness of surface measure or measurability of the parameter
set. The plane is explicitly the range of `A.normalGraphL`, where `A` is the derivative of the
graphing function. `HasFDerivAt.tangentConeAt_normalGraphEmbedding_image` identifies it with
the classical tangent cone over a neighborhood of the parameter. This is a comparison of cone
conditions, not a density-one theorem or a uniqueness theorem for approximate tangent planes.
The cone condition also holds for differentiability within an arbitrary parameter set.

All surface measures here use the normalized convention `μHE[k]`.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (approximate tangent planes).
-/

public section

open Filter Metric MeasureTheory Set
open scoped ENNReal Topology

namespace HasFDerivWithinAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {φ : E → ℝ} {A : E →L[ℝ] ℝ} {x : E}

/-- Differentiability within a parameter set makes the normal graph satisfy the cone condition
about the range of the derivative's linear graph. No surface-measure finiteness, measurability,
or membership of the base point in the parameter set is needed. This includes dimension zero. -/
theorem tendsto_euclideanHausdorffMeasure_normalGraphEmbedding_outside_cone_div
    {s : Set E} (hφ : HasFDerivWithinAt φ A s x) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun r =>
      μHE[Module.finrank ℝ E]
        {z ∈ TauCeti.normalGraphEmbedding φ '' s ∩
            closedBall (TauCeti.normalGraphEmbedding φ x) r |
          ε * dist z (TauCeti.normalGraphEmbedding φ x) <
            infDist (z - TauCeti.normalGraphEmbedding φ x)
              (LinearMap.range A.normalGraphL.toLinearMap : Set (WithLp 2 (ℝ × E)))} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨δ, hδ, hcone⟩ := hφ.exists_pos_forall_infDist_range_normalGraphL_le hε
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r hr
  have hempty :
      {z ∈ TauCeti.normalGraphEmbedding φ '' s ∩
          closedBall (TauCeti.normalGraphEmbedding φ x) r |
        ε * dist z (TauCeti.normalGraphEmbedding φ x) <
          infDist (z - TauCeti.normalGraphEmbedding φ x)
            (LinearMap.range A.normalGraphL.toLinearMap : Set (WithLp 2 (ℝ × E)))} = ∅ := by
    apply eq_empty_of_forall_notMem
    intro z hz
    exact (not_lt_of_ge (hcone z hz.1.1
      ((mem_closedBall.mp hz.1.2).trans_lt hr))) hz.2
  rw [hempty, measure_empty, ENNReal.zero_div]

end HasFDerivWithinAt

/-- The classical tangent plane of a differentiable normal graph satisfies the approximate
tangent-plane cone condition. The parameter set is arbitrary, with no surface-measure
finiteness or measurability hypothesis. This includes dimension zero. -/
theorem HasFDerivAt.tendsto_euclideanHausdorffMeasure_normalGraphEmbedding_outside_cone_div
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {φ : E → ℝ} {A : E →L[ℝ] ℝ} {x : E}
    (hφ : HasFDerivAt φ A x) (s : Set E) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun r =>
      μHE[Module.finrank ℝ E]
        {z ∈ TauCeti.normalGraphEmbedding φ '' s ∩
            closedBall (TauCeti.normalGraphEmbedding φ x) r |
          ε * dist z (TauCeti.normalGraphEmbedding φ x) <
            infDist (z - TauCeti.normalGraphEmbedding φ x)
              (LinearMap.range A.normalGraphL.toLinearMap : Set (WithLp 2 (ℝ × E)))} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r))
      (𝓝[>] 0) (𝓝 0) :=
  hφ.hasFDerivWithinAt.tendsto_euclideanHausdorffMeasure_normalGraphEmbedding_outside_cone_div hε
