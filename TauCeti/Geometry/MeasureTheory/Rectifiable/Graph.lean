/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.TangentCone.Graph
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import TauCeti.Analysis.Calculus.FDeriv.ImageCone

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

All surface measures here use the normalized convention `μHE[k]`.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (approximate tangent planes).
-/

public section

open Filter Metric MeasureTheory Set
open scoped ENNReal Topology

namespace HasFDerivAt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {φ : E → ℝ} {A : E →L[ℝ] ℝ} {x : E}

/-- The classical tangent plane of a differentiable normal graph satisfies the approximate
tangent-plane cone condition at every differentiability point. The parameter set is arbitrary;
no surface-measure finiteness or measurability hypothesis is needed. This includes dimension
zero. -/
theorem tendsto_euclideanHausdorffMeasure_normalGraphEmbedding_outside_cone_div
    (hφ : HasFDerivAt φ A x) (s : Set E) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun r =>
      μHE[Module.finrank ℝ E]
        {z ∈ TauCeti.normalGraphEmbedding φ '' s ∩
            closedBall (TauCeti.normalGraphEmbedding φ x) r |
          ε * dist z (TauCeti.normalGraphEmbedding φ x) <
            infDist (z - TauCeti.normalGraphEmbedding φ x)
              (LinearMap.range A.normalGraphL.toLinearMap : Set (WithLp 2 (ℝ × E)))} /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r))
      (𝓝[>] 0) (𝓝 0) := by
  have hi : AntilipschitzWith 1
      (univ.domRestrict (TauCeti.normalGraphEmbedding φ)) := fun y z =>
    TauCeti.antilipschitzWith_normalGraphEmbedding φ y z
  obtain ⟨δ, hδ, hcone⟩ :=
    hφ.normalGraphEmbedding.hasFDerivWithinAt.exists_pos_forall_infDist_range_le
      (mem_univ x) hi hε
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
    exact (not_lt_of_ge (hcone z (image_mono (subset_univ s) hz.1.1)
      ((mem_closedBall.mp hz.1.2).trans_lt hr))) hz.2
  rw [hempty, measure_empty, ENNReal.zero_div]

end HasFDerivAt
