/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.MeasurableTangent
import TauCeti.Geometry.Euclidean.Volume.Measure

/-!
# Approximate tangent planes of rectifiable sets

A countably `k`-rectifiable set with locally finite normalized Euclidean Hausdorff measure
has, almost everywhere, a `k`-plane outside whose every cone the set has density zero.
Together with the density-one theorem in `Rectifiable.Density`, this proves existence of
approximate tangent planes. Uniqueness and measurability of the plane field are not asserted.

The distinction from pointwise tangent cones is important: a rectifiable set can have other
patches accumulating at a point, so the whole set need not lie in a narrow cone. We use the
measurable approximate tangent projection field from `Rectifiable.MeasurableTangent`,
forgetting the projection data. Its construction uses a countable Borel cover with patchwise
cone containment and measure differentiation for the part outside each patch.
No Borel representative of the original set is required.

All densities use `μHE[k]` and the volume of a ball in `EuclideanSpace ℝ (Fin k)`; there is
no change to raw Hausdorff normalization. The result includes `k = 0`.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (approximate tangents).
* P. Mattila, *Geometry of Sets and Measures in Euclidean Spaces*, Theorem 15.19.
-/

public section

open Filter Metric MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {k : ℕ} {E : Set V}

/-- **Existence of approximate tangent planes.** At almost every point of a null-measurable,
countably `k`-rectifiable set with locally finite `μHE[k]` measure, there is a `k`-plane such
that the part of the set outside every cone about that plane has `k`-dimensional density
zero. The density-one theorem supplies the nonzero density required for an approximate
tangent plane. This theorem does not assert uniqueness of the plane. -/
theorem CountablyRectifiable.ae_exists_submodule_tendsto_measure_outside_cone_div
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    [IsLocallyFiniteMeasure (μHE[k].restrict E)] :
    ∀ᵐ x ∂μHE[k], x ∈ E → ∃ P : Submodule ℝ V, Module.finrank ℝ P = k ∧
      ∀ ε > (0 : ℝ), Tendsto (fun r =>
        μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Q, _, hQ⟩ := hE.exists_measurable_approximate_tangent_projection hEm
  filter_upwards [hQ] with x hx hxE
  obtain ⟨P, hdim, _, hP⟩ := hx hxE
  exact ⟨P, hdim, hP⟩

end TauCeti
