/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.TangentCone
import TauCeti.Geometry.Euclidean.Volume.Measure

/-!
# Approximate tangent planes of rectifiable sets

A countably `k`-rectifiable set with locally finite normalized Euclidean Hausdorff measure
has, almost everywhere, a `k`-plane outside whose every cone the set has density zero.
Together with the density-one theorem in `Rectifiable.Density`, this proves existence of
approximate tangent planes. Uniqueness and measurability of the plane field are not asserted.

The distinction from pointwise tangent cones is important: a rectifiable set can have other
patches accumulating at a point, so the whole set need not lie in a narrow cone. We use the
countable Borel cover with patchwise cone containment, and the zero-density theorem for the
part of the set outside each patch. Local finiteness is used only to localize this argument
to bounded pieces. No Borel representative of the original set is required.

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

/-- The finite-measure version of approximate tangent-plane existence. -/
private theorem CountablyRectifiable.ae_exists_submodule_tendsto_measure_outside_cone_div_of_ne_top
    (hE : CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k])
    (hfin : μHE[k] E ≠ ∞) :
    ∀ᵐ x ∂μHE[k], x ∈ E → ∃ P : Submodule ℝ V, Module.finrank ℝ P = k ∧
      ∀ ε > (0 : ℝ), Tendsto (fun r =>
        μHE[k] {z ∈ E ∩ closedBall x r | ε * dist z x < infDist (z - x) (P : Set V)} /
          volume (closedBall (0 : EuclideanSpace ℝ (Fin k)) r)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨T, hTm, hcover, hcone⟩ := hE.exists_measurable_cover_forall_infDist_le
  have hzero (n : ℕ) := TauCeti.ae_tendsto_euclideanHausdorffMeasure_inter_closedBall_div k
    (hEm.diff (hTm n).nullMeasurableSet)
    (ne_top_of_le_ne_top hfin (measure_mono (sdiff_subset : E \ T n ⊆ E)))
  filter_upwards [ae_le_set.mpr hcover, ae_all_iff.mpr hzero] with x hcov hx hxE
  obtain ⟨n, hxn⟩ := mem_iUnion.mp (hcov hxE)
  obtain ⟨P, hdim, hP⟩ := hcone n x hxn
  refine ⟨P, hdim, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hlocal⟩ := hP ε hε
  have hxzero := hx n (fun h => h.2 hxn)
  -- In a sufficiently small ball, every point outside the cone is outside this patch.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hxzero
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ)] with r hr
  gcongr
  intro z hz
  refine ⟨⟨hz.1.1, ?_⟩, hz.1.2⟩
  intro hzT
  exact (not_lt_of_ge (hlocal z hzT ((mem_closedBall.mp hz.1.2).trans_lt hr))) hz.2

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
  -- Bounded pieces have finite measure and agree locally with the original set.
  have hfin (n : ℕ) : μHE[k] (E ∩ ball 0 n) ≠ ∞ := by
    rw [inter_comm, ← Measure.restrict_apply measurableSet_ball]
    exact measure_ball_lt_top.ne
  filter_upwards [ae_all_iff.mpr fun n =>
    (hE.mono inter_subset_left).ae_exists_submodule_tendsto_measure_outside_cone_div_of_ne_top
      (hEm.inter measurableSet_ball.nullMeasurableSet) (hfin n)] with x hx hxE
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  have hxn : x ∈ ball (0 : V) n := mem_ball_zero_iff.mpr hn
  obtain ⟨P, hdim, hP⟩ := hx n ⟨hxE, hxn⟩
  refine ⟨P, hdim, fun ε hε => (hP ε hε).congr' ?_⟩
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds
    (eventually_closedBall_subset (isOpen_ball.mem_nhds hxn))] with r hr
  have hsets : (E ∩ ball 0 n) ∩ closedBall x r = E ∩ closedBall x r := by
    rw [inter_assoc, inter_eq_right.mpr hr]
  rw [hsets]

end TauCeti
