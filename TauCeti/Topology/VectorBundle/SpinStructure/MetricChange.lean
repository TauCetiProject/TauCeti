/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Orientation
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Lift.MetricChange
public import TauCeti.Topology.VectorBundle.SpinStructure.Orientation

/-!
# Spin structures under a change of metric

Let `E → X` be a continuous Riemannian vector bundle with finite-dimensional fibres and let `g` be a
second continuous Riemannian metric on `E`. A Spin structure `s` for the given metric induces the
Spin structure `s.metricChange g` for `g` on the copy `TauCeti.WithFiberMetric g` of `E`
(`TauCeti.OrthonormalFrameLift.metricChange`): its frames are those of `s` composed with the
inverse square root `B ^ (-1/2)` of the positive operator `B` with `g u v = ⟪B u, v⟫`. Every Spin
structure for `g` arises this way from exactly one Spin structure for the given metric, and
equivalence classes correspond (`TauCeti.OrthonormalFrameLift.metricChange_injective`,
`TauCeti.OrthonormalFrameLift.metricChange_surjective`,
`TauCeti.OrthonormalFrameLift.nonempty_equiv_metricChange_iff`).

Since `B ^ (-1/2)` is positive it has positive determinant, so the metric change does not move the
orientation chosen by the Spin structure: `s.metricChange g` induces on each fibre the orientation
that `s` induces, read on the copy of the fibre carrying `g`
(`TauCeti.SpinStructure.fiberOrientation_metricChange`,
`TauCeti.SpinStructure.orientation_metricChange_apply`). Thus the metric change matches the Spin
structures of a fixed orientation for the two metrics.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter II,
  §1.
-/

public section

open Bundle

universe w

namespace TauCeti.SpinStructure

variable {X : Type*} [TopologicalSpace X] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : X → Type w} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)] [∀ x, FiniteDimensional ℝ (E x)] [FiberBundle F E]
  [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E] {n : ℕ}
  (g : ContinuousRiemannianMetric F E)

/-- **A change of metric preserves the orientation of a Spin structure**: the metric change of `s`
to `g` induces on each fibre the orientation induced by `s`, read on the copy of the fibre carrying
`g`. The transport `B ^ (-1/2)` has positive determinant. It takes precedence over the general
transport rule `TauCeti.SpinStructure.fiberOrientation_map` in `simp`. -/
@[simp high]
theorem fiberOrientation_metricChange (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (x : X) :
    fiberOrientation (s.metricChange g) o x =
      Orientation.map (Fin n) (WithFiberMetric.toWithFiberMetric g x).toLinearEquiv
        (s.fiberOrientation o x) := by
  rw [OrthonormalFrameLift.metricChange, fiberOrientation_map,
    ContinuousRiemannianMetric.toLinearEquiv_metricChangeIsometry, Orientation.map_trans,
    Orientation.map_metricChangeEquiv _ _ _ (by rw [Fintype.card_fin, s.finrank_fiber x])]

/-- The bundle orientation induced by the metric change of a Spin structure is, on each fibre,
the orientation induced by the Spin structure itself. -/
theorem orientation_metricChange_apply (s : SpinStructure F E n)
    (o : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n)) (x : X) :
    orientation (s.metricChange g) o x =
      Orientation.map (Fin n) (WithFiberMetric.toWithFiberMetric g x).toLinearEquiv
        (s.orientation o x) := by
  rw [orientation_apply, orientation_apply, fiberOrientation_metricChange]

end TauCeti.SpinStructure
