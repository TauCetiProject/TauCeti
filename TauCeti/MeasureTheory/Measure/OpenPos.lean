/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Consequences of positivity on open sets

Mathlib's `Metric.measure_ball_pos` says that a measure positive on nonempty open sets gives
positive measure to every ball of positive radius. In a proper space, where balls are bounded and
so have finite measure under a measure finite on compact sets, the same holds for the real-valued
measure `μ.real`, and likewise for closed balls. For a locally finite measure, closed balls of
small positive radius around a point have positive finite measure, so proportions of sets in
shrinking balls are well behaved. Since a property holding almost everywhere holds on a dense
set, an almost everywhere inequality between continuous functions holds everywhere.

An almost-everywhere inclusion of an open set in another set implies inclusion in its closure.
In particular, two almost-everywhere equal open sets have the same closure. Taking interiors
then shows that regular open sets are determined by their almost-everywhere classes.

On a discrete space, such a measure charges every point, so the only null set is empty and
almost everywhere means everywhere.

## Main results

* `IsOpen.subset_closure_of_ae_le`: an open set lies in the closure of any set containing it a.e.
* `IsOpen.closure_eq_of_ae_eq`: a.e. equal open sets have equal closures.
* `TauCeti.eq_of_ae_eq_of_interior_closure_eq`: a.e. equal regular open sets are equal.
* `Metric.measureReal_ball_pos`: a ball of positive radius has positive real measure.
* `Metric.measureReal_closedBall_pos`: a closed ball of positive radius has positive real
  measure.
* `Metric.eventually_measure_closedBall_ne_zero_ne_top`: closed balls of small positive radius
  have positive finite measure.
* `Continuous.ae_le_iff_le`: continuous functions satisfy `f ≤ᵐ[μ] g` if and only if `f ≤ g`.
* `MeasureTheory.ae_eq_top_of_discreteTopology`: on a discrete space, for a measure positive on
  open sets, almost everywhere means everywhere.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace IsOpen

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] {μ : Measure X}
  [μ.IsOpenPosMeasure] {s t : Set X}

/-- An open set contained almost everywhere in another set is contained in its closure.
No measurability assumption on either set is needed. -/
theorem subset_closure_of_ae_le (hs : IsOpen s) (hst : s ≤ᵐ[μ] t) : s ⊆ closure t :=
  ((Measure.dense_of_ae hst).open_subset_closure_inter hs).trans <|
    closure_mono fun _ hx => hx.2 hx.1

/-- Almost-everywhere equal open sets have the same closure for a measure positive on nonempty
open sets. The open sets themselves need not be equal. -/
theorem closure_eq_of_ae_eq (hs : IsOpen s) (ht : IsOpen t) (hst : s =ᵐ[μ] t) :
    closure s = closure t :=
  Subset.antisymm (closure_minimal (hs.subset_closure_of_ae_le hst.le) isClosed_closure)
    (closure_minimal (ht.subset_closure_of_ae_le hst.symm.le) isClosed_closure)

end IsOpen

namespace TauCeti

/-- Regular open sets are determined by their almost-everywhere classes for a measure positive
on nonempty open sets. Regular openness is expressed by `interior (closure s) = s`; ordinary
openness alone does not suffice. -/
theorem eq_of_ae_eq_of_interior_closure_eq {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} [μ.IsOpenPosMeasure] {s t : Set X}
    (hs : interior (closure s) = s) (ht : interior (closure t) = t) (hst : s =ᵐ[μ] t) :
    s = t := by
  have hsopen : IsOpen s := hs ▸ isOpen_interior
  rw [← hs, ← ht, hsopen.closure_eq_of_ae_eq (ht ▸ isOpen_interior) hst]

/-- In a proper space, a measure that is positive on nonempty open sets and finite on compact sets
gives every ball of positive radius positive real measure. -/
theorem _root_.Metric.measureReal_ball_pos {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ.real (Metric.ball x r) :=
  ENNReal.toReal_pos (Metric.measure_ball_pos μ x hr).ne' measure_ball_lt_top.ne

/-- In a proper space, a measure that is positive on nonempty open sets and finite on compact sets
gives every closed ball of positive radius positive real measure. -/
theorem _root_.Metric.measureReal_closedBall_pos {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    (x : X) {r : ℝ} (hr : 0 < r) : 0 < μ.real (Metric.closedBall x r) :=
  ENNReal.toReal_pos (Metric.measure_closedBall_pos μ x hr).ne' measure_closedBall_lt_top.ne

/-- For a locally finite measure that is positive on nonempty open sets, closed balls of small
positive radius around a point have positive finite measure. -/
theorem _root_.Metric.eventually_measure_closedBall_ne_zero_ne_top {X : Type*}
    [PseudoMetricSpace X] [MeasurableSpace X] (μ : Measure X) [IsLocallyFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (x : X) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), μ (Metric.closedBall x r) ≠ 0 ∧ μ (Metric.closedBall x r) ≠ ∞ := by
  obtain ⟨U, hU, hUμ⟩ := μ.finiteAt_nhds x
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hU
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  exact ⟨(Metric.measure_closedBall_pos μ x hr.1).ne',
    ((measure_mono ((Metric.closedBall_subset_ball hr.2).trans hεU)).trans_lt hUμ).ne⟩

/-- Under a measure positive on nonempty open sets, an almost everywhere inequality between
continuous functions into an order-closed space holds everywhere. -/
theorem _root_.Continuous.ae_le_iff_le {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure] [TopologicalSpace Y] [Preorder Y]
    [OrderClosedTopology Y] {f g : X → Y} (hf : Continuous f) (hg : Continuous g) :
    f ≤ᵐ[μ] g ↔ f ≤ g :=
  -- The closed set where `f ≤ g` is dense, hence everything.
  ⟨fun h x => (μ.dense_of_ae h).induction (fun _ => id) (isClosed_le hf hg) x,
    Eventually.of_forall⟩

/-- On a discrete space, a measure positive on nonempty open sets charges every point, so
almost everywhere means everywhere. -/
theorem _root_.MeasureTheory.ae_eq_top_of_discreteTopology {α : Type*} [TopologicalSpace α]
    [DiscreteTopology α] [MeasurableSpace α] (μ : Measure α) [μ.IsOpenPosMeasure] :
    ae μ = ⊤ :=
  ae_eq_top.2 fun x => (isOpen_discrete {x}).measure_ne_zero μ (Set.singleton_nonempty x)

end TauCeti

end
