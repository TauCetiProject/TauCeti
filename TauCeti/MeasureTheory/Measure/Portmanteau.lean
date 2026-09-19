/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Thickenings with null boundaries for countably many sets

The portmanteau theorem makes the masses of a set converge along weak convergence as soon as the
limit law does not charge the boundary of the set. Mathlib's `exists_null_frontier_thickening`
supplies, for one set, thickening radii in any interval whose thickenings have null boundary. This
file chooses a single radius that works simultaneously for countably many sets, which is what is
needed to cut a separable space into finitely many continuity sets of small diameter: the sets are
the points of a dense sequence, and the thickenings are the balls around them.

## Main statements

* `TauCeti.exists_forall_null_frontier_thickening` — for countably many sets, some radius in any
  nonempty open interval gives thickenings whose boundaries are all null.
-/

public section

open MeasureTheory Set

namespace TauCeti

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace Ω] [OpensMeasurableSpace Ω]

/-- For countably many sets `s k` and an s-finite measure `μ`, some radius in any nonempty open
interval gives thickenings whose boundaries are all `μ`-null: for each set only countably many
radii fail, and a nonempty open interval of reals is uncountable. -/
theorem exists_forall_null_frontier_thickening (μ : Measure Ω) [SFinite μ] {ι : Type*}
    [Countable ι] (s : ι → Set Ω) {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Ioo a b, ∀ k, μ (frontier (Metric.thickening r (s k))) = 0 := by
  have hcount (k : ι) : {r : ℝ | 0 < μ (frontier (Metric.thickening r (s k)))}.Countable :=
    Measure.countable_meas_pos_of_disjoint_iUnion (fun r ↦ isClosed_frontier.measurableSet)
      (Metric.frontier_thickening_disjoint (s k))
  obtain ⟨r, hr, hr'⟩ :
      (Ioo a b \ ⋃ k, {r : ℝ | 0 < μ (frontier (Metric.thickening r (s k)))}).Nonempty := by
    refine nonempty_of_not_subset fun hsub ↦ ?_
    exact (Cardinal.Real.Ioo_countable_iff.1 ((countable_iUnion hcount).mono hsub)).not_gt hab
  refine ⟨r, hr, fun k ↦ ?_⟩
  by_contra hk
  exact hr' (mem_iUnion.2 ⟨k, pos_iff_ne_zero.2 hk⟩)

end TauCeti
