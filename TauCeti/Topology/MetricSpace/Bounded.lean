/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Balls in metric spaces: diameters and balls far away

A closed ball of radius `r` has extended diameter at most `2 r`
(`Metric.ediam_closedBall_le`). This is the extended-diameter counterpart of Mathlib's
`Metric.diam_closedBall`, stated for every real radius: a ball of negative radius is empty.

Any two points of a bounded set are within its diameter (`Metric.edist_le_diam_of_mem`), and in
a bounded space any two points are within the diameter of the whole space
(`Metric.edist_le_diam_univ`), in the extended form used by Mathlib's Hölder bounds.

Closed balls of a fixed radius `r` leave every bounded set as their centre does: as `x` tends to
infinity in the cobounded filter, `closedBall x r` is eventually contained in every set whose
complement is bounded (`Metric.tendsto_closedBall_cobounded_smallSets`). So a property holding
near infinity eventually holds on whole balls of radius `r`, which is the form in which local
estimates on balls, such as mean-value inequalities, are applied near infinity. In particular a
property holding near infinity holds on a neighbourhood of each point near infinity
(`Metric.eventually_cobounded_eventually_nhds`).

In a proper space the frontier of a bounded set is compact
(`Bornology.IsBounded.isCompact_frontier`), as a closed subset of its compact closure.

In a proper pseudometric space, closed balls are compact and hence totally bounded, so any
function whose distance from a base point is uniformly bounded has totally bounded range
(`Metric.totallyBounded_range_of_dist_le`).
-/

public section

open scoped Topology

namespace Metric

variable {X : Type*} [PseudoMetricSpace X]

/-- A closed ball of radius `r` has extended diameter at most `2 r`. -/
theorem ediam_closedBall_le (x : X) (r : ℝ) :
    ediam (closedBall x r) ≤ ENNReal.ofReal (2 * r) :=
  ediam_le_of_forall_dist_le fun y hy z hz => (dist_triangle_right y z x).trans <| by
    linarith [mem_closedBall.1 hy, mem_closedBall.1 hz]

/-- Any two points of a bounded set are within its diameter. -/
theorem edist_le_diam_of_mem {s : Set X} (hs : Bornology.IsBounded s) {x y : X} (hx : x ∈ s)
    (hy : y ∈ s) : edist x y ≤ ((diam s).toNNReal : ENNReal) := by
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (dist_le_diam_of_mem hs hx hy)

/-- In a bounded space any two points are within the diameter of the whole space. -/
theorem edist_le_diam_univ [BoundedSpace X] (x y : X) :
    edist x y ≤ ((diam (Set.univ : Set X)).toNNReal : ENNReal) :=
  edist_le_diam_of_mem (Bornology.isBounded_univ.2 inferInstance) (Set.mem_univ x)
    (Set.mem_univ y)

/-- Closed balls of a fixed radius tend to infinity with their centres: as `x` tends to infinity
in the cobounded filter, `closedBall x r` is eventually contained in each set whose complement is
bounded. -/
theorem tendsto_closedBall_cobounded_smallSets (r : ℝ) :
    Filter.Tendsto (fun x : X ↦ closedBall x r) (Bornology.cobounded X)
      (Bornology.cobounded X).smallSets := by
  rcases isEmpty_or_nonempty X with hX | ⟨⟨c⟩⟩
  · simp [Filter.filter_eq_bot_of_isEmpty]
  refine ((hasBasis_cobounded_compl_closedBall c).smallSets).tendsto_right_iff.2 fun s _ ↦ ?_
  refine (hasBasis_cobounded_compl_closedBall c).eventually_iff.2
    ⟨s + r, trivial, fun x hx y hy ↦ ?_⟩
  simp only [Set.mem_compl_iff, mem_closedBall, not_le] at hx ⊢
  linarith [dist_triangle x y c, mem_closedBall'.1 hy]

/-- A property holds near every point of a neighbourhood of infinity exactly when it holds on a
neighbourhood of infinity: the cobounded filter has a basis of open sets. -/
theorem eventually_cobounded_eventually_nhds {p : X → Prop} :
    (∀ᶠ x in Bornology.cobounded X, ∀ᶠ y in 𝓝 x, p y) ↔ ∀ᶠ x in Bornology.cobounded X, p x := by
  refine ⟨fun h ↦ h.mono fun _ hx ↦ hx.self_of_nhds, fun h ↦ ?_⟩
  filter_upwards [(tendsto_closedBall_cobounded_smallSets 1).eventually
    (Filter.eventually_smallSets_subset.2 h)] with x hx
  exact Filter.mem_of_superset (closedBall_mem_nhds x one_pos) hx

/-- In a proper pseudometric space, the range of a function bounded in distance from a base point
is totally bounded. -/
theorem totallyBounded_range_of_dist_le [ProperSpace X] {ι : Type*} {f : ι → X} {c : X} {M : ℝ}
    (hM : ∀ i, dist (f i) c ≤ M) : TotallyBounded (Set.range f) :=
  (isCompact_closedBall c M).totallyBounded.subset
    (Set.range_subset_iff.2 fun i ↦ mem_closedBall.2 (hM i))

end Metric

/-- In a proper space the frontier of a bounded set is compact. -/
theorem Bornology.IsBounded.isCompact_frontier {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {s : Set X} (hs : Bornology.IsBounded s) : IsCompact (frontier s) :=
  hs.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
