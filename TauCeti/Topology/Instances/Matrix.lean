/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Metrizable.Basic

/-!
# Metrizability of the space of matrices

Mathlib gives `Matrix m n α` the product topology of `m → n → α`, so for finite index types it is
pseudo-metrizable whenever `α` is. This makes metrizable-codomain results, such as measurability
of pointwise limits of measurable maps, available for matrix-valued functions without choosing a
matrix norm.

The same product topology gives entrywise control of a real matrix-valued map near a point of
continuity, again without a matrix norm
(`ContinuousAt.exists_ball_subset_forall_abs_sub_le`).
-/

public section

namespace TauCeti

/-- A space of matrices with finitely many rows and columns over a pseudo-metrizable space is
pseudo-metrizable. -/
instance {m n α : Type*} [Finite m] [Finite n] [TopologicalSpace α]
    [TopologicalSpace.PseudoMetrizableSpace α] :
    TopologicalSpace.PseudoMetrizableSpace (Matrix m n α) :=
  -- The topology of `Matrix m n α` is by definition the product topology on `m → n → α`.
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (m → n → α))

end TauCeti

namespace ContinuousAt

open Filter Metric
open scoped Topology

/-- If a real matrix-valued map `a` on a pseudo-metric space is continuous at `x`, then for every
neighbourhood `s` of `x` and every `ε > 0` there is a ball `B(x, r) ⊆ s` on which every entry of
`a` differs from its value at `x` by at most `ε`. -/
theorem exists_ball_subset_forall_abs_sub_le {X m n : Type*} [PseudoMetricSpace X] [Finite m]
    [Finite n] {a : X → Matrix m n ℝ} {x : X} (hcont : ContinuousAt a x) {s : Set X}
    (hs : s ∈ 𝓝 x) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ s ∧ ∀ y ∈ ball x r, ∀ i j, |a y i j - a x i j| ≤ ε := by
  have hev : ∀ᶠ y in 𝓝 x, y ∈ s ∧ ∀ i j, |a y i j - a x i j| ≤ ε := by
    refine Eventually.and hs (eventually_all.2 fun i => eventually_all.2 fun j => ?_)
    have hij : ContinuousAt (fun y => a y i j) x :=
      (continuous_id.matrix_elem i j).continuousAt.comp hcont
    filter_upwards [Metric.tendsto_nhds.1 hij ε hε] with y hy
    exact (Real.dist_eq _ _ ▸ hy).le
  obtain ⟨r, hr, hrx⟩ := Metric.eventually_nhds_iff_ball.1 hev
  exact ⟨r, hr, fun y hy => (hrx y hy).1, fun y hy => (hrx y hy).2⟩

end ContinuousAt
