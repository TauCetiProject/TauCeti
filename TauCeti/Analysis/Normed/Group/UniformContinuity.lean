/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Uniformly small finite families of increments

Uniform continuity sends finite families of pairs with uniformly vanishing distances to
families of increments with vanishing sup norm. The finite index type may vary along any
filter. In particular, this controls continuous-path increments along vanishing-mesh grids
in a compact time interval, as needed in Taylor remainder estimates for Itô's formula.
-/

public section

open Filter Set
open scoped Topology

namespace UniformContinuousOn

/-- Uniform continuity controls the sup norm of a varying finite family of increments when
all endpoints eventually lie in the domain and their distances vanish uniformly. -/
theorem tendsto_norm_sub_of_dist_le {X E ι : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup E] {s : Set X} {f : X → E} (hf : UniformContinuousOn f s)
    {l : Filter ι} {n : ι → ℕ} {x y : ∀ k, Fin (n k) → X} {δ : ι → ℝ}
    (hx : ∀ᶠ k in l, ∀ i, x k i ∈ s) (hy : ∀ᶠ k in l, ∀ i, y k i ∈ s)
    (hxy : ∀ᶠ k in l, ∀ i, dist (y k i) (x k i) ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) :
    Tendsto (fun k ↦ ‖fun i ↦ f (y k i) - f (x k i)‖) l (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨η, hη, hosc⟩ := Metric.uniformContinuousOn_iff.1 hf (ε / 2) (half_pos hε)
  filter_upwards [(tendsto_order.1 hδ).2 η hη, hx, hy, hxy] with k hk hxk hyk hxyk
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (pi_norm_le_iff_of_nonneg (half_pos hε).le).2
  intro i
  simpa only [dist_eq_norm] using (hosc _ (hyk i) _ (hxk i) ((hxyk i).trans_lt hk)).le

end UniformContinuousOn
