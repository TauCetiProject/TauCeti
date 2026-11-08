/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Basic facts about seminormed groups

In a seminormed additive group, the squared distance between two points is at most twice the sum
of their squared distances to any third point: the triangle inequality through `c`, squared with
`(x + y) ^ 2 ≤ 2 (x ^ 2 + y ^ 2)`.

An unbounded set stays unbounded after removing a closed ball, since a closed ball is bounded.

A bound on the norms of a set with two distinct points is positive, since one of the points is
nonzero.

A continuous function on `ℝ` with limits at `±∞` is bounded.

A map bounded by `M` on a set sends it into the closed ball of radius `2 * M` around any of its
values there.

## Main declarations

* `TauCeti.norm_sub_sq_le_two_mul` -- the squared triangle inequality through an intermediate
  point.
* `TauCeti.not_isBounded_inter_lt_norm_sub` -- the part of an unbounded set outside a closed ball
  is unbounded.
* `Set.Nontrivial.pos_of_forall_norm_le` -- a bound on the norms of a nontrivial set is positive.
* `TauCeti.exists_forall_norm_le_of_tendsto` -- a continuous function `ℝ → F` with limits at `±∞`
  is bounded.
* `TauCeti.mapsTo_closedBall_of_forall_norm_le` -- a map bounded by `M` on `s` sends `s` into the
  closed ball of radius `2 * M` around any of its values on `s`.
-/

public section

open Bornology Metric Filter
open scoped Topology

namespace TauCeti

/-- **Squared triangle inequality.** The squared distance from `a` to `b` is at most twice the sum
of the squared distances from `a` and from `b` to an intermediate point `c`. -/
theorem norm_sub_sq_le_two_mul {E : Type*} [SeminormedAddCommGroup E] (a b c : E) :
    ‖a - b‖ ^ 2 ≤ 2 * (‖a - c‖ ^ 2 + ‖b - c‖ ^ 2) :=
  (pow_le_pow_left₀ (norm_nonneg _)
    ((norm_sub_le_norm_sub_add_norm_sub a c b).trans_eq (by rw [norm_sub_rev c b])) 2).trans
    add_sq_le

/-- An unbounded set stays unbounded after removing a closed ball: its far part
`s ∩ {w | ρ < ‖w - c‖}` is unbounded. -/
theorem not_isBounded_inter_lt_norm_sub {E : Type*} [SeminormedAddCommGroup E] {s : Set E}
    (hs : ¬IsBounded s) (c : E) (ρ : ℝ) : ¬IsBounded (s ∩ {w : E | ρ < ‖w - c‖}) :=
  fun h => hs <| (h.union (isBounded_closedBall (x := c) (r := ρ))).subset fun w hw => by
    by_cases hw' : ρ < ‖w - c‖
    · exact Or.inl ⟨hw, hw'⟩
    · exact Or.inr (mem_closedBall_iff_norm.mpr (not_lt.mp hw'))

/-- In a normed group, a bound on the norms of a set with two distinct points is positive. -/
theorem _root_.Set.Nontrivial.pos_of_forall_norm_le {E : Type*} [NormedAddGroup E] {s : Set E}
    (hs : s.Nontrivial) {r : ℝ} (hr : ∀ x ∈ s, ‖x‖ ≤ r) : 0 < r := by
  obtain ⟨x, hxs, hx0⟩ := hs.exists_ne 0
  exact (norm_pos_iff.mpr hx0).trans_le (hr x hxs)

/-- A map bounded by `M` on a set `s` sends `s` into the closed ball of radius `2 * M` around its
value at any point `c ∈ s`. -/
theorem mapsTo_closedBall_of_forall_norm_le {α F : Type*} [SeminormedAddCommGroup F] {f : α → F}
    {s : Set α} {c : α} {M : ℝ} (hM : ∀ y ∈ s, ‖f y‖ ≤ M) (hc : c ∈ s) :
    Set.MapsTo f s (closedBall (f c) (2 * M)) := fun y hy => by
  rw [mem_closedBall]
  linarith [dist_le_norm_add_norm (f y) (f c), hM y hy, hM c hc]

/-- A continuous function `ℝ → F` into a seminormed group with limits at `±∞` is bounded. -/
theorem exists_forall_norm_le_of_tendsto {F : Type*} [SeminormedAddCommGroup F] {A : ℝ → F}
    {Aminus Aplus : F} (hA : Continuous A) (hbot : Tendsto A atBot (𝓝 Aminus))
    (htop : Tendsto A atTop (𝓝 Aplus)) : ∃ M, ∀ s, ‖A s‖ ≤ M := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    (hA.isBounded_range_iff_isBigO_atTop_atBot.mpr
      ⟨htop.isBigO_one ℝ, hbot.isBigO_one ℝ⟩)
  exact ⟨M, fun s ↦ hM _ (Set.mem_range_self s)⟩

end TauCeti
