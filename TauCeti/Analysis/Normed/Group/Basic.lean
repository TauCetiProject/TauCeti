/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Basic facts about seminormed groups

In a seminormed additive group, the squared distance between two points is at most twice the sum
of their squared distances to any third point: the triangle inequality through `c`, squared with
`(x + y) ^ 2 ≤ 2 (x ^ 2 + y ^ 2)`.

An unbounded set stays unbounded after removing a closed ball, since a closed ball is bounded.

A bound on the norms of a set with two distinct points is positive, since one of the points is
nonzero.

A map bounded by `M` on a set sends it into the closed ball of radius `2 * M` around any of its
values there.

## Main declarations

* `TauCeti.norm_sub_sq_le_two_mul` -- the squared triangle inequality through an intermediate
  point.
* `TauCeti.not_isBounded_inter_lt_norm_sub` -- the part of an unbounded set outside a closed ball
  is unbounded.
* `Set.Nontrivial.pos_of_forall_norm_le` -- a bound on the norms of a nontrivial set is positive.
* `TauCeti.exists_enorm_sub_le_mul_of_reflTransGen` -- constants joined by a chain of related
  indices are uniformly close if constants at related indices are.
* `TauCeti.mapsTo_closedBall_of_forall_norm_le` -- a map bounded by `M` on `s` sends `s` into the
  closed ball of radius `2 * M` around any of its values on `s`.
-/

public section

open Bornology Metric
open scoped ENNReal NNReal

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

/-- Families of vectors joined by a chain of related indices are uniformly close, if the vectors at
related indices are: if `‖a k j - a k i‖ ≤ D * G k` for related `i j` and all `k`, then the
same holds, with a constant `D'` independent of `k`, for any `j` reachable from `i₀`. -/
theorem exists_enorm_sub_le_mul_of_reflTransGen {κ F ι : Type*} [SeminormedAddGroup F]
    {R : ι → ι → Prop} {i₀ : ι} {a : κ → ι → F} {G : κ → ℝ≥0∞}
    (hadj : ∀ i j, R i j → ∃ D : ℝ≥0, ∀ k, ‖a k j - a k i‖ₑ ≤ D * G k) {j : ι}
    (hj : Relation.ReflTransGen R i₀ j) :
    ∃ D : ℝ≥0, ∀ k, ‖a k j - a k i₀‖ₑ ≤ D * G k := by
  induction hj with
  | refl => exact ⟨0, fun _ ↦ by simp⟩
  | @tail j l _ hjl ih =>
    obtain ⟨D₁, hD₁⟩ := ih
    obtain ⟨D₂, hD₂⟩ := hadj j l hjl
    refine ⟨D₂ + D₁, fun k ↦ ?_⟩
    calc ‖a k l - a k i₀‖ₑ = ‖(a k l - a k j) + (a k j - a k i₀)‖ₑ := by rw [sub_add_sub_cancel]
      _ ≤ ‖a k l - a k j‖ₑ + ‖a k j - a k i₀‖ₑ := enorm_add_le _ _
      _ ≤ D₂ * G k + D₁ * G k := add_le_add (hD₂ k) (hD₁ k)
      _ = ↑(D₂ + D₁) * G k := by push_cast; ring

end TauCeti
