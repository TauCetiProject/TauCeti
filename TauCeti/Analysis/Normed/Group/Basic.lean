/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Uniform
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

/-- Constants joined by a chain of related indices are uniformly close, if constants at related
indices are. -/
theorem exists_enorm_sub_le_mul_of_reflTransGen {X F ι : Type*} [NormedAddCommGroup F]
    {R : ι → ι → Prop} {i₀ : ι}
    (P : (X → F) → (ι → F) → ℝ≥0∞ → Prop)
    (hadj : ∀ i j, R i j → ∃ D : ℝ≥0, ∀ f a G, P f a G → ‖a j - a i‖ₑ ≤ D * G) {j : ι}
    (hj : Relation.ReflTransGen R i₀ j) :
    ∃ D : ℝ≥0, ∀ f a G, P f a G → ‖a j - a i₀‖ₑ ≤ D * G := by
  induction hj with
  | refl => exact ⟨0, fun _ _ _ _ ↦ by simp⟩
  | @tail j k _ hjk ih =>
    obtain ⟨D₁, hD₁⟩ := ih
    obtain ⟨D₂, hD₂⟩ := hadj j k hjk
    refine ⟨D₂ + D₁, fun f a G hP ↦ ?_⟩
    calc ‖a k - a i₀‖ₑ = ‖(a k - a j) + (a j - a i₀)‖ₑ := by rw [sub_add_sub_cancel]
      _ ≤ ‖a k - a j‖ₑ + ‖a j - a i₀‖ₑ := enorm_add_le _ _
      _ ≤ D₂ * G + D₁ * G := add_le_add (hD₂ f a G hP) (hD₁ f a G hP)
      _ = ↑(D₂ + D₁) * G := by push_cast; ring

end TauCeti
