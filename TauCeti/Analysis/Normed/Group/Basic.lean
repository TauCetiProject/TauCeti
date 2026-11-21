/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Basic facts about seminormed groups

In a seminormed additive group, the squared distance between two points is at most twice the sum
of their squared distances to any third point: the triangle inequality through `c`, squared with
`(x + y) ^ 2 ≤ 2 (x ^ 2 + y ^ 2)`; likewise the squared norm of a sum of three vectors is at most
three times the sum of their squared norms. The extended norm satisfies the triangle inequality
`‖u - w‖ₑ ≤ ‖u - v‖ₑ + ‖v - w‖ₑ`. Through the point `b`, a bound `c ‖a - b‖² ≤ r` with
`c > 0` bounds `‖a‖²` by `2 / c * r + 2 ‖b‖²`. The reciprocal transform `(1 + ‖x - a‖²)⁻¹` of a
squared distance is at most `1`.

An unbounded set stays unbounded after removing a closed ball, since a closed ball is bounded.

A bound on the norms of a set with two distinct points is positive, since one of the points is
nonzero.

A continuous function on `ℝ` with limits at `±∞` is bounded.

A map bounded by `M` on a set sends it into the closed ball of radius `2 * M` around any of its
values there.

Near `0`, the product `‖x‖ * R` is eventually less than any positive bound.

A sum `z + a` with `‖a‖ < ‖z‖` is nonzero.

A constant bound on `‖f x‖` over a ball of positive radius is nonnegative, since the ball
contains `0`.

The translation by `c - c₀`, which takes `c₀` to `c`, preserves distances to these centres.

The points at which a map comes within `ε` of a set form the preimage of the union of the closed
`ε`-balls about its points.

A point off a finite set stays farther than `ε` from all of its points for every small enough
`ε > 0`.

## Main declarations

* `TauCeti.norm_sub_sq_le_two_mul` -- the squared triangle inequality through an intermediate
  point.
* `TauCeti.norm_add_add_sq_le_three_mul` -- the squared triangle inequality for three summands.
* `TauCeti.eNorm_sub_le_eNorm_sub_add_eNorm_sub` -- the triangle inequality for the extended norm.
* `TauCeti.norm_sq_le_of_mul_norm_sub_sq_le` -- `c ‖a - b‖² ≤ r` with `c > 0` bounds `‖a‖²` by
  `2 / c * r + 2 ‖b‖²`.
* `TauCeti.inv_one_add_norm_sub_sq_le_one` -- the reciprocal transform of a squared distance is at
  most `1`.
* `TauCeti.not_isBounded_inter_lt_norm_sub` -- the part of an unbounded set outside a closed ball
  is unbounded.
* `Set.Nontrivial.pos_of_forall_norm_le` -- a bound on the norms of a nontrivial set is positive.
* `TauCeti.exists_forall_norm_le_of_tendsto` -- a continuous function `ℝ → F` with limits at `±∞`
  is bounded.
* `TauCeti.exists_enorm_sub_le_mul_of_reflTransGen` -- constants joined by a chain of related
  indices are uniformly close if constants at related indices are.
* `TauCeti.mapsTo_closedBall_of_forall_norm_le` -- a map bounded by `M` on `s` sends `s` into the
  closed ball of radius `2 * M` around any of its values on `s`.
* `TauCeti.eventually_norm_mul_lt` -- eventually near `0`, `‖x‖ * R < ρ` for any `ρ > 0`.
* `TauCeti.add_ne_zero_of_norm_lt` -- `z + a ≠ 0` when `‖a‖ < ‖z‖`.
* `TauCeti.nonneg_of_forall_norm_lt` -- a constant bound on `‖f x‖` over a ball of positive radius
  is nonnegative.
* `TauCeti.dist_add_sub_eq` -- `dist (x + (c - c₀)) c = dist x c₀`.
* `TauCeti.setOf_exists_norm_sub_le_eq_preimage` -- `{t | ∃ s ∈ S, ‖f t - s‖ ≤ ε}` is the
  preimage under `f` of the union of the closed `ε`-balls about the points of `S`.
* `TauCeti.eventually_not_exists_norm_sub_le` -- a point off a finite set `S` is, for every small
  enough `ε > 0`, farther than `ε` from each point of `S`.
-/

public section

open Bornology Metric Filter
open scoped ENNReal NNReal Topology

namespace TauCeti

/-- **Squared triangle inequality.** The squared distance from `a` to `b` is at most twice the sum
of the squared distances from `a` and from `b` to an intermediate point `c`. -/
theorem norm_sub_sq_le_two_mul {E : Type*} [SeminormedAddCommGroup E] (a b c : E) :
    ‖a - b‖ ^ 2 ≤ 2 * (‖a - c‖ ^ 2 + ‖b - c‖ ^ 2) :=
  (pow_le_pow_left₀ (norm_nonneg _)
    ((norm_sub_le_norm_sub_add_norm_sub a c b).trans_eq (by rw [norm_sub_rev c b])) 2).trans
    add_sq_le

/-- **Squared triangle inequality for three summands.** The squared norm of `a + b + c` is at most
three times the sum of the squared norms of `a`, `b` and `c`. -/
theorem norm_add_add_sq_le_three_mul {E : Type*} [SeminormedAddCommGroup E] (a b c : E) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) :=
  (pow_le_pow_left₀ (norm_nonneg _) norm_add₃_le 2).trans <| by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖a‖ - ‖c‖)]

/-- **Triangle inequality for the extended norm.** `‖u - w‖ₑ ≤ ‖u - v‖ₑ + ‖v - w‖ₑ`, the
extended-norm form of `norm_sub_le_norm_sub_add_norm_sub`. -/
theorem eNorm_sub_le_eNorm_sub_add_eNorm_sub {G : Type*} [SeminormedAddCommGroup G] (u v w : G) :
    ‖u - w‖ₑ ≤ ‖u - v‖ₑ + ‖v - w‖ₑ := by
  simpa only [eDist_eq_eNorm_sub] using edist_triangle u v w

/-- If `c ‖a - b‖² ≤ r` with `c > 0`, then `‖a‖² ≤ 2 / c * r + 2 ‖b‖²`: the squared triangle
inequality through `b`. -/
theorem norm_sq_le_of_mul_norm_sub_sq_le {E : Type*} [SeminormedAddGroup E] {a b : E}
    {c r : ℝ} (hc : 0 < c) (h : c * ‖a - b‖ ^ 2 ≤ r) :
    ‖a‖ ^ 2 ≤ 2 / c * r + 2 * ‖b‖ ^ 2 := by
  have hab : ‖a - b‖ ^ 2 ≤ r / c := by
    rw [le_div_iff₀ hc, mul_comm]
    exact h
  have htri := (pow_le_pow_left₀ (norm_nonneg a) (norm_le_norm_sub_add a b) 2).trans add_sq_le
  rw [div_mul_eq_mul_div, mul_div_assoc]
  linarith

/-- The reciprocal transform `(1 + ‖x - a‖²)⁻¹` of the squared distance is at most `1`. -/
theorem inv_one_add_norm_sub_sq_le_one {E : Type*} [SeminormedAddCommGroup E] (x a : E) :
    (1 + ‖x - a‖ ^ 2)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (le_add_of_nonneg_right (by positivity))

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

/-- Eventually near `0`, the norm of `x` times a fixed real `R` is less than any `ρ > 0`. -/
theorem eventually_norm_mul_lt {E : Type*} [SeminormedAddGroup E] (R : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ x in 𝓝 (0 : E), ‖x‖ * R < ρ :=
  (tendsto_norm_zero.mul_const R).eventually (gt_mem_nhds (by rwa [zero_mul]))

/-- A sum `z + a` with `‖a‖ < ‖z‖` is nonzero. -/
theorem add_ne_zero_of_norm_lt {E : Type*} [SeminormedAddGroup E] {a z : E} (h : ‖a‖ < ‖z‖) :
    z + a ≠ 0 :=
  fun h' ↦ h.ne' (by rw [eq_neg_of_add_eq_zero_left h', norm_neg])

/-- A continuous function `ℝ → F` into a seminormed group with limits at `±∞` is bounded. -/
theorem exists_forall_norm_le_of_tendsto {F : Type*} [SeminormedAddCommGroup F] {A : ℝ → F}
    {Aminus Aplus : F} (hA : Continuous A) (hbot : Tendsto A atBot (𝓝 Aminus))
    (htop : Tendsto A atTop (𝓝 Aplus)) : ∃ M, ∀ s, ‖A s‖ ≤ M := by
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    (hA.isBounded_range_iff_isBigO_atTop_atBot.mpr
      ⟨htop.isBigO_one ℝ, hbot.isBigO_one ℝ⟩)
  exact ⟨M, fun s ↦ hM _ (Set.mem_range_self s)⟩

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
      _ ≤ ‖a k l - a k j‖ₑ + ‖a k j - a k i₀‖ₑ := eNorm_add_le _ _
      _ ≤ D₂ * G k + D₁ * G k := add_le_add (hD₂ k) (hD₁ k)
      _ = ↑(D₂ + D₁) * G k := by push_cast; ring

/-- A constant bound on `‖f x‖` over a ball of positive radius is nonnegative, since the ball
contains `0`. -/
theorem nonneg_of_forall_norm_lt {E F 𝓕 : Type*} [SeminormedAddGroup E] [SeminormedAddGroup F]
    [FunLike 𝓕 E F] (f : 𝓕) {δ B : ℝ} (hδ : 0 < δ) (hf : ∀ x : E, ‖x‖ < δ → ‖f x‖ ≤ B) :
    0 ≤ B :=
  (norm_nonneg _).trans <| hf 0 (by simpa using hδ)

/-- The translation by `c - c₀`, which takes `c₀` to `c`, preserves distances: the distance from
`x + (c - c₀)` to `c` is the distance from `x` to `c₀`. -/
theorem dist_add_sub_eq {E : Type*} [SeminormedAddCommGroup E] (x c c₀ : E) :
    dist (x + (c - c₀)) c = dist x c₀ := by
  rw [← dist_add_right x c₀ (c - c₀), add_sub_cancel]

/-- The set of points at which `f` comes within `ε` of some point of `S` is the preimage under `f`
of the union of the closed `ε`-balls about the points of `S`. -/
theorem setOf_exists_norm_sub_le_eq_preimage {α E : Type*} [SeminormedAddCommGroup E] (f : α → E)
    (S : Set E) (ε : ℝ) :
    {t | ∃ s ∈ S, ‖f t - s‖ ≤ ε} = f ⁻¹' ⋃ s ∈ S, closedBall s ε := by
  ext; simp [dist_eq_norm]

/-- **A point off a finite set keeps a positive distance from it.** If `z` is not in the finite set
`S`, then for every small enough `ε > 0` it is farther than `ε` from each point of `S`. -/
theorem eventually_not_exists_norm_sub_le {E : Type*} [NormedAddGroup E] {z : E} {S : Finset E}
    (hz : z ∉ S) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ¬ ∃ s ∈ S, ‖z - s‖ ≤ ε := by
  -- Each of the finitely many distances `‖z - s‖` is positive.
  have hlt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ s ∈ S, ε < ‖z - s‖ :=
    (eventually_all_finset S).mpr fun s hs => (eventually_lt_nhds <| norm_sub_pos_iff.mpr
      fun h : z = s => hz (h ▸ hs)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hlt] with ε hε ⟨s, hs, hle⟩
  exact (hε s hs).not_ge hle

end TauCeti
