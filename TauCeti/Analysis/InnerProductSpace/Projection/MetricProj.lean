/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import TauCeti.Analysis.InnerProductSpace.Projection.Minimal
import TauCeti.Topology.MetricSpace.HausdorffDistance

/-!
# The metric projection onto a set

The metric projection `TauCeti.metricProj s x` sends a point `x` of a normed group to a point of
`s` nearest to `x`, that is a point `y ∈ s` with `‖x - y‖ = Metric.infDist x s`, chosen when
one exists, and to the junk value `0` otherwise. It is a total function on every set, which lets
recursions such as projected gradient methods be written without carrying membership proofs.

In a real inner product space a nonempty complete convex set `K` has a nearest point to every
`x`, so `metricProj K x ∈ K`, and it is characterized by the variational inequality
`⟪x - metricProj K x, u - metricProj K x⟫ ≤ 0` for `u ∈ K`. Expanding `‖x - u‖ ^ 2` around
`metricProj K x` turns this into the projection inequality

`‖metricProj K x - u‖ ^ 2 + ‖x - metricProj K x‖ ^ 2 ≤ ‖x - u‖ ^ 2`,

which says that projecting onto `K` brings a point closer to every point of `K`, with a gain of
at least the squared distance moved. It is the step that controls the iterates of projected and
online gradient descent.

## Main definitions

* `TauCeti.metricProj s x`: a point of `s` nearest to `x` when one exists, and `0` otherwise.

## Main results

* `TauCeti.metricProj_mem_of_exists`, `TauCeti.norm_sub_metricProj_of_exists`: when a nearest
  point exists, `metricProj s x` is one.
* `TauCeti.metricProj_eq_self_of_mem`: points of `s` project to themselves.
* `TauCeti.metricProj_mem`, `TauCeti.norm_sub_metricProj`: the metric projection onto a nonempty
  complete convex set is a nearest point of the set.
* `TauCeti.exists_norm_sub_eq_infDist_of_isComplete`: a nonempty complete convex set in a real
  inner product space has a nearest point to every point.
* `TauCeti.inner_sub_sub_nonpos_of_norm_sub_eq_infDist`,
  `TauCeti.inner_sub_metricProj_sub_metricProj_nonpos`: the variational inequality, for any
  nearest point and for the metric projection.
* `TauCeti.metricProj_eq_iff`, `TauCeti.eq_metricProj_of_norm_sub_eq_infDist`: the variational
  inequality characterizes the metric projection, which is the unique nearest point.
* `TauCeti.norm_metricProj_sub_sq_add_norm_sub_metricProj_sq_le`: the projection inequality.
* `TauCeti.norm_metricProj_sub_le`: projecting onto `K` does not increase the distance to points
  of `K`.

## References

* S. Bubeck, *Convex optimization: algorithms and complexity*, Foundations and Trends in Machine
  Learning 8 (2015), Lemma 3.1.
* E. Hazan, *Introduction to online convex optimization*, 2nd ed., MIT Press, 2022, Theorem 2.1.
* F. Orabona, *A modern introduction to online learning*, arXiv:1912.13213, Proposition 2.11.
-/

public section

open Metric
open scoped RealInnerProductSpace

namespace TauCeti

section NormedAddCommGroup

variable {E : Type*} [NormedAddCommGroup E] {s : Set E} {x : E}

open Classical in
/-- The metric projection onto `s`: a point `y ∈ s` nearest to `x`, that is with
`‖x - y‖ = Metric.infDist x s`, chosen when one exists, and `0` otherwise. -/
noncomputable def metricProj (s : Set E) (x : E) : E :=
  if h : ∃ y ∈ s, ‖x - y‖ = infDist x s then h.choose else 0

private theorem metricProj_spec (h : ∃ y ∈ s, ‖x - y‖ = infDist x s) :
    metricProj s x ∈ s ∧ ‖x - metricProj s x‖ = infDist x s := by
  rw [metricProj, dite_eq_left_of_eq_true (eq_true h)]
  exact h.choose_spec

/-- When some point of `s` is nearest to `x`, the metric projection of `x` lies in `s`. -/
theorem metricProj_mem_of_exists (h : ∃ y ∈ s, ‖x - y‖ = infDist x s) : metricProj s x ∈ s :=
  (metricProj_spec h).1

/-- When some point of `s` is nearest to `x`, the metric projection of `x` is nearest to `x`. -/
theorem norm_sub_metricProj_of_exists (h : ∃ y ∈ s, ‖x - y‖ = infDist x s) :
    ‖x - metricProj s x‖ = infDist x s :=
  (metricProj_spec h).2

/-- When no point of `s` is nearest to `x`, the metric projection of `x` is the junk value
`0`. -/
theorem metricProj_of_not_exists (h : ¬∃ y ∈ s, ‖x - y‖ = infDist x s) : metricProj s x = 0 := by
  rw [metricProj, dite_eq_right_of_eq_false (eq_false h)]

@[simp]
theorem metricProj_empty (x : E) : metricProj ∅ x = 0 :=
  metricProj_of_not_exists (by simp)

/-- A point of `s` is its own metric projection. -/
@[simp]
theorem metricProj_eq_self_of_mem (hx : x ∈ s) : metricProj s x = x := by
  have h : ∃ y ∈ s, ‖x - y‖ = infDist x s := ⟨x, hx, by simp [infDist_zero_of_mem hx]⟩
  have hdist := norm_sub_metricProj_of_exists h
  rw [infDist_zero_of_mem hx, norm_sub_eq_zero_iff] at hdist
  exact hdist.symm

end NormedAddCommGroup

section InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {K : Set E}

/-- A nonempty complete convex set in a real inner product space has a point nearest to every
point `x`: some `y ∈ K` has `‖x - y‖ = Metric.infDist x K`. -/
theorem exists_norm_sub_eq_infDist_of_isComplete (hne : K.Nonempty) (hc : IsComplete K)
    (hK : Convex ℝ K) (x : E) : ∃ y ∈ K, ‖x - y‖ = infDist x K := by
  obtain ⟨y, hy, h⟩ := exists_norm_eq_iInf_of_complete_convex hne hc hK x
  exact ⟨y, hy, h.trans infDist_eq_iInf_norm_sub.symm⟩

/-- The metric projection onto a nonempty complete convex set lies in the set. -/
theorem metricProj_mem (hne : K.Nonempty) (hc : IsComplete K) (hK : Convex ℝ K) (x : E) :
    metricProj K x ∈ K :=
  metricProj_mem_of_exists (exists_norm_sub_eq_infDist_of_isComplete hne hc hK x)

/-- The metric projection onto a nonempty complete convex set is a nearest point of the set. -/
theorem norm_sub_metricProj (hne : K.Nonempty) (hc : IsComplete K) (hK : Convex ℝ K) (x : E) :
    ‖x - metricProj K x‖ = infDist x K :=
  norm_sub_metricProj_of_exists (exists_norm_sub_eq_infDist_of_isComplete hne hc hK x)

/-- **The variational inequality of a nearest point.** If `K` is convex and `y ∈ K` is nearest
to `x`, that is `‖x - y‖ = Metric.infDist x K`, then `⟪x - y, z - y⟫ ≤ 0` for every `z ∈ K`. -/
theorem inner_sub_sub_nonpos_of_norm_sub_eq_infDist (hK : Convex ℝ K) {x y : E} (hy : y ∈ K)
    (h : ‖x - y‖ = infDist x K) : ∀ z ∈ K, ⟪x - y, z - y⟫ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero hK hy).1 (h.trans infDist_eq_iInf_norm_sub)

/-- **The variational inequality of the metric projection.** If `K` is a complete convex set
and `u ∈ K`, then `⟪x - metricProj K x, u - metricProj K x⟫ ≤ 0`: the segment from the
projection to `u` makes a non-acute angle (at least `π / 2`) with the segment from the projection
to `x`. -/
theorem inner_sub_metricProj_sub_metricProj_nonpos (hc : IsComplete K) (hK : Convex ℝ K)
    (x : E) {u : E} (hu : u ∈ K) : ⟪x - metricProj K x, u - metricProj K x⟫ ≤ 0 := by
  have h := exists_norm_sub_eq_infDist_of_isComplete ⟨u, hu⟩ hc hK x
  exact inner_sub_sub_nonpos_of_norm_sub_eq_infDist hK (metricProj_mem_of_exists h)
    (norm_sub_metricProj_of_exists h) u hu

/-- **The variational characterization of the metric projection.** For a nonempty complete
convex set `K`, `metricProj K x = p` if and only if `p ∈ K` and `⟪x - p, z - p⟫ ≤ 0` for every
`z ∈ K`. -/
theorem metricProj_eq_iff (hne : K.Nonempty) (hc : IsComplete K) (hK : Convex ℝ K) {x p : E} :
    metricProj K x = p ↔ p ∈ K ∧ ∀ z ∈ K, ⟪x - p, z - p⟫ ≤ 0 := by
  constructor
  · rintro rfl
    exact ⟨metricProj_mem hne hc hK x,
      fun z hz ↦ inner_sub_metricProj_sub_metricProj_nonpos hc hK x hz⟩
  · rintro ⟨hp, hvar⟩
    have h₁ := hvar _ (metricProj_mem hne hc hK x)
    have h := norm_sub_le_norm_sub_of_inner_sub_le_zero
      (inner_sub_metricProj_sub_metricProj_nonpos hc hK x hp) h₁
    rw [sub_self, norm_zero] at h
    exact sub_eq_zero.1 (norm_le_zero_iff.1 h)

/-- Every nearest point of a complete convex set `K` to `x` is the metric projection of `x`. -/
theorem eq_metricProj_of_norm_sub_eq_infDist (hc : IsComplete K) (hK : Convex ℝ K) {x y : E}
    (hy : y ∈ K) (h : ‖x - y‖ = infDist x K) : y = metricProj K x :=
  ((metricProj_eq_iff ⟨y, hy⟩ hc hK).2
    ⟨hy, inner_sub_sub_nonpos_of_norm_sub_eq_infDist hK hy h⟩).symm

/-- **The projection inequality.** If `K` is a complete convex set in a real inner product
space and `u ∈ K`, then
`‖metricProj K x - u‖ ^ 2 + ‖x - metricProj K x‖ ^ 2 ≤ ‖x - u‖ ^ 2`. -/
theorem norm_metricProj_sub_sq_add_norm_sub_metricProj_sq_le (hc : IsComplete K)
    (hK : Convex ℝ K) (x : E) {u : E} (hu : u ∈ K) :
    ‖metricProj K x - u‖ ^ 2 + ‖x - metricProj K x‖ ^ 2 ≤ ‖x - u‖ ^ 2 := by
  have hvar := inner_sub_metricProj_sub_metricProj_nonpos hc hK x hu
  have hneg : ⟪x - metricProj K x, metricProj K x - u⟫ =
      -⟪x - metricProj K x, u - metricProj K x⟫ := by
    rw [← inner_neg_right, neg_sub]
  have hsplit : x - u = (x - metricProj K x) + (metricProj K x - u) := by abel
  rw [hsplit, norm_add_sq_real, hneg]
  linarith

/-- **Projecting onto a complete convex set does not increase the distance to its points.** If
`u ∈ K`, then `‖metricProj K x - u‖ ≤ ‖x - u‖`. -/
theorem norm_metricProj_sub_le (hc : IsComplete K) (hK : Convex ℝ K) (x : E) {u : E}
    (hu : u ∈ K) : ‖metricProj K x - u‖ ≤ ‖x - u‖ := by
  have h := norm_metricProj_sub_sq_add_norm_sub_metricProj_sq_le hc hK x hu
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  linarith [sq_nonneg ‖x - metricProj K x‖]

end InnerProductSpace

end TauCeti
