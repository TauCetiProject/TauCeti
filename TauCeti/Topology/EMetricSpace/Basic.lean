/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Topology.EMetricSpace.Basic

/-!
# Basic extended-metric inequalities

Elementary triangle-inequality bounds in weak extended pseudometric spaces:

* The polygon inequality `edist_le_Ico_sum_edist` of Mathlib bounds the distance between two terms
  of a sequence by the sum of the steps between them when the first index is the smaller. Here the
  two indices may come in either order, and the indices may be the ceilings of scaled times, as for
  the piecewise constant interpolant of a time discretization.
* Two points lying in open extended balls `Metric.eball p r₁` and `Metric.eball p r₂` about a
  common center `p` have extended distance strictly less than `r₁ + r₂` (and strictly less than
  `2 * r` when `r₁ = r₂ = r`).

## Main results

* `TauCeti.edist_le_Ico_min_max_sum_edist`: the distance between two terms of a sequence is at most
  the sum of the steps taken between them, whichever index is larger.
* `TauCeti.edist_ceil_div_le_Ico_sum_edist`: the same for the terms at the ceilings of `a / τ` and
  `b / τ`.
* `TauCeti.edist_lt_add_of_mem_eball`: two points in `Metric.eball p r₁` and `Metric.eball p r₂`
  lie at extended distance strictly less than `r₁ + r₂`.
* `TauCeti.edist_lt_two_mul_of_mem_eball`: any two points in `Metric.eball p r` lie at extended
  distance strictly less than `2 * r`.
-/

public section

open scoped ENNReal

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [WeakPseudoEMetricSpace X]

/-- **The polygon inequality for two indices in either order.** The distance between two terms of
a sequence is at most the sum of the steps taken between them. -/
theorem edist_le_Ico_min_max_sum_edist (f : ℕ → X) (m n : ℕ) :
    edist (f m) (f n) ≤ ∑ i ∈ Finset.Ico (min m n) (max m n), edist (f i) (f (i + 1)) := by
  rcases le_total m n with h | h
  · simpa [min_eq_left h, max_eq_right h] using edist_le_Ico_sum_edist f h
  · rw [edist_comm]
    simpa [min_eq_right h, max_eq_left h] using edist_le_Ico_sum_edist f h

/-- The distance between the terms of a sequence at the ceilings of `a / τ` and `b / τ` is at most
the sum of the steps taken between them. -/
theorem edist_ceil_div_le_Ico_sum_edist {K : Type*} [Semifield K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorSemiring K] {τ : K} (hτ : 0 ≤ τ) (U : ℕ → X) (a b : K) :
    edist (U ⌈a / τ⌉₊) (U ⌈b / τ⌉₊) ≤
      ∑ n ∈ Finset.Ico ⌈min a b / τ⌉₊ ⌈max a b / τ⌉₊, edist (U n) (U (n + 1)) := by
  have hmono : Monotone fun x : K ↦ ⌈x / τ⌉₊ := fun x y hxy ↦
    Nat.ceil_mono (div_le_div_of_nonneg_right hxy hτ)
  have hmin : ⌈min a b / τ⌉₊ = min ⌈a / τ⌉₊ ⌈b / τ⌉₊ := hmono.map_min
  have hmax : ⌈max a b / τ⌉₊ = max ⌈a / τ⌉₊ ⌈b / τ⌉₊ := hmono.map_max
  rw [hmin, hmax]
  exact edist_le_Ico_min_max_sum_edist U _ _

/-- Two points in open extended balls `Metric.eball p r₁` and `Metric.eball p r₂` about a common
center lie at extended distance strictly less than `r₁ + r₂`. -/
theorem edist_lt_add_of_mem_eball {p x y : X} {r₁ r₂ : ℝ≥0∞}
    (hx : x ∈ Metric.eball p r₁) (hy : y ∈ Metric.eball p r₂) :
    edist x y < r₁ + r₂ :=
  (edist_triangle_right x y p).trans_lt
    (ENNReal.add_lt_add (Metric.mem_eball.1 hx) (Metric.mem_eball.1 hy))

/-- Any two points of `Metric.eball p r` lie at extended distance strictly less than `2 * r`. -/
theorem edist_lt_two_mul_of_mem_eball {p x y : X} {r : ℝ≥0∞}
    (hx : x ∈ Metric.eball p r) (hy : y ∈ Metric.eball p r) :
    edist x y < 2 * r :=
  (edist_lt_add_of_mem_eball hx hy).trans_eq (two_mul r).symm

end TauCeti
