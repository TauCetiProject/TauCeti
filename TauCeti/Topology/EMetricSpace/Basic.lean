/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Topology.EMetricSpace.Basic

/-!
# The polygon inequality in either index order

The polygon inequality `edist_le_Ico_sum_edist` of Mathlib bounds the distance between two terms of
a sequence by the sum of the steps between them when the first index is the smaller. Here the
two indices may come in either order, and the indices may be the ceilings of scaled times, as for
the piecewise constant interpolant of a time discretization.

## Main results

* `TauCeti.edist_le_sum_Ico_min_max_edist`: the distance between two terms of a sequence is at most
  the sum of the steps taken between them, whichever index is larger.
* `TauCeti.edist_ceil_div_le_sum_Ico_edist`: the same for the terms at the ceilings of `a / τ` and
  `b / τ`.
-/

public section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [WeakPseudoEMetricSpace X]

/-- **The polygon inequality for two indices in either order.** The distance between two terms of
a sequence is at most the sum of the steps taken between them. -/
theorem edist_le_sum_Ico_min_max_edist (f : ℕ → X) (m n : ℕ) :
    edist (f m) (f n) ≤ ∑ i ∈ Finset.Ico (min m n) (max m n), edist (f i) (f (i + 1)) := by
  rcases le_total m n with h | h
  · simpa [min_eq_left h, max_eq_right h] using edist_le_Ico_sum_edist f h
  · rw [edist_comm]
    simpa [min_eq_right h, max_eq_left h] using edist_le_Ico_sum_edist f h

/-- The distance between the terms of a sequence at the ceilings of `a / τ` and `b / τ` is at most
the sum of the steps taken between them. -/
theorem edist_ceil_div_le_sum_Ico_edist {K : Type*} [Semifield K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorSemiring K] {τ : K} (hτ : 0 ≤ τ) (U : ℕ → X) (a b : K) :
    edist (U ⌈a / τ⌉₊) (U ⌈b / τ⌉₊) ≤
      ∑ n ∈ Finset.Ico ⌈min a b / τ⌉₊ ⌈max a b / τ⌉₊, edist (U n) (U (n + 1)) := by
  have hmono : Monotone fun x : K ↦ ⌈x / τ⌉₊ := fun x y hxy ↦
    Nat.ceil_mono (div_le_div_of_nonneg_right hxy hτ)
  have hmin : ⌈min a b / τ⌉₊ = min ⌈a / τ⌉₊ ⌈b / τ⌉₊ := hmono.map_min
  have hmax : ⌈max a b / τ⌉₊ = max ⌈a / τ⌉₊ ⌈b / τ⌉₊ := hmono.map_max
  rw [hmin, hmax]
  exact edist_le_sum_Ico_min_max_edist U _ _

end TauCeti
