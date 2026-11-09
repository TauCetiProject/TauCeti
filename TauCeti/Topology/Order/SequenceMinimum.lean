/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Basic
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Attainment of a sequence minimum from a lower barrier

A sequence bounded below by a sequence converging to `c` attains its minimum if it
has values at most `c` arbitrarily far out. This allows a converging lower barrier
to certify attainment without requiring convergence of the sequence itself.
-/

public section

open Filter Set
open scoped Topology

namespace Filter.Tendsto

/-- A sequence above a convergent lower barrier attains its minimum, with value at
most the barrier's limit, provided it has values at most that limit frequently. -/
theorem exists_minimum_of_lower_bound {α : Type*} [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α] {a b : ℕ → α} {c : α}
    (hb : Tendsto b atTop (𝓝 c)) (hba : ∀ n, b n ≤ a n)
    (ha : ∃ᶠ n in atTop, a n ≤ c) :
    ∃ n, a n ≤ c ∧ ∀ m, a n ≤ a m := by
  classical
  by_cases h : ∀ n, c ≤ a n
  · obtain ⟨n, hn⟩ := ha.exists
    exact ⟨n, hn, fun m => hn.trans (h m)⟩
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have htail : ∀ᶠ n in atTop, a i < a n :=
      (hb.eventually (eventually_gt_nhds hi)).mono fun n hn => hn.trans_le (hba n)
    obtain ⟨N, hN⟩ := eventually_atTop.1 htail
    obtain ⟨k, _, hmin⟩ := Set.exists_min_image (Set.Iic (max N i)) a (Set.finite_Iic _)
      ⟨i, le_max_right N i⟩
    refine ⟨k, (hmin i (le_max_right N i)).trans hi.le, fun m => ?_⟩
    by_cases hm : m ≤ max N i
    · exact hmin m hm
    · exact (hmin i (le_max_right N i)).trans (hN m (by omega)).le

end Filter.Tendsto
