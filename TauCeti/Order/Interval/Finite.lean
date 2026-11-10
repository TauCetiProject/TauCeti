/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.Lattice

/-!
# Intervals avoiding a finite set of points

A finite family of points of a nonempty order without a maximal element misses a nonempty open
interval: along a strictly increasing sequence, each point lies in at most two of the intervals
from the sequence element of index `n` to that of index `n + 2`.

A finite set of points cuts every closed interval of a linear order into finitely many closed
pieces whose interiors avoid it. `TauCeti.Icc_induction_of_disjoint_Ioo` proves a two-endpoint
property of closed intervals by checking it on such pieces and gluing at shared endpoints.
-/

public section

open Set

namespace TauCeti

/-- There is a nonempty open interval avoiding a finite family of points in a nonempty preorder
without a maximal element. -/
theorem exists_Ioo_disjoint_range_of_finite {α ι : Type*} [Preorder α] [Nonempty α]
    [NoMaxOrder α] [Finite ι] (a : ι → α) :
    ∃ p q x : α, (∀ i, a i ∉ Ioo p q) ∧ x ∈ Ioo p q := by
  obtain ⟨f, hf⟩ := Nat.exists_strictMono α
  -- Each point lies in `Ioo (f n) (f (n + 2))` for at most two consecutive indices `n`.
  have hfin (i : ι) : {n : ℕ | a i ∈ Ioo (f n) (f (n + 2))}.Finite := by
    rcases {n : ℕ | a i ∈ Ioo (f n) (f (n + 2))}.eq_empty_or_nonempty with h | ⟨n₀, hn₀⟩
    · rw [h]
      exact Set.finite_empty
    refine (Set.finite_le_nat (n₀ + 1)).subset fun m hm => ?_
    by_contra hlt
    exact (hn₀.2.trans_le (hf.monotone (Nat.succ_le_of_lt (not_le.1 hlt)))).not_gt hm.1
  obtain ⟨n, hn⟩ := (Set.finite_iUnion hfin).exists_notMem
  simp only [Set.mem_iUnion, not_exists] at hn
  exact ⟨f n, f (n + 2), f (n + 1), hn, hf (Nat.lt_succ_self n), hf (Nat.lt_succ_self (n + 1))⟩

/-- **Induction over closed intervals cut by a finite set.** Let `Q c d` be a property of the
endpoints of closed intervals `[c, d]` contained in `s`. If `Q` holds on every such interval
whose interior avoids the finite set `p`, and `Q` is preserved by concatenation at a shared
endpoint inside `s`, then `Q` holds on every closed interval contained in `s`. -/
theorem Icc_induction_of_disjoint_Ioo {α : Type*} [LinearOrder α] {p : Finset α} {s : Set α}
    {Q : α → α → Prop}
    (hbase : ∀ c d : α, c ≤ d → Icc c d ⊆ s → Disjoint (↑p : Set α) (Ioo c d) → Q c d)
    (hglue : ∀ c m d : α, c ≤ m → m ≤ d → Icc c d ⊆ s → Q c m → Q m d → Q c d) {c d : α}
    (hcd : c ≤ d) (hs : Icc c d ⊆ s) : Q c d := by
  -- Induct on `p`: a new point `m` inside `(c, d)` splits `[c, d]` into `[c, m]` and `[m, d]`.
  induction p using Finset.induction_on generalizing c d with
  | empty => exact hbase c d hcd hs (by simp)
  | insert m p _ ih =>
    refine ih (fun c d hcd hs hdisj => ?_) hcd hs
    simp only [Finset.coe_insert, disjoint_insert_left] at hbase
    by_cases hm : m ∈ Ioo c d
    · exact hglue c m d hm.1.le hm.2.le hs
        (hbase c m hm.1.le ((Icc_subset_Icc_right hm.2.le).trans hs)
          ⟨by simp, hdisj.mono_right (Ioo_subset_Ioo_right hm.2.le)⟩)
        (hbase m d hm.2.le ((Icc_subset_Icc_left hm.1.le).trans hs)
          ⟨by simp, hdisj.mono_right (Ioo_subset_Ioo_left hm.1.le)⟩)
    · exact hbase c d hcd hs ⟨hm, hdisj⟩

end TauCeti
