/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval

/-!
# Intervals inside the cells of a finite subdivision

A family `s : Fin (N + 1) → α` of points in a linear order cuts out the cells
`[s i.castSucc, s i.succ]`, `i : Fin N`. If a nondegenerate interval `[c, d]` starts at or after
`s 0`, ends at or before `s (Fin.last N)`, and no point of the family lies strictly between `c`
and `d`, then `[c, d]` lies in a single cell. No monotonicity of `s` is needed. For a monotone
family from `a` to `b`, every point of the family lies in `[a, b]`.

## Main results

* `TauCeti.exists_Icc_subset_Icc_castSucc_succ`: an interval meeting no point of the family in
  its interior lies in a single cell;
* `Monotone.mem_uIcc_of_map_zero_of_map_last`: every point of a monotone subdivision from `a` to
  `b` lies in `uIcc a b`.
-/

public section

open Set

namespace TauCeti

/-- If `s 0 ≤ c < d ≤ s (Fin.last N)` and no point of the family `s` lies strictly between `c` and
`d`, then `[c, d]` lies in a single cell `[s i.castSucc, s i.succ]`. -/
theorem exists_Icc_subset_Icc_castSucc_succ {α : Type*} [LinearOrder α] {N : ℕ}
    {s : Fin (N + 1) → α} {c d : α} (h0 : s 0 ≤ c) (hcd : c < d) (hlast : d ≤ s (Fin.last N))
    (hdisj : ∀ i, s i ∉ Ioo c d) :
    ∃ i : Fin N, Icc c d ⊆ Icc (s i.castSucc) (s i.succ) := by
  -- The cell starts at the last point of the family at or below `c`.
  let S := Finset.univ.filter fun j : Fin (N + 1) ↦ s j ≤ c
  have hS : S.Nonempty := ⟨0, by simp [S, h0]⟩
  set j := S.max' hS
  have hj : s j ≤ c := (Finset.mem_filter.1 (S.max'_mem hS)).2
  have hjmax : ∀ k, s k ≤ c → k ≤ j := fun k hk ↦ S.le_max' k (by simp [S, hk])
  have hjlast : j ≠ Fin.last N := by
    intro h
    rw [h] at hj
    exact lt_irrefl d (hlast.trans_lt (hj.trans_lt hcd))
  have hci : c < s (j.castPred hjlast).succ := by
    by_contra! h
    have hlt : (j.castPred hjlast).castSucc < (j.castPred hjlast).succ := Fin.castSucc_lt_succ
    rw [Fin.castSucc_castPred] at hlt
    exact (hjmax _ h).not_gt hlt
  have hhi : d ≤ s (j.castPred hjlast).succ := by
    by_contra! h
    exact hdisj _ ⟨hci, h⟩
  refine ⟨j.castPred hjlast, fun t ht ↦ ⟨?_, ht.2.trans hhi⟩⟩
  rw [Fin.castSucc_castPred]
  exact hj.trans ht.1

/-- Every point of a monotone subdivision `s` from `a` to `b` lies in `[a, b]`. -/
theorem _root_.Monotone.mem_uIcc_of_map_zero_of_map_last {α : Type*} [LinearOrder α]
    {a b : α} {N : ℕ} {s : Fin (N + 1) → α} (hs : Monotone s) (ha : s 0 = a)
    (hb : s (Fin.last N) = b) (i : Fin (N + 1)) : s i ∈ uIcc a b := by
  have hab : a ≤ b := by rw [← ha, ← hb]; exact hs (Fin.zero_le _)
  rw [uIcc_of_le hab, ← ha, ← hb]
  exact ⟨hs (Fin.zero_le _), hs (Fin.le_last _)⟩

end TauCeti
