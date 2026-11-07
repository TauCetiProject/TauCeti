/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.Interval.Set.Basic

/-!
# Intervals inside the cells of a finite subdivision

A family `s : Fin (N + 1) → α` of points in a linear order cuts out the cells
`[s i.castSucc, s i.succ]`, `i : Fin N`. If a nondegenerate interval `[c, d]` starts at or after
`s 0`, ends at or before `s (Fin.last N)`, and no point of the family lies strictly between `c`
and `d`, then `[c, d]` lies in a single cell. No monotonicity of `s` is needed.

Points in `(τ 0, τ n]` likewise lie in one of the cells `(τ j, τ (j + 1)]`, `j < n`,
even when the sequence `τ` is not monotone.

## Main results

* `TauCeti.exists_lt_mem_Ioc_of_mem_Ioc`: a point between the first and last entries of a
  finite sequence lies in a successive half-open cell.
* `TauCeti.exists_Icc_subset_Icc_castSucc_succ`: an interval meeting no point of the family in
  its interior lies in a single cell.
-/

public section

open Set

namespace TauCeti

/-- A point in `(τ 0, τ n]` lies in a successive cell `(τ j, τ (j + 1)]` with `j < n`.
The sequence need not be monotone. -/
theorem exists_lt_mem_Ioc_of_mem_Ioc {α : Type*} [LinearOrder α] {τ : ℕ → α}
    {n : ℕ} {t : α} (ht : t ∈ Ioc (τ 0) (τ n)) :
    ∃ j < n, t ∈ Ioc (τ j) (τ (j + 1)) := by
  induction n with
  | zero => exact (ht.1.not_ge ht.2).elim
  | succ n ih =>
    by_cases htn : t ≤ τ n
    · obtain ⟨j, hj, htj⟩ := ih ⟨ht.1, htn⟩
      exact ⟨j, hj.trans (Nat.lt_succ_self n), htj⟩
    · exact ⟨n, Nat.lt_succ_self n, lt_of_not_ge htn, ht.2⟩

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

end TauCeti
