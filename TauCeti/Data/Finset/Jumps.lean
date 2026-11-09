/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.DenselyOrdered
import Mathlib.Tactic.ByContra

/-! # Summing finitely many jumps on an ordered interval

A function into an additive commutative group, constant between finitely many events, has total
change equal to the sum of its local changes. This is the finite telescoping
step in the signed Sturm theorem; it uses no topology or completeness.
-/

public section

namespace Finset

open Set

variable {R : Type*} [LinearOrder R] [DenselyOrdered R]

/-- Choose a point to the right of an event, before all later events and a given bound. -/
theorem exists_right_gap (S : Finset R) {r b : R} (hrb : r < b) :
    ∃ c, r < c ∧ c < b ∧ ∀ x ∈ S, r < x → c < x := by
  classical
  obtain ⟨c, hrc, hc⟩ := Finset.exists_between (s := {r}) (t := insert b (S.filter (r < ·)))
    (singleton_nonempty r) (insert_nonempty _ _) (by simp +contextual [hrb])
  exact ⟨c, hrc r (mem_singleton_self r), hc b (mem_insert_self _ _),
    fun x hx hrx => hc x (mem_insert_of_mem (mem_filter.2 ⟨hx, hrx⟩))⟩

/-- Choose a point to the left of an event, after all earlier events and a given bound. -/
theorem exists_left_gap (S : Finset R) {a r : R} (har : a < r) :
    ∃ c, a < c ∧ c < r ∧ ∀ x ∈ S, x < r → x < c := by
  obtain ⟨c, hcr, hac, hc⟩ := exists_right_gap (R := OrderDual R) S (r := r) (b := a) har
  exact ⟨c, hac, hcr, hc⟩

omit [DenselyOrdered R] in
/-- If an event `r` is the only event in `(a, c]`, then the events strictly between `a` and a
larger `b` split into `r` and the events strictly between `c` and `b`. -/
theorem filter_lt_lt_eq_insert (S : Finset R) {a b c r : R} (hrS : r ∈ S) (har : a < r)
    (hrc : r ≤ c) (hcb : c < b) (hsingle : ∀ x ∈ S, x ∈ Ioc a c → x = r) :
    S.filter (fun x => a < x ∧ x < b) = insert r (S.filter (fun x => c < x ∧ x < b)) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hxS, hax, hxb⟩
    by_cases hxr : x = r
    · exact Or.inl hxr
    · refine Or.inr ⟨hxS, ?_, hxb⟩
      by_contra! hxc
      exact hxr (hsingle x hxS ⟨hax, hxc⟩)
  · rintro (rfl | ⟨hxS, hcx, hxb⟩)
    · exact ⟨hrS, har, hrc.trans_lt hcb⟩
    · exact ⟨hxS, (har.trans_le hrc).trans hcx, hxb⟩

/-- The first event strictly inside `(a, b)` is isolated on `[a, c]` for some `c < b` outside `S`,
provided `a ∉ S`. -/
theorem exists_first_event (S : Finset R) {a b : R} (ha : a ∉ S)
    (hT : (S.filter (fun x => a < x ∧ x < b)).Nonempty) :
    ∃ r c, r ∈ S ∧ a < r ∧ r < c ∧ c < b ∧ c ∉ S ∧ ∀ x ∈ S, x ∈ Icc a c → x = r := by
  set T := S.filter (fun x => a < x ∧ x < b)
  obtain ⟨hrS, har, hrb⟩ := Finset.mem_filter.mp (T.min'_mem hT)
  obtain ⟨c, hrc, hcb, hc⟩ := exists_right_gap S hrb
  refine ⟨T.min' hT, c, hrS, har, hrc, hcb, fun hcS => (hc c hcS hrc).false,
    fun x hx haxc => le_antisymm (le_of_not_gt fun h => (hc x hx h).not_ge haxc.2) ?_⟩
  have hax : a < x := haxc.1.lt_of_ne (by rintro rfl; exact ha hx)
  exact T.min'_le x (Finset.mem_filter.mpr ⟨hx, hax, haxc.2.trans_lt hcb⟩)

/-- Local changes at isolated events sum to the total change between two
points outside the event set. -/
theorem sum_jumps {G : Type*} [AddCommGroup G] (S : Finset R) (V w : R → G)
    {a₀ b₀ : R}
    (hconst : ∀ a b, a₀ ≤ a → b ≤ b₀ → a < b → (∀ x ∈ S, x ∉ Icc a b) → V a = V b)
    (hjump : ∀ a r b, a₀ ≤ a → b ≤ b₀ → a < r → r < b → r ∈ S →
      (∀ x ∈ S, x ∈ Icc a b → x = r) → V a - V b = w r)
    (hab : a₀ < b₀) (ha : a₀ ∉ S) (hb : b₀ ∉ S) :
    V a₀ - V b₀ = ∑ x ∈ S.filter (fun x => a₀ < x ∧ x < b₀), w x := by
  classical
  -- Induct on the number of events in `(a, b₀)`: move the left endpoint `a` past the first
  -- event, account for its jump, and apply the induction hypothesis to the remaining interval.
  have aux (a : R) (haa : a₀ ≤ a) (hab : a < b₀) (ha : a ∉ S) :
      V a - V b₀ = ∑ x ∈ S.filter (fun x => a < x ∧ x < b₀), w x := by
    induction hn : (S.filter (fun x => a < x ∧ x < b₀)).card using Nat.strong_induction_on
        generalizing a with
    | ind n ih =>
      by_cases hT : (S.filter (fun x => a < x ∧ x < b₀)).Nonempty
      · obtain ⟨r, c, hrS, har, hrc, hcb, hcS, hsingle⟩ := exists_first_event S ha hT
        have hrU : r ∉ S.filter (fun x => c < x ∧ x < b₀) :=
          fun h => (Finset.mem_filter.mp h).2.1.not_gt hrc
        have hTU := filter_lt_lt_eq_insert S hrS har hrc.le hcb
          fun x hx hxc => hsingle x hx (Ioc_subset_Icc_self hxc)
        have hcard : (S.filter (fun x => c < x ∧ x < b₀)).card < n := by
          rw [← hn, hTU, Finset.card_insert_of_notMem hrU]
          omega
        rw [hTU, Finset.sum_insert hrU, ← hjump a r c haa hcb.le har hrc hrS hsingle,
          ← ih _ hcard c (haa.trans (har.trans hrc).le) hcb hcS rfl, sub_add_sub_cancel]
      · have hno : ∀ x ∈ S, x ∉ Icc a b₀ := fun x hx hxab =>
          hT ⟨x, Finset.mem_filter.mpr ⟨hx, hxab.1.lt_of_ne (by rintro rfl; exact ha hx),
            hxab.2.lt_of_ne (by rintro rfl; exact hb hx)⟩⟩
        rw [Finset.not_nonempty_iff_eq_empty.mp hT, Finset.sum_empty,
          hconst a b₀ haa le_rfl hab hno, sub_self]
  exact aux a₀ le_rfl hab ha

end Finset
