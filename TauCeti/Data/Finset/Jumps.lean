/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Abel

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
  by_cases h : ∃ y ∈ S, r < y
  · obtain ⟨y, _, hry, hy⟩ := S.exists_next_right h
    obtain ⟨c, hrc, hcyb⟩ := exists_between (lt_min hry hrb)
    exact ⟨c, hrc, hcyb.trans_le (min_le_right _ _),
      fun x hx hrx => (hcyb.trans_le (min_le_left _ _)).trans_le (hy x hx hrx)⟩
  · obtain ⟨c, hrc, hcb⟩ := exists_between hrb
    exact ⟨c, hrc, hcb, fun x hx hrx => (h ⟨x, hx, hrx⟩).elim⟩

/-- Choose a point to the left of an event, after all earlier events and a given bound. -/
theorem exists_left_gap (S : Finset R) {a r : R} (har : a < r) :
    ∃ c, a < c ∧ c < r ∧ ∀ x ∈ S, x < r → x < c := by
  obtain ⟨c, hcr, hac, hc⟩ := exists_right_gap (R := OrderDual R) S (r := r) (b := a) har
  exact ⟨c, hac, hcr, hc⟩

omit [DenselyOrdered R] in
/-- If an event `r` is isolated on `[a, c]`, then the events strictly between `a` and a larger `b`
split into `r` and the events strictly between `c` and `b`. -/
theorem filter_lt_lt_eq_insert (S : Finset R) {a b c r : R} (hrS : r ∈ S) (har : a < r)
    (hrc : r < c) (hcb : c < b) (hsingle : ∀ x ∈ S, x ∈ Icc a c → x = r) :
    S.filter (fun x => a < x ∧ x < b) = insert r (S.filter (fun x => c < x ∧ x < b)) := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hxS, hax, hxb⟩
    by_cases hxr : x = r
    · exact Or.inl hxr
    · refine Or.inr ⟨hxS, ?_, hxb⟩
      by_contra! hxc
      exact hxr (hsingle x hxS ⟨hax.le, hxc⟩)
  · rintro (rfl | ⟨hxS, hcx, hxb⟩)
    · exact ⟨hrS, har, hrc.trans hcb⟩
    · exact ⟨hxS, har.trans (hrc.trans hcx), hxb⟩

/-- The first event strictly inside `(a, b)` is isolated on `[a, c]` for some `c < b` outside `S`,
provided `a ∉ S`. -/
theorem exists_first_event (S : Finset R) {a b : R} (ha : a ∉ S)
    (hT : (S.filter (fun x => a < x ∧ x < b)).Nonempty) :
    ∃ r c, r ∈ S ∧ a < r ∧ r < c ∧ c < b ∧ c ∉ S ∧ ∀ x ∈ S, x ∈ Icc a c → x = r := by
  set T := S.filter (fun x => a < x ∧ x < b)
  have hrT : T.min' hT ∈ T := Finset.min'_mem T hT
  obtain ⟨hrS, har, hrb⟩ := Finset.mem_filter.mp hrT
  obtain ⟨c, hrc, hcb, hc⟩ := exists_right_gap S hrb
  refine ⟨T.min' hT, c, hrS, har, hrc, hcb, fun hcS => (hc c hcS hrc).false, ?_⟩
  intro x hx haxc
  have hax : a < x := haxc.1.lt_of_ne (by rintro rfl; exact ha hx)
  have hxT : x ∈ T := Finset.mem_filter.mpr ⟨hx, hax, haxc.2.trans_lt hcb⟩
  have hrx : T.min' hT ≤ x := Finset.min'_le T x hxT
  by_contra hne
  exact (hc x hx (hrx.lt_of_ne (Ne.symm hne))).not_ge haxc.2

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
  -- Induct on the number of events inside the interval. Isolate the first event,
  -- account for its jump, and apply the induction hypothesis to the remaining interval.
  have aux (a b : R) (haa : a₀ ≤ a) (hbb : b ≤ b₀)
      (hab : a < b) (ha : a ∉ S) (hb : b ∉ S) :
      V a - V b = ∑ x ∈ S.filter (fun x => a < x ∧ x < b), w x := by
    induction hn : (S.filter (fun x => a < x ∧ x < b)).card using Nat.strong_induction_on
        generalizing a b with
    | ind n ih =>
      by_cases hT : (S.filter (fun x => a < x ∧ x < b)).Nonempty
      · obtain ⟨r, c, hrS, har, hrc, hcb, hcS, hsingle⟩ := exists_first_event S ha hT
        have hrU : r ∉ S.filter (fun x => c < x ∧ x < b) := by
          simp only [Finset.mem_filter]
          exact fun h => h.2.1.not_gt hrc
        have hTU := filter_lt_lt_eq_insert S hrS har hrc hcb hsingle
        have hcard : (S.filter (fun x => c < x ∧ x < b)).card < n := by
          rw [← hn, hTU, Finset.card_insert_of_notMem hrU]
          omega
        have hlocal := hjump a r c haa (hcb.le.trans hbb) har hrc hrS hsingle
        have hrest : V c - V b = ∑ x ∈ S.filter (fun x => c < x ∧ x < b), w x :=
          ih _ hcard c b (haa.trans (har.trans hrc).le) hbb hcb hcS hb rfl
        rw [hTU, Finset.sum_insert hrU]
        calc
          V a - V b = (V a - V c) + (V c - V b) := by abel
          _ = w r + ∑ x ∈ S.filter (fun x => c < x ∧ x < b), w x := by rw [hlocal, hrest]
      · have hT0 := Finset.not_nonempty_iff_eq_empty.mp hT
        have hno : ∀ x ∈ S, x ∉ Icc a b := by
          intro x hx hxab
          have hax : a < x := hxab.1.lt_of_ne (by rintro rfl; exact ha hx)
          have hxb : x < b := hxab.2.lt_of_ne (by rintro rfl; exact hb hx)
          have : x ∈ S.filter (fun x => a < x ∧ x < b) := Finset.mem_filter.mpr ⟨hx, hax, hxb⟩
          simp [hT0] at this
        simp [hT0, hconst a b haa hbb hab hno]
  exact aux a₀ b₀ le_rfl le_rfl hab ha hb

end Finset
