/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.Order
public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Intervals avoiding a finite set of points

A finite family of real points is bounded above, so an open interval beyond it contains a point.

A finite set of points cuts every closed interval of a linear order into finitely many closed
pieces whose interiors avoid it. `TauCeti.Icc_induction_of_disjoint_Ioo` proves a two-endpoint
property of closed intervals by checking it on such pieces and gluing at shared endpoints.
-/

public section

open Set

namespace TauCeti

/-- There is a nonempty open real interval avoiding a finite family of real points. -/
theorem exists_Ioo_disjoint_range_of_finite {ι : Type*} [Finite ι] (a : ι → ℝ) :
    ∃ p q x : ℝ, (∀ i, a i ∉ Ioo p q) ∧ x ∈ Ioo p q := by
  obtain ⟨S, hbound⟩ := Finite.exists_le a
  let p := S + 1
  let x := p + 1
  let q := p + 2
  have ha : ∀ i, a i ∉ Ioo p q := by
    intro i hi
    have := hbound i
    dsimp [p] at hi
    exact (not_lt.mpr (by linarith : a i ≤ S + 1)) hi.1
  have hx : x ∈ Ioo p q := by dsimp [x, q]; constructor <;> linarith
  exact ⟨p, q, x, ha, hx⟩

/-- **Induction over closed intervals cut by a finite set.** Let `Q c d` be a property of the
endpoints of closed intervals `[c, d]` contained in `s`. If `Q` holds on every such interval
whose interior avoids the finite set `p`, and `Q` is preserved by concatenation at a shared
endpoint, then `Q` holds on every closed interval contained in `s`. -/
theorem Icc_induction_of_disjoint_Ioo {α : Type*} [LinearOrder α] {p : Finset α} {s : Set α}
    {Q : α → α → Prop}
    (hbase : ∀ c d : α, c ≤ d → Icc c d ⊆ s → Disjoint (↑p : Set α) (Ioo c d) → Q c d)
    (hglue : ∀ c m d : α, c ≤ m → m ≤ d → Q c m → Q m d → Q c d) {c d : α} (hcd : c ≤ d)
    (hs : Icc c d ⊆ s) : Q c d := by
  have hdisj : ∀ {c d : α}, p.filter (· ∈ Ioo c d) = ∅ → Disjoint (↑p : Set α) (Ioo c d) :=
    fun he => disjoint_left.mpr fun _ hxp hx => Finset.filter_eq_empty_iff.mp he hxp hx
  -- Strong induction on the number of points of `p` strictly inside `[c, d]`.
  suffices h : ∀ n, ∀ c d : α, (p.filter (· ∈ Ioo c d)).card ≤ n → c ≤ d → Icc c d ⊆ s →
      Q c d from h _ c d le_rfl hcd hs
  intro n
  induction n with
  | zero =>
    intro c d hcard hcd hs
    exact hbase c d hcd hs (hdisj (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)))
  | succ n ih =>
    intro c d hcard hcd hs
    rcases (p.filter (· ∈ Ioo c d)).eq_empty_or_nonempty with he | hne
    · exact hbase c d hcd hs (hdisj he)
    -- Split off the largest point of `p` inside `[c, d]`.
    set m := (p.filter (· ∈ Ioo c d)).max' hne
    obtain ⟨hmp, hm⟩ := Finset.mem_filter.mp ((p.filter (· ∈ Ioo c d)).max'_mem hne)
    have hssub : p.filter (· ∈ Ioo c m) ⊂ p.filter (· ∈ Ioo c d) :=
      (Finset.ssubset_iff_of_subset (Finset.monotone_filter_right _ fun x _ hx =>
          ⟨hx.1, hx.2.trans hm.2⟩)).mpr
        ⟨m, Finset.mem_filter.mpr ⟨hmp, hm⟩, fun hmem =>
          (Finset.mem_filter.mp hmem).2.2.false⟩
    have h₁ : Q c m :=
      ih c m (Nat.le_of_lt_succ ((Finset.card_lt_card hssub).trans_le hcard)) hm.1.le
        ((Icc_subset_Icc le_rfl hm.2.le).trans hs)
    have h₂ : Q m d :=
      hbase m d hm.2.le ((Icc_subset_Icc hm.1.le le_rfl).trans hs) <|
        disjoint_left.mpr fun x hxp hx => ((p.filter (· ∈ Ioo c d)).le_max' x
          (Finset.mem_filter.mpr ⟨hxp, hm.1.trans hx.1, hx.2⟩)).not_gt hx.1
    exact hglue c m d hm.1.le hm.2.le h₁ h₂

end TauCeti
