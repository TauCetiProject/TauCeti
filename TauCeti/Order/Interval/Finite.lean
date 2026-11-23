/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finset.Sort

/-!
# Intervals avoiding a finite set of points

A finite family of points of a nonempty preorder without a maximal element misses a nonempty open
interval.

A finite set of points cuts every closed interval of a linear order into finitely many closed
pieces whose interiors avoid it. `TauCeti.Icc_induction_of_disjoint_Ioo` proves a two-endpoint
property of closed intervals by checking it on such pieces and gluing at shared endpoints.

Between two points `a₀ < a₁` of a finite set `C` in a linear order, the points of `C ∩ [a₀, a₁]`
can be listed in increasing order `a₀ = d 0 < ⋯ < d (m + 1) = a₁`, with no point of `C` between
two consecutive ones (`Set.Finite.exists_strictMono_fin_consecutive`). In a densely ordered linear
order there is also a finite version with exactly one point of `C` in each band: points
`b 0 < ⋯ < b m` chosen strictly between consecutive points of `C ∩ [a₀, a₁]` avoid `C`, and
`[a₀, b 0]`, each `[b i, b (i + 1)]` and `[b m, a₁]` contain exactly one point of `C`
(`Set.Finite.exists_strictMono_notMem_inter_Icc_eq_singleton`).
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

/-- **Listing the points of a finite set between two of its points.** Let `C` be a finite subset
of a linear order and let `a₀ < a₁` be two of its points. The points of `C` in `[a₀, a₁]` can
be listed in increasing order `a₀ = d 0 < d 1 < ⋯ < d (m + 1) = a₁`, and no point of `C` lies
strictly between two consecutive ones. -/
theorem Set.Finite.exists_strictMono_fin_consecutive {α : Type*} [LinearOrder α] {C : Set α}
    (hC : C.Finite) {a₀ a₁ : α} (h₀ : a₀ ∈ C) (h₁ : a₁ ∈ C) (h : a₀ < a₁) :
    ∃ m : ℕ, ∃ d : Fin (m + 2) → α, StrictMono d ∧ (∀ j, d j ∈ C) ∧ d 0 = a₀ ∧
      d (Fin.last (m + 1)) = a₁ ∧
      ∀ (i : Fin (m + 1)) {x : α}, x ∈ C → d i.castSucc < x → x < d i.succ → False := by
  set s := (hC.inter_of_left (Icc a₀ a₁)).toFinset with hs
  have hmem {x : α} : x ∈ s ↔ x ∈ C ∧ x ∈ Icc a₀ a₁ := by simp [hs]
  have hcard : 2 ≤ s.card := by
    have hsub : ({a₀, a₁} : Finset α) ⊆ s := by
      intro x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hmem.2 ⟨h₀, le_rfl, h.le⟩
      · rw [Finset.mem_singleton.1 hx]
        exact hmem.2 ⟨h₁, h.le, le_rfl⟩
    simpa [Finset.card_pair h.ne] using Finset.card_le_card hsub
  obtain ⟨m, hm⟩ : ∃ m, s.card = m + 2 := ⟨s.card - 2, by omega⟩
  set d := s.orderEmbOfFin hm
  have hdI (j : Fin (m + 2)) : d j ∈ Icc a₀ a₁ := (hmem.1 (s.orderEmbOfFin_mem hm j)).2
  -- Every point of `C` in `[a₀, a₁]` is some `d j`.
  have hd {x : α} (hx : x ∈ C) (hxI : x ∈ Icc a₀ a₁) : ∃ j, d j = x := by
    have hx' : x ∈ Set.range d := by
      rw [Finset.range_orderEmbOfFin]
      exact Finset.mem_coe.2 (hmem.2 ⟨hx, hxI⟩)
    exact Set.mem_range.1 hx'
  refine ⟨m, d, d.strictMono, fun j ↦ (hmem.1 (s.orderEmbOfFin_mem hm j)).1, ?_, ?_,
    fun i x hx hx₁ hx₂ ↦ ?_⟩
  · obtain ⟨j, hj⟩ := hd h₀ ⟨le_rfl, h.le⟩
    exact le_antisymm (hj ▸ d.monotone (Fin.zero_le j)) (hdI 0).1
  · obtain ⟨j, hj⟩ := hd h₁ ⟨h.le, le_rfl⟩
    exact le_antisymm (hdI _).2 (hj ▸ d.monotone (Fin.le_last j))
  · obtain ⟨j, rfl⟩ := hd hx ⟨(hdI _).1.trans hx₁.le, hx₂.le.trans (hdI _).2⟩
    have h₁ := d.lt_iff_lt.1 hx₁
    have h₂ := d.lt_iff_lt.1 hx₂
    rw [Fin.lt_def, Fin.val_castSucc] at h₁
    rw [Fin.lt_def, Fin.val_succ] at h₂
    omega

/-- **Finitely many points separating a finite set between two of its points.** Let `C` be a
finite subset of a densely ordered linear order and let `a₀ < a₁` be two of its points. There are
strictly increasing points `b 0 < ⋯ < b m` in `(a₀, a₁)`, none of them in `C`, such that `a₀`
is the only point of `C` in `[a₀, b 0]`, `a₁` is the only point of `C` in `[b m, a₁]`, and each
`[b i, b (i + 1)]` contains exactly one point of `C`. -/
theorem Set.Finite.exists_strictMono_notMem_inter_Icc_eq_singleton {α : Type*} [LinearOrder α]
    [DenselyOrdered α] {C : Set α} (hC : C.Finite) {a₀ a₁ : α} (h₀ : a₀ ∈ C) (h₁ : a₁ ∈ C)
    (h : a₀ < a₁) :
    ∃ m : ℕ, ∃ b : Fin (m + 1) → α, StrictMono b ∧ (∀ i, b i ∉ C) ∧ a₀ < b 0 ∧
      b (Fin.last m) < a₁ ∧ C ∩ Icc a₀ (b 0) = {a₀} ∧ C ∩ Icc (b (Fin.last m)) a₁ = {a₁} ∧
      ∀ i : Fin m, ∃ c, C ∩ Icc (b i.castSucc) (b i.succ) = {c} := by
  -- The points of `C` in `[a₀, a₁]`, in increasing order `a₀ = d 0 < d 1 < ⋯ < d (m + 1) = a₁`.
  obtain ⟨m, d, hdm, hdC, hd0, hdl, hgap⟩ := hC.exists_strictMono_fin_consecutive h₀ h₁ h
  -- `b i` lies strictly between `d i` and `d (i + 1)`.
  choose b hbl hbu using fun i : Fin (m + 1) ↦ exists_between (hdm (Fin.castSucc_lt_succ (i := i)))
  have hb0 : a₀ < b 0 := by simpa [hd0] using hbl 0
  have hbm : b (Fin.last m) < a₁ := by simpa [hdl] using hbu (Fin.last m)
  -- `d (i + 1)` lies strictly between `b i` and `b (i + 1)`.
  have hbd (i : Fin m) : b i.castSucc < d i.succ.castSucc ∧ d i.succ.castSucc < b i.succ :=
    ⟨Fin.succ_castSucc i ▸ hbu i.castSucc, hbl i.succ⟩
  refine ⟨m, b, Fin.strictMono_iff_lt_succ.2 fun i ↦ ?_, fun i hi ↦ hgap i hi (hbl i) (hbu i),
    hb0, hbm, ?_, ?_, fun i ↦ ?_⟩
  · exact (hbd i).1.trans (hbd i).2
  · refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨h₀, le_rfl, hb0.le⟩, fun x ⟨hx, hx₁, hx₂⟩ ↦ ?_⟩
    by_contra hne
    exact hgap 0 hx (by simpa [hd0] using lt_of_le_of_ne hx₁ (Ne.symm hne))
      (hx₂.trans_lt (hbu 0))
  · refine Set.eq_singleton_iff_unique_mem.2 ⟨⟨h₁, hbm.le, le_rfl⟩, fun x ⟨hx, hx₁, hx₂⟩ ↦ ?_⟩
    by_contra hne
    exact hgap (Fin.last m) hx ((hbl _).trans_le hx₁)
      (by simpa [hdl] using lt_of_le_of_ne hx₂ hne)
  · -- The only point of `C` in `[b i, b (i + 1)]` is `d (i + 1)`.
    refine ⟨d i.succ.castSucc, Set.eq_singleton_iff_unique_mem.2
      ⟨⟨hdC _, (hbd i).1.le, (hbd i).2.le⟩, fun x ⟨hx, hx₁, hx₂⟩ ↦ ?_⟩⟩
    rcases lt_trichotomy x (d i.succ.castSucc) with hlt' | heq | hgt
    · exact (hgap i.castSucc hx ((hbl _).trans_le hx₁)
        (by rw [Fin.succ_castSucc]; exact hlt')).elim
    · exact heq
    · exact (hgap i.succ hx hgt (hx₂.trans_lt (hbu _))).elim
