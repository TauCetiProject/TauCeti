/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Prod
public import TauCeti.Order.Dilworth.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Split-graph strict-order matchings and Dilworth duality

A strict-order matching on a finite set `s` (`Finset.IsOrderMatching`) is a finite set of strictly
increasing pairs in `s × s` whose left and right projections are injective, modeling matchings in
the split bipartite graph of an order. Its maximum cardinality is `Finset.orderMatchingNumber`.

Every nonempty finite `<`-chain admits a strict-order matching of size `c.card - 1`
(`IsChain.exists_isOrderMatching_card_add_one`), so pairwise-disjoint partitions into nonempty
`<`-chains convert to strict-order matchings with `E.card + C.card = s.card`
(`Finset.exists_isOrderMatching_of_chainPartition`). Conversely, in a strict partial order, every
strict-order matching `E` induces a partition of `s` into `s.card - E.card` nonempty `<`-chains
(`Finset.IsOrderMatching.exists_chainPartition`). Combined with Dilworth's theorem, this yields the
split-graph matching duality `s.orderMatchingNumber + s.antichainWidth = s.card` on any finite
subset `s` of a partial order (`Finset.orderMatchingNumber_add_antichainWidth`).

## Main definitions

* `Finset.IsOrderMatching`: predicate for a finite set of strictly increasing pairs in `s × s`
  whose first and second projections are injective.
* `Finset.orderMatchingNumber`: the maximum number of edges in a strict-order matching on `s`.

## Main results

* `IsChain.exists_isOrderMatching_card_add_one`: every nonempty finite `<`-chain admits a
  strict-order matching of size `c.card - 1`.
* `Finset.exists_isOrderMatching_of_chainPartition` and
  `Finset.IsOrderMatching.exists_chainPartition`: conversion between pairwise-disjoint chain
  partitions and strict-order matchings with `E.card + C.card = s.card`.
* `Finset.IsOrderMatching.card_add_card_le_of_isAntichain`: weak duality between strict-order
  matchings and strict antichains.
* `Finset.orderMatchingNumber_add_antichainWidth`: in a partial order,
  `s.orderMatchingNumber + s.antichainWidth = s.card`.

## References

* M. X. Goemans, *18.997 Topics in Combinatorial Optimization, Lecture 6* (MIT, 2004),
  Theorem 3 and split-poset matching duality.
-/

public section

section OrderMatching

namespace Finset

section Basic

variable {α : Type*} [LT α]

/-- A strict-order matching on `s` is a finite set of strictly increasing pairs in `s × s` whose
first and second projections are injective. In the split bipartite graph of `s`, each element
appears at most once on the left and at most once on the right. -/
def IsOrderMatching (s : Finset α) (E : Finset (α × α)) : Prop :=
  (∀ e ∈ E, e.1 ∈ s ∧ e.2 ∈ s ∧ e.1 < e.2) ∧
    (E : Set (α × α)).InjOn Prod.fst ∧
    (E : Set (α × α)).InjOn Prod.snd

/-- Explicit characterization of a strict-order matching on `s`. -/
theorem isOrderMatching_iff {s : Finset α} {E : Finset (α × α)} :
    s.IsOrderMatching E ↔
      (∀ e ∈ E, e.1 ∈ s ∧ e.2 ∈ s ∧ e.1 < e.2) ∧
      (∀ e ∈ E, ∀ f ∈ E, e.1 = f.1 → e = f) ∧
      (∀ e ∈ E, ∀ f ∈ E, e.2 = f.2 → e = f) :=
  Iff.rfl

@[simp]
theorem isOrderMatching_empty (s : Finset α) : s.IsOrderMatching ∅ := by
  simp [IsOrderMatching]

@[simp]
theorem isOrderMatching_singleton_iff {s : Finset α} {a b : α} :
    s.IsOrderMatching {(a, b)} ↔ a ∈ s ∧ b ∈ s ∧ a < b := by
  simp [isOrderMatching_iff]

/-- Any subset of a strict-order matching is a strict-order matching. -/
theorem IsOrderMatching.subset {s : Finset α} {E E' : Finset (α × α)}
    (hE : s.IsOrderMatching E) (h : E' ⊆ E) : s.IsOrderMatching E' :=
  ⟨fun e he ↦ hE.1 e (h he), hE.2.1.mono (coe_subset.mpr h), hE.2.2.mono (coe_subset.mpr h)⟩

/-- A strict-order matching on `s` remains a strict-order matching on any superset of `s`. -/
theorem IsOrderMatching.mono {s t : Finset α} {E : Finset (α × α)}
    (hE : s.IsOrderMatching E) (h : s ⊆ t) : t.IsOrderMatching E :=
  ⟨fun e he ↦ ⟨h (hE.1 e he).1, h (hE.1 e he).2.1, (hE.1 e he).2.2⟩, hE.2.1, hE.2.2⟩

/-- Every edge of a strict-order matching on `s` lies in `s ×ˢ s`. -/
theorem IsOrderMatching.subset_product {s : Finset α} {E : Finset (α × α)}
    (hE : s.IsOrderMatching E) : E ⊆ s ×ˢ s := fun e he ↦
  mem_product.mpr ⟨(hE.1 e he).1, (hE.1 e he).2.1⟩

/-- A strict-order matching on `s` has at most `s.card` edges. -/
theorem IsOrderMatching.card_le_card {s : Finset α} {E : Finset (α × α)}
    (hE : s.IsOrderMatching E) : E.card ≤ s.card :=
  Finset.card_le_card_of_injOn Prod.fst (fun e he ↦ (hE.1 e he).1) hE.2.1

/-- Inserting a pair `(a, b)` into a strict-order matching on `s` yields a strict-order matching
exactly when `a, b ∈ s`, `a < b`, and `(a, b)` shares neither endpoint with any distinct edge. -/
theorem isOrderMatching_insert_iff [DecidableEq α] {s : Finset α} {E : Finset (α × α)}
    {a b : α} :
    s.IsOrderMatching (insert (a, b) E) ↔
      s.IsOrderMatching E ∧ a ∈ s ∧ b ∈ s ∧ a < b ∧
      (∀ e ∈ E, e.1 = a → e = (a, b)) ∧ (∀ e ∈ E, e.2 = b → e = (a, b)) := by
  constructor
  · intro h
    refine ⟨h.subset (subset_insert _ _), (h.1 (a, b) (mem_insert_self _ _)).1,
      (h.1 (a, b) (mem_insert_self _ _)).2.1, (h.1 (a, b) (mem_insert_self _ _)).2.2, ?_, ?_⟩
    · intro e he he1
      exact h.2.1 (mem_coe.mpr (mem_insert_of_mem he)) (mem_coe.mpr (mem_insert_self _ _)) he1
    · intro e he he2
      exact h.2.2 (mem_coe.mpr (mem_insert_of_mem he)) (mem_coe.mpr (mem_insert_self _ _)) he2
  · rintro ⟨hE, has, hbs, hab, hfst, hsnd⟩
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      rcases mem_insert.mp he with rfl | he'
      · exact ⟨has, hbs, hab⟩
      · exact hE.1 e he'
    · intro e₁ he₁ e₂ he₂ heq
      rcases mem_insert.mp (mem_coe.mp he₁) with rfl | he₁' <;>
        rcases mem_insert.mp (mem_coe.mp he₂) with rfl | he₂'
      · rfl
      · exact (hfst e₂ he₂' heq.symm).symm
      · exact hfst e₁ he₁' heq
      · exact hE.2.1 he₁' he₂' heq
    · intro e₁ he₁ e₂ he₂ heq
      rcases mem_insert.mp (mem_coe.mp he₁) with rfl | he₁' <;>
        rcases mem_insert.mp (mem_coe.mp he₂) with rfl | he₂'
      · rfl
      · exact (hsnd e₂ he₂' heq.symm).symm
      · exact hsnd e₁ he₁' heq
      · exact hE.2.2 he₁' he₂' heq

/-- Strict-order embeddings preserve and reflect strict-order matchings. -/
@[simp]
theorem isOrderMatching_map_iff {β : Type*} [LT β] {s : Finset α} {E : Finset (α × α)}
    (f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)) :
    (s.map f.toEmbedding).IsOrderMatching (E.map (f.toEmbedding.prodMap f.toEmbedding)) ↔
      s.IsOrderMatching E := by
  constructor
  · rintro ⟨hmem, hfst, hsnd⟩
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      have h := hmem (f e.1, f e.2) (mem_map.mpr ⟨e, he, rfl⟩)
      exact ⟨(mem_map' f.toEmbedding).mp h.1, (mem_map' f.toEmbedding).mp h.2.1,
        f.map_rel_iff.mp h.2.2⟩
    · intro e₁ he₁ e₂ he₂ heq
      have h := hfst (mem_coe.mpr (mem_map.mpr ⟨e₁, he₁, rfl⟩))
        (mem_coe.mpr (mem_map.mpr ⟨e₂, he₂, rfl⟩)) (congrArg f heq)
      exact Prod.ext (f.injective (congrArg Prod.fst h)) (f.injective (congrArg Prod.snd h))
    · intro e₁ he₁ e₂ he₂ heq
      have h := hsnd (mem_coe.mpr (mem_map.mpr ⟨e₁, he₁, rfl⟩))
        (mem_coe.mpr (mem_map.mpr ⟨e₂, he₂, rfl⟩)) (congrArg f heq)
      exact Prod.ext (f.injective (congrArg Prod.fst h)) (f.injective (congrArg Prod.snd h))
  · rintro ⟨hmem, hfst, hsnd⟩
    refine ⟨?_, ?_, ?_⟩
    · intro e he
      obtain ⟨p, hp, rfl⟩ := mem_map.mp he
      exact ⟨mem_map_of_mem _ (hmem p hp).1, mem_map_of_mem _ (hmem p hp).2.1,
        f.map_rel_iff.mpr (hmem p hp).2.2⟩
    · intro e₁ he₁ e₂ he₂ heq
      obtain ⟨p₁, hp₁, rfl⟩ := mem_map.mp (mem_coe.mp he₁)
      obtain ⟨p₂, hp₂, rfl⟩ := mem_map.mp (mem_coe.mp he₂)
      exact congrArg (f.toEmbedding.prodMap f.toEmbedding)
        (hfst hp₁ hp₂ (f.injective heq))
    · intro e₁ he₁ e₂ he₂ heq
      obtain ⟨p₁, hp₁, rfl⟩ := mem_map.mp (mem_coe.mp he₁)
      obtain ⟨p₂, hp₂, rfl⟩ := mem_map.mp (mem_coe.mp he₂)
      exact congrArg (f.toEmbedding.prodMap f.toEmbedding)
        (hsnd hp₁ hp₂ (f.injective heq))

open scoped Classical in
/-- The maximum number of edges in a strict-order matching on `s`. -/
noncomputable def orderMatchingNumber (s : Finset α) : ℕ :=
  ((s ×ˢ s).powerset.filter s.IsOrderMatching).sup Finset.card

/-- Every strict-order matching on `s` has at most `s.orderMatchingNumber` edges. -/
theorem card_le_orderMatchingNumber {s : Finset α} {E : Finset (α × α)}
    (hE : s.IsOrderMatching E) : E.card ≤ s.orderMatchingNumber := by
  classical
  exact Finset.le_sup (f := Finset.card)
    (mem_filter.mpr ⟨mem_powerset.mpr hE.subset_product, hE⟩)

/-- `s.orderMatchingNumber ≤ n` if and only if every strict-order matching on `s` has at most `n`
edges. -/
theorem orderMatchingNumber_le_iff {s : Finset α} {n : ℕ} :
    s.orderMatchingNumber ≤ n ↔ ∀ E, s.IsOrderMatching E → E.card ≤ n := by
  classical
  simp only [orderMatchingNumber, Finset.sup_le_iff, mem_filter, mem_powerset, and_imp]
  exact ⟨fun h E hE ↦ h E hE.subset_product hE, fun h E _ hE ↦ h E hE⟩

/-- Some strict-order matching on `s` attains `s.orderMatchingNumber`. -/
theorem exists_isOrderMatching_card_eq_orderMatchingNumber (s : Finset α) :
    ∃ E, s.IsOrderMatching E ∧ E.card = s.orderMatchingNumber := by
  classical
  have hne : ((s ×ˢ s).powerset.filter s.IsOrderMatching).Nonempty :=
    ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), isOrderMatching_empty s⟩⟩
  obtain ⟨E, hE, hEq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  exact ⟨E, (mem_filter.mp hE).2, hEq.symm⟩

/-- `n ≤ s.orderMatchingNumber` if and only if some strict-order matching on `s` has at least `n`
edges. -/
theorem le_orderMatchingNumber_iff {s : Finset α} {n : ℕ} :
    n ≤ s.orderMatchingNumber ↔ ∃ E, s.IsOrderMatching E ∧ n ≤ E.card := by
  refine ⟨fun h ↦ ?_, fun ⟨_, hE, hn⟩ ↦ hn.trans (card_le_orderMatchingNumber hE)⟩
  obtain ⟨E, hE, hcard⟩ := s.exists_isOrderMatching_card_eq_orderMatchingNumber
  exact ⟨E, hE, hcard.symm ▸ h⟩

/-- The strict-order matching number of `s` is zero if and only if no pair of elements in `s` is
strictly ordered. -/
theorem orderMatchingNumber_eq_zero_iff {s : Finset α} :
    s.orderMatchingNumber = 0 ↔ ∀ a ∈ s, ∀ b ∈ s, ¬ a < b := by
  constructor
  · intro h a ha b hb hlt
    have h1 : 1 ≤ s.orderMatchingNumber :=
      (card_singleton (a, b)) ▸ card_le_orderMatchingNumber
        (isOrderMatching_singleton_iff.mpr ⟨ha, hb, hlt⟩)
    omega
  · intro hno
    apply Nat.eq_zero_of_le_zero
    rw [orderMatchingNumber_le_iff]
    intro E hE
    have hEempty : E = ∅ := eq_empty_iff_forall_notMem.mpr fun e he ↦
      hno e.1 (hE.1 e he).1 e.2 (hE.1 e he).2.1 (hE.1 e he).2.2
    simp [hEempty]

/-- The strict-order matching number of `s` is positive if and only if `s` contains a strictly
ordered pair. -/
theorem orderMatchingNumber_pos_iff {s : Finset α} :
    0 < s.orderMatchingNumber ↔ ∃ a ∈ s, ∃ b ∈ s, a < b := by
  rw [Nat.pos_iff_ne_zero, ne_eq, orderMatchingNumber_eq_zero_iff]
  push Not
  rfl

@[simp]
theorem orderMatchingNumber_empty : (∅ : Finset α).orderMatchingNumber = 0 :=
  orderMatchingNumber_eq_zero_iff.mpr fun _ h ↦ absurd h (notMem_empty _)

@[simp]
theorem orderMatchingNumber_singleton [Std.Irrefl (· < · : α → α → Prop)] (a : α) :
    ({a} : Finset α).orderMatchingNumber = 0 :=
  orderMatchingNumber_eq_zero_iff.mpr fun _ hx _ hy hlt ↦
    irrefl a (mem_singleton.mp hx ▸ mem_singleton.mp hy ▸ hlt)

/-- The strict-order matching number of `s` is at most the cardinality of `s`. -/
theorem orderMatchingNumber_le_card (s : Finset α) : s.orderMatchingNumber ≤ s.card :=
  orderMatchingNumber_le_iff.mpr fun _ hE ↦ hE.card_le_card

/-- The strict-order matching number is monotone under set inclusion. -/
theorem orderMatchingNumber_mono {s t : Finset α} (h : s ⊆ t) :
    s.orderMatchingNumber ≤ t.orderMatchingNumber :=
  orderMatchingNumber_le_iff.mpr fun _ hE ↦ card_le_orderMatchingNumber (hE.mono h)

/-- Strict-order embeddings preserve the strict-order matching number. -/
@[simp]
theorem orderMatchingNumber_map {β : Type*} [LT β] (s : Finset α)
    (f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)) :
    (s.map f.toEmbedding).orderMatchingNumber = s.orderMatchingNumber := by
  classical
  let ff : α × α ↪ β × β := f.toEmbedding.prodMap f.toEmbedding
  apply le_antisymm
  · rw [orderMatchingNumber_le_iff]
    intro F hF
    let E : Finset (α × α) := (s ×ˢ s).filter fun p ↦ ff p ∈ F
    have hEF : E.map ff = F := by
      ext e
      simp only [E, mem_map, mem_filter, mem_product]
      refine ⟨fun ⟨_, ⟨_, hpF⟩, heq⟩ ↦ heq ▸ hpF, fun he ↦ ?_⟩
      obtain ⟨a, has, ha⟩ := mem_map.mp (hF.1 e he).1
      obtain ⟨b, hbs, hb⟩ := mem_map.mp (hF.1 e he).2.1
      have hff : ff (a, b) = e := Prod.ext ha hb
      exact ⟨(a, b), ⟨⟨has, hbs⟩, hff.symm ▸ he⟩, hff⟩
    have hE : s.IsOrderMatching E := (isOrderMatching_map_iff f).mp (hEF.symm ▸ hF)
    simpa [← hEF] using card_le_orderMatchingNumber hE
  · rw [orderMatchingNumber_le_iff]
    intro E hE
    simpa using card_le_orderMatchingNumber ((isOrderMatching_map_iff f).mpr hE)

/-- In an irreflexive relation, `s` has strict-order matching number zero if and only if `s` is a
`<`-antichain. -/
theorem orderMatchingNumber_eq_zero_iff_isAntichain [Std.Irrefl (· < · : α → α → Prop)]
    {s : Finset α} : s.orderMatchingNumber = 0 ↔ IsAntichain (· < ·) (s : Set α) := by
  rw [orderMatchingNumber_eq_zero_iff]
  refine ⟨fun h _ ha _ hb _ ↦ h _ ha _ hb, fun hs _ ha b hb hlt ↦ ?_⟩
  exact hs ha hb (fun h ↦ Std.Irrefl.irrefl b (h ▸ hlt)) hlt

end Basic

end Finset

section ChainMatchingBridge

/-- In a strict-order matching `E` on `t` with `E.card + 1 = t.card`, unmatched right endpoint `a`,
and unmatched left endpoint `b`, any subset `B ⊆ t` containing `a` and omitting `b` has an edge of
`E` leaving `B`. -/
private theorem exists_crossing_edge_of_isOrderMatching {α : Type*} [LT α] {t B : Finset α}
    {E : Finset (α × α)} {a b : α} (hE : t.IsOrderMatching E) (hcard : E.card + 1 = t.card)
    (hbt : b ∈ t) (ha_in : ∀ e ∈ E, e.2 ≠ a) (hb_out : ∀ e ∈ E, e.1 ≠ b)
    (hBt : B ⊆ t) (haB : a ∈ B) (hbB : b ∉ B) :
    ∃ e ∈ E, e.1 ∈ B ∧ e.2 ∉ B := by
  classical
  by_contra hno
  have hclosed : ∀ e ∈ E, e.1 ∈ B → e.2 ∈ B := fun e he h1 ↦ by
    by_contra h2
    exact hno ⟨e, he, h1, h2⟩
  have hmaps : Set.MapsTo Prod.fst (E : Set (α × α)) ((t.erase b : Finset α) : Set α) :=
    fun e he ↦ Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hb_out e he, (hE.1 e he).1⟩)
  have hcard_le : (t.erase b).card ≤ E.card := by
    rw [Finset.card_erase_of_mem hbt]
    omega
  have hsurj := Finset.surjOn_of_injOn_of_card_le Prod.fst hmaps hE.2.1 hcard_le
  have hex : ∀ x ∈ B, ∃ e ∈ E, e.1 = x := fun x hx ↦
    hsurj (Finset.mem_erase.mpr ⟨fun hxb ↦ hbB (hxb ▸ hx), hBt hx⟩)
  let next : α → α := fun x ↦ if hx : x ∈ B then (hex x hx).choose.2 else x
  have hspec : ∀ x (hx : x ∈ B), (hex x hx).choose ∈ E ∧ (hex x hx).choose.1 = x :=
    fun x hx ↦ (hex x hx).choose_spec
  have hle : B.card ≤ (B.erase a).card := by
    refine Finset.card_le_card_of_injOn next (fun x hx ↦ ?_) (fun x hx y hy hxy ↦ ?_)
    · have hx' : x ∈ B := Finset.mem_coe.mp hx
      simp only [next, hx', ↓reduceDIte, Finset.mem_coe, Finset.mem_erase]
      exact ⟨ha_in _ (hspec x hx').1, hclosed _ (hspec x hx').1 ((hspec x hx').2.symm ▸ hx')⟩
    · have hx' : x ∈ B := Finset.mem_coe.mp hx
      have hy' : y ∈ B := Finset.mem_coe.mp hy
      simp only [next, hx', hy', ↓reduceDIte] at hxy
      have heq := hE.2.2 (hspec x hx').1 (hspec y hy').1 hxy
      rw [← (hspec x hx').2, ← (hspec y hy').2, heq]
  have hlt : (B.erase a).card < B.card := Finset.card_erase_lt_of_mem haB
  omega

/-- Replacing an edge `(u, v) ∈ E` by `(u, y)` and `(y, v)` for a fresh vertex `y ∉ t` with
`u < y < v` yields a strict-order matching on `insert y t` with one additional edge and the same
unmatched endpoints `a` and `b`. -/
private theorem isOrderMatching_split_edge {α : Type*} [LT α] [DecidableEq α]
    {t : Finset α} {E : Finset (α × α)} {y u v a b : α}
    (hE : t.IsOrderMatching E) (hyt : y ∉ t) (huv : (u, v) ∈ E) (huy : u < y) (hyv : y < v)
    (hat : a ∈ t) (hbt : b ∈ t) (ha_in : ∀ e ∈ E, e.2 ≠ a) (hb_out : ∀ e ∈ E, e.1 ≠ b) :
    let E' := insert (u, y) (insert (y, v) (E.erase (u, v)))
    (insert y t).IsOrderMatching E' ∧ E'.card = E.card + 1 ∧
      (∀ e ∈ E', e.2 ≠ a) ∧ (∀ e ∈ E', e.1 ≠ b) := by
  have hu : u ∈ t := (hE.1 (u, v) huv).1
  have hv : v ∈ t := (hE.1 (u, v) huv).2.1
  have hE1 : (insert y t).IsOrderMatching (insert (y, v) (E.erase (u, v))) := by
    rw [Finset.isOrderMatching_insert_iff]
    refine ⟨(hE.subset (Finset.erase_subset _ _)).mono (Finset.subset_insert _ _),
      Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hv, hyv, fun e he he1 ↦ ?_,
      fun e he he2 ↦ ?_⟩
    · exact absurd (he1 ▸ (hE.1 e (Finset.mem_erase.mp he).2).1) hyt
    · exact absurd (hE.2.2 (Finset.mem_erase.mp he).2 huv he2) (Finset.mem_erase.mp he).1
  have hE2 : (insert y t).IsOrderMatching (insert (u, y) (insert (y, v) (E.erase (u, v)))) := by
    rw [Finset.isOrderMatching_insert_iff]
    refine ⟨hE1, Finset.mem_insert_of_mem hu, Finset.mem_insert_self _ _, huy, fun e he he1 ↦ ?_,
      fun e he he2 ↦ ?_⟩
    · rcases Finset.mem_insert.mp he with rfl | he'
      · exact absurd (by dsimp at he1; exact he1.symm ▸ hu) hyt
      · exact absurd (hE.2.1 (Finset.mem_erase.mp he').2 huv he1) (Finset.mem_erase.mp he').1
    · rcases Finset.mem_insert.mp he with rfl | he'
      · exact absurd (by dsimp at he2; exact he2 ▸ hv) hyt
      · exact absurd (he2 ▸ (hE.1 e (Finset.mem_erase.mp he').2).2.1) hyt
  have h1not : (y, v) ∉ E.erase (u, v) := fun h ↦ hyt (hE.1 _ (Finset.mem_erase.mp h).2).1
  have h2not : (u, y) ∉ insert (y, v) (E.erase (u, v)) := fun h ↦ by
    rcases Finset.mem_insert.mp h with heq | h'
    · exact hyt ((Prod.mk.inj heq).1 ▸ hu)
    · exact hyt (hE.1 _ (Finset.mem_erase.mp h').2).2.1
  refine ⟨hE2, ?_, fun e he ↦ ?_, fun e he ↦ ?_⟩
  · rw [Finset.card_insert_of_notMem h2not, Finset.card_insert_of_notMem h1not,
      Finset.card_erase_of_mem huv]
    have : 1 ≤ E.card := Finset.card_pos.mpr ⟨(u, v), huv⟩
    omega
  · rcases Finset.mem_insert.mp he with rfl | he'
    · exact fun h ↦ by dsimp at h; exact hyt (h.symm ▸ hat)
    · rcases Finset.mem_insert.mp he' with rfl | he''
      · exact ha_in (u, v) huv
      · exact ha_in e (Finset.mem_erase.mp he'').2
  · rcases Finset.mem_insert.mp he with rfl | he'
    · exact hb_out (u, v) huv
    · rcases Finset.mem_insert.mp he' with rfl | he''
      · exact fun h ↦ by dsimp at h; exact hyt (h.symm ▸ hbt)
      · exact hb_out e (Finset.mem_erase.mp he'').2

/-- Prepending an edge `(y, a)` from a fresh vertex `y ∉ t` to an unmatched right endpoint `a ∈ t`
extends a strict-order matching on `t` to `insert y t`. -/
private theorem isOrderMatching_prepend_edge {α : Type*} [LT α] [DecidableEq α]
    {t : Finset α} {E : Finset (α × α)} {y a b : α}
    (hE : t.IsOrderMatching E) (hyt : y ∉ t) (hat : a ∈ t) (hbt : b ∈ t) (hya : y < a)
    (ha_in : ∀ e ∈ E, e.2 ≠ a) (hb_out : ∀ e ∈ E, e.1 ≠ b) :
    (insert y t).IsOrderMatching (insert (y, a) E) ∧ (insert (y, a) E).card = E.card + 1 ∧
      (∀ e ∈ insert (y, a) E, e.2 ≠ y) ∧ (∀ e ∈ insert (y, a) E, e.1 ≠ b) := by
  have hnot : (y, a) ∉ E := fun h ↦ hyt (hE.1 _ h).1
  refine ⟨Finset.isOrderMatching_insert_iff.mpr ⟨hE.mono (Finset.subset_insert _ _),
      Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hat, hya,
      fun e he h ↦ (hyt (h ▸ (hE.1 e he).1)).elim, fun e he h ↦ (ha_in e he h).elim⟩,
    Finset.card_insert_of_notMem hnot, fun e he h ↦ ?_, fun e he h ↦ ?_⟩
  · rcases Finset.mem_insert.mp he with rfl | he'
    · dsimp at h; exact hyt (h ▸ hat)
    · exact hyt (h ▸ (hE.1 e he').2.1)
  · rcases Finset.mem_insert.mp he with rfl | he'
    · dsimp at h; exact hyt (h.symm ▸ hbt)
    · exact hb_out e he' h

/-- Appending an edge `(b, y)` from an unmatched left endpoint `b ∈ t` to a fresh vertex `y ∉ t`
extends a strict-order matching on `t` to `insert y t`. -/
private theorem isOrderMatching_append_edge {α : Type*} [LT α] [DecidableEq α]
    {t : Finset α} {E : Finset (α × α)} {y a b : α}
    (hE : t.IsOrderMatching E) (hyt : y ∉ t) (hat : a ∈ t) (hbt : b ∈ t) (hby : b < y)
    (ha_in : ∀ e ∈ E, e.2 ≠ a) (hb_out : ∀ e ∈ E, e.1 ≠ b) :
    (insert y t).IsOrderMatching (insert (b, y) E) ∧ (insert (b, y) E).card = E.card + 1 ∧
      (∀ e ∈ insert (b, y) E, e.2 ≠ a) ∧ (∀ e ∈ insert (b, y) E, e.1 ≠ y) := by
  have hnot : (b, y) ∉ E := fun h ↦ hyt (hE.1 _ h).2.1
  refine ⟨Finset.isOrderMatching_insert_iff.mpr ⟨hE.mono (Finset.subset_insert _ _),
      Finset.mem_insert_of_mem hbt, Finset.mem_insert_self _ _, hby,
      fun e he h ↦ (hb_out e he h).elim, fun e he h ↦ (hyt (h ▸ (hE.1 e he).2.1)).elim⟩,
    Finset.card_insert_of_notMem hnot, fun e he h ↦ ?_, fun e he h ↦ ?_⟩
  · rcases Finset.mem_insert.mp he with rfl | he'
    · dsimp at h; exact hyt (h.symm ▸ hat)
    · exact ha_in e he' h
  · rcases Finset.mem_insert.mp he with rfl | he'
    · dsimp at h; exact hyt (h ▸ hbt)
    · exact hyt (h ▸ (hE.1 e he').1)

/-- A nonempty finite `<`-chain `c` (for any relation `<`, not necessarily transitive) admits a
strict-order matching on `c` with `c.card - 1` edges. -/
theorem IsChain.exists_isOrderMatching_card_add_one {α : Type*} [LT α] {c : Finset α}
    (hchain : IsChain (· < ·) (c : Set α)) (hc : c.Nonempty) :
    ∃ E, c.IsOrderMatching E ∧ E.card + 1 = c.card := by
  classical
  suffices ∃ (E : Finset (α × α)) (a b : α),
      c.IsOrderMatching E ∧ E.card + 1 = c.card ∧
      a ∈ c ∧ b ∈ c ∧ (∀ e ∈ E, e.2 ≠ a) ∧ (∀ e ∈ E, e.1 ≠ b) by
    obtain ⟨E, _, _, hE, hcard, -, -, -, -⟩ := this
    exact ⟨E, hE, hcard⟩
  induction hc using Finset.Nonempty.cons_induction with
  | singleton x =>
    exact ⟨∅, x, x, Finset.isOrderMatching_empty _, by simp, Finset.mem_singleton_self x,
      Finset.mem_singleton_self x, by simp, by simp⟩
  | @cons y t hyt _ ih =>
    rw [Finset.cons_eq_insert] at hchain ⊢
    obtain ⟨E, a, b, hE, hcard, hat, hbt, ha_in, hb_out⟩ :=
      ih (hchain.mono (Finset.coe_subset.mpr (Finset.subset_insert y t)))
    by_cases h1 : y < a
    · obtain ⟨hE', hcard', ha', hb'⟩ :=
        isOrderMatching_prepend_edge hE hyt hat hbt h1 ha_in hb_out
      exact ⟨_, y, b, hE', by rw [hcard', Finset.card_insert_of_notMem hyt]; omega,
        Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hbt, ha', hb'⟩
    · by_cases h2 : b < y
      · obtain ⟨hE', hcard', ha', hb'⟩ :=
          isOrderMatching_append_edge hE hyt hat hbt h2 ha_in hb_out
        exact ⟨_, a, y, hE', by rw [hcard', Finset.card_insert_of_notMem hyt]; omega,
          Finset.mem_insert_of_mem hat, Finset.mem_insert_self _ _, ha', hb'⟩
      · have hay : a < y := (hchain (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hat)
          (fun h ↦ hyt (h ▸ hat))).resolve_left h1
        obtain ⟨⟨u, v⟩, huv, huB, hvB⟩ := exists_crossing_edge_of_isOrderMatching hE hcard hbt ha_in
          hb_out (Finset.filter_subset (· < y) t) (Finset.mem_filter.mpr ⟨hat, hay⟩)
          (fun h ↦ h2 (Finset.mem_filter.mp h).2)
        have hv_t : v ∈ t := (hE.1 (u, v) huv).2.1
        have hyv : y < v := (hchain (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hv_t)
          (fun h ↦ hyt (h ▸ hv_t))).resolve_right (fun h ↦ hvB (Finset.mem_filter.mpr ⟨hv_t, h⟩))
        obtain ⟨hE', hcard', ha', hb'⟩ := isOrderMatching_split_edge hE hyt huv
          (Finset.mem_filter.mp huB).2 hyv hat hbt ha_in hb_out
        exact ⟨_, a, b, hE', by rw [hcard', Finset.card_insert_of_notMem hyt]; omega,
          Finset.mem_insert_of_mem hat, Finset.mem_insert_of_mem hbt, ha', hb'⟩

namespace Finset

/-- Every pairwise-disjoint partition `C` of `s` into nonempty `<`-chains yields a strict-order
matching `E` on `s` satisfying `E.card + C.card = s.card`. -/
theorem exists_isOrderMatching_of_chainPartition {α : Type*} [LT α] [DecidableEq α]
    {s : Finset α} {C : Finset (Finset α)}
    (hC : ∀ c ∈ C, c.Nonempty ∧ IsChain (· < ·) (c : Set α))
    (hdisj : (C : Set (Finset α)).Pairwise Disjoint)
    (hcov : C.biUnion id = s) :
    ∃ E, s.IsOrderMatching E ∧ E.card + C.card = s.card := by
  classical
  let edgeOf : Finset α → Finset (α × α) := fun c ↦
    if hc : c ∈ C then ((hC c hc).2.exists_isOrderMatching_card_add_one (hC c hc).1).choose else ∅
  have hedge : ∀ c ∈ C, c.IsOrderMatching (edgeOf c) ∧ (edgeOf c).card + 1 = c.card :=
    fun c hc ↦ by
      simpa only [edgeOf, hc, ↓reduceDIte] using
        ((hC c hc).2.exists_isOrderMatching_card_add_one (hC c hc).1).choose_spec
  have hdisjE : (C : Set (Finset α)).PairwiseDisjoint edgeOf := fun c₁ hc₁ c₂ hc₂ hne ↦
    Finset.disjoint_left.mpr fun e he₁ he₂ ↦
      Finset.disjoint_left.mp (hdisj hc₁ hc₂ hne)
        ((hedge c₁ hc₁).1.1 e he₁).1 ((hedge c₂ hc₂).1.1 e he₂).1
  refine ⟨C.biUnion edgeOf, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro e he
    obtain ⟨c, hc, hec⟩ := mem_biUnion.mp he
    have hcs : c ⊆ s := hcov ▸ subset_biUnion_of_mem id hc
    exact ⟨hcs ((hedge c hc).1.1 e hec).1, hcs ((hedge c hc).1.1 e hec).2.1,
      ((hedge c hc).1.1 e hec).2.2⟩
  · intro e₁ he₁ e₂ he₂ heq
    obtain ⟨c₁, hc₁, h₁⟩ := mem_biUnion.mp (mem_coe.mp he₁)
    obtain ⟨c₂, hc₂, h₂⟩ := mem_biUnion.mp (mem_coe.mp he₂)
    have hc : c₁ = c₂ := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj hc₁ hc₂ hne)
        ((hedge c₁ hc₁).1.1 e₁ h₁).1 (heq ▸ ((hedge c₂ hc₂).1.1 e₂ h₂).1)
    subst hc
    exact (hedge c₁ hc₁).1.2.1 h₁ h₂ heq
  · intro e₁ he₁ e₂ he₂ heq
    obtain ⟨c₁, hc₁, h₁⟩ := mem_biUnion.mp (mem_coe.mp he₁)
    obtain ⟨c₂, hc₂, h₂⟩ := mem_biUnion.mp (mem_coe.mp he₂)
    have hc : c₁ = c₂ := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj hc₁ hc₂ hne)
        ((hedge c₁ hc₁).1.1 e₁ h₁).2.1 (heq ▸ ((hedge c₂ hc₂).1.1 e₂ h₂).2.1)
    subst hc
    exact (hedge c₁ hc₁).1.2.2 h₁ h₂ heq
  · have hdisjId : (C : Set (Finset α)).PairwiseDisjoint id := hdisj
    rw [card_biUnion hdisjE, ← hcov, card_biUnion hdisjId]
    calc
      ∑ c ∈ C, (edgeOf c).card + C.card = ∑ c ∈ C, ((edgeOf c).card + 1) := by
        simp [Finset.sum_add_distrib]
      _ = ∑ c ∈ C, (id c).card := Finset.sum_congr rfl fun c hc ↦ (hedge c hc).2

/-- Endpoint invariants after merging `cₐ` and `c_b` along a strict edge `(a, b)`: every unmatched
left endpoint remains strictly greatest in its chain, and every unmatched right endpoint remains
strictly least in its chain. -/
private theorem merge_strictChain_endpoints {α : Type*} [LT α] [IsStrictOrder α (· < ·)]
    [DecidableEq α] {E : Finset (α × α)} {C : Finset (Finset α)} {a b : α} {cₐ c_b : Finset α}
    (hmax : ∀ c ∈ C, ∀ x ∈ c, (∀ e ∈ E, e.1 ≠ x) → ∀ u ∈ c, u ≠ x → u < x)
    (hmin : ∀ c ∈ C, ∀ x ∈ c, (∀ e ∈ E, e.2 ≠ x) → ∀ v ∈ c, v ≠ x → x < v)
    (hcₐ : cₐ ∈ C) (ha : a ∈ cₐ) (ha_top : ∀ u ∈ cₐ, u ≠ a → u < a)
    (hc_b : c_b ∈ C) (hb : b ∈ c_b) (hb_bot : ∀ v ∈ c_b, v ≠ b → b < v)
    (hcross : ∀ u ∈ cₐ, ∀ v ∈ c_b, u < v) :
    let C' := insert (cₐ ∪ c_b) ((C.erase cₐ).erase c_b)
    (∀ c ∈ C', ∀ x ∈ c, (∀ e ∈ insert (a, b) E, e.1 ≠ x) → ∀ u ∈ c, u ≠ x → u < x) ∧
    (∀ c ∈ C', ∀ x ∈ c, (∀ e ∈ insert (a, b) E, e.2 ≠ x) → ∀ v ∈ c, v ≠ x → x < v) := by
  have hRsub : (C.erase cₐ).erase c_b ⊆ C := (erase_subset _ _).trans (erase_subset _ _)
  refine ⟨fun c hc x hx hxout u hu hux ↦ ?_, fun c hc x hx hxin v hv hvx ↦ ?_⟩
  · have hxE : ∀ e ∈ E, e.1 ≠ x := fun e he ↦ hxout e (mem_insert_of_mem he)
    have hxa : x ≠ a := fun h ↦ hxout (a, b) (mem_insert_self _ _) h.symm
    rcases mem_insert.mp hc with rfl | hcR
    · have hxb : x ∈ c_b := by
        rcases mem_union.mp hx with hxa' | hxb'
        · exact absurd (ha_top x hxa' hxa) (asymm (hmax cₐ hcₐ x hxa' hxE a ha hxa.symm))
        · exact hxb'
      rcases mem_union.mp hu with hua' | hub'
      · exact hcross u hua' x hxb
      · exact hmax c_b hc_b x hxb hxE u hub' hux
    · exact hmax c (hRsub hcR) x hx hxE u hu hux
  · have hxE : ∀ e ∈ E, e.2 ≠ x := fun e he ↦ hxin e (mem_insert_of_mem he)
    have hxb : x ≠ b := fun h ↦ hxin (a, b) (mem_insert_self _ _) h.symm
    rcases mem_insert.mp hc with rfl | hcR
    · have hxa : x ∈ cₐ := by
        rcases mem_union.mp hx with hxa' | hxb'
        · exact hxa'
        · exact absurd (hb_bot x hxb' hxb) (asymm (hmin c_b hc_b x hxb' hxE b hb hxb.symm))
      rcases mem_union.mp hv with hva' | hvb'
      · exact hmin cₐ hcₐ x hxa hxE v hva' hvx
      · exact hcross x hxa v hvb'
    · exact hmin c (hRsub hcR) x hx hxE v hv hvx

/-- Merging the chain ending at `a` and the chain starting at `b` along a strict edge `a < b`
produces a strict chain whose strictly greatest and least elements stay unmatched. -/
private theorem merge_strictChain_step {α : Type*} [LT α] [IsStrictOrder α (· < ·)] [DecidableEq α]
    {s : Finset α} {E : Finset (α × α)} {C : Finset (Finset α)} {a b : α} {cₐ c_b : Finset α}
    (hab : a < b) (hC : ∀ c ∈ C, c.Nonempty ∧ IsChain (· < ·) (c : Set α))
    (hdisj : (C : Set (Finset α)).Pairwise Disjoint) (hcov : C.biUnion id = s)
    (hcard : E.card + C.card = s.card)
    (hmax : ∀ c ∈ C, ∀ x ∈ c, (∀ e ∈ E, e.1 ≠ x) → ∀ u ∈ c, u ≠ x → u < x)
    (hmin : ∀ c ∈ C, ∀ x ∈ c, (∀ e ∈ E, e.2 ≠ x) → ∀ v ∈ c, v ≠ x → x < v)
    (hcₐ : cₐ ∈ C) (ha : a ∈ cₐ) (ha_out : ∀ e ∈ E, e.1 ≠ a)
    (hc_b : c_b ∈ C) (hb : b ∈ c_b) (hb_in : ∀ e ∈ E, e.2 ≠ b)
    (hab_notMem : (a, b) ∉ E) :
    ∃ C' : Finset (Finset α),
      (∀ c ∈ C', c.Nonempty ∧ IsChain (· < ·) (c : Set α)) ∧
      (C' : Set (Finset α)).Pairwise Disjoint ∧
      C'.biUnion id = s ∧
      (insert (a, b) E).card + C'.card = s.card ∧
      (∀ c ∈ C', ∀ x ∈ c, (∀ e ∈ insert (a, b) E, e.1 ≠ x) → ∀ u ∈ c, u ≠ x → u < x) ∧
      (∀ c ∈ C', ∀ x ∈ c, (∀ e ∈ insert (a, b) E, e.2 ≠ x) → ∀ v ∈ c, v ≠ x → x < v) := by
  have ha_top : ∀ u ∈ cₐ, u ≠ a → u < a := hmax cₐ hcₐ a ha ha_out
  have hb_bot : ∀ v ∈ c_b, v ≠ b → b < v := hmin c_b hc_b b hb hb_in
  have hne_c : cₐ ≠ c_b := fun h ↦
    asymm hab (ha_top b (h ▸ hb) fun hba ↦ irrefl a (hba ▸ hab))
  have hcross : ∀ u ∈ cₐ, ∀ v ∈ c_b, u < v := fun u hu v hv ↦ by
    rcases eq_or_ne u a with rfl | hua <;> rcases eq_or_ne v b with rfl | hvb
    · exact hab
    · exact _root_.trans hab (hb_bot v hv hvb)
    · exact _root_.trans (ha_top u hu hua) hab
    · exact _root_.trans (_root_.trans (ha_top u hu hua) hab) (hb_bot v hv hvb)
  let R : Finset (Finset α) := (C.erase cₐ).erase c_b
  have hRsub : R ⊆ C := (erase_subset _ _).trans (erase_subset _ _)
  have hdisj_union : ∀ c ∈ R, Disjoint (cₐ ∪ c_b) c := fun c hc ↦
    Finset.disjoint_union_left.mpr
      ⟨hdisj hcₐ (hRsub hc) (mem_erase.mp (mem_erase.mp hc).2).1.symm,
        hdisj hc_b (hRsub hc) (mem_erase.mp hc).1.symm⟩
  have hunion_notMem : cₐ ∪ c_b ∉ R := fun h ↦
    Finset.disjoint_left.mp (hdisj_union _ h) (mem_union_left c_b ha) (mem_union_left c_b ha)
  have hend := merge_strictChain_endpoints hmax hmin hcₐ ha ha_top hc_b hb hb_bot hcross
  refine ⟨insert (cₐ ∪ c_b) R, ?_, ?_, ?_, ?_, hend.1, hend.2⟩
  · intro c hc
    rcases mem_insert.mp hc with rfl | hcR
    · refine ⟨⟨a, mem_union_left c_b ha⟩, ?_⟩
      rw [coe_union]
      exact isChain_union.mpr ⟨(hC cₐ hcₐ).2, (hC c_b hc_b).2,
        fun u hu v hv _ ↦ Or.inl (hcross u hu v hv)⟩
    · exact hC c (hRsub hcR)
  · rw [coe_insert, Set.pairwise_insert_of_symm]
    exact ⟨hdisj.mono (coe_subset.mpr hRsub), fun c hc _ ↦ hdisj_union c hc⟩
  · rw [biUnion_insert, id_eq, ← hcov]
    ext x
    simp only [mem_union, mem_biUnion, id_eq, R, mem_erase]
    grind
  · have hRcard : R.card + 2 = C.card := by
      rw [card_erase_of_mem (mem_erase.mpr ⟨hne_c.symm, hc_b⟩), card_erase_of_mem hcₐ]
      have : 2 ≤ C.card := Finset.one_lt_card.mpr ⟨cₐ, hcₐ, c_b, hc_b, hne_c⟩
      omega
    rw [card_insert_of_notMem hab_notMem, card_insert_of_notMem hunion_notMem]
    omega

/-- Every strict-order matching `E` on `s` in a strict partial order yields a pairwise-disjoint
partition `C` of `s` into nonempty strict chains satisfying `E.card + C.card = s.card`. -/
theorem IsOrderMatching.exists_chainPartition {α : Type*} [LT α] [IsStrictOrder α (· < ·)]
    [DecidableEq α] {s : Finset α} {E : Finset (α × α)} (hE : s.IsOrderMatching E) :
    ∃ C : Finset (Finset α),
      (∀ c ∈ C, c.Nonempty ∧ IsChain (· < ·) (c : Set α)) ∧
      (C : Set (Finset α)).Pairwise Disjoint ∧
      C.biUnion id = s ∧ E.card + C.card = s.card := by
  suffices ∃ C : Finset (Finset α),
      (∀ c ∈ C, c.Nonempty ∧ IsChain (· < ·) (c : Set α)) ∧
      (C : Set (Finset α)).Pairwise Disjoint ∧
      C.biUnion id = s ∧ E.card + C.card = s.card ∧
      (∀ c ∈ C, ∀ x ∈ c, (∀ e ∈ E, e.1 ≠ x) → ∀ u ∈ c, u ≠ x → u < x) ∧
      (∀ c ∈ C, ∀ x ∈ c, (∀ e ∈ E, e.2 ≠ x) → ∀ v ∈ c, v ≠ x → x < v) by
    obtain ⟨C, h1, h2, h3, h4, -, -⟩ := this
    exact ⟨C, h1, h2, h3, h4⟩
  induction E using Finset.induction_on with
  | empty =>
    refine ⟨s.image singleton, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      obtain ⟨x, -, rfl⟩ := mem_image.mp hc
      exact ⟨singleton_nonempty x, by simp⟩
    · intro c₁ hc₁ c₂ hc₂ hne
      obtain ⟨x₁, -, rfl⟩ := mem_image.mp (mem_coe.mp hc₁)
      obtain ⟨x₂, -, rfl⟩ := mem_image.mp (mem_coe.mp hc₂)
      exact Finset.disjoint_singleton.mpr fun h ↦ hne (congrArg singleton h)
    · ext x
      simp
    · rw [card_empty, zero_add, card_image_of_injective _ singleton_injective]
    · intro c hc x hx _ u hu hux
      obtain ⟨y, -, rfl⟩ := mem_image.mp hc
      exact absurd ((mem_singleton.mp hu).trans (mem_singleton.mp hx).symm) hux
    · intro c hc x hx _ v hv hvx
      obtain ⟨y, -, rfl⟩ := mem_image.mp hc
      exact absurd ((mem_singleton.mp hv).trans (mem_singleton.mp hx).symm) hvx
  | @insert e E' henot ih =>
    rcases e with ⟨a, b⟩
    obtain ⟨hE', has, hbs, hab, hfst, hsnd⟩ := isOrderMatching_insert_iff.mp hE
    obtain ⟨C, hC, hdisj, hcov, hcard, hmax, hmin⟩ := ih hE'
    obtain ⟨cₐ, hcₐ, ha⟩ := mem_biUnion.mp (hcov.symm ▸ has)
    obtain ⟨c_b, hc_b, hb⟩ := mem_biUnion.mp (hcov.symm ▸ hbs)
    have ha_out : ∀ e ∈ E', e.1 ≠ a := fun e he h ↦ henot (hfst e he h ▸ he)
    have hb_in : ∀ e ∈ E', e.2 ≠ b := fun e he h ↦ henot (hsnd e he h ▸ he)
    exact merge_strictChain_step hab hC hdisj hcov hcard hmax hmin hcₐ ha ha_out hc_b hb hb_in
      henot

/-- Weak duality between strict-order matchings and strict antichains: in a strict partial order,
`E.card + A.card ≤ s.card` whenever `E` is a strict-order matching on `s` and `A ⊆ s` is a
`<`-antichain. -/
theorem IsOrderMatching.card_add_card_le_of_isAntichain {α : Type*} [LT α]
    [IsStrictOrder α (· < ·)] {s A : Finset α} {E : Finset (α × α)}
    (hE : s.IsOrderMatching E) (hAs : A ⊆ s) (hA : IsAntichain (· < ·) (A : Set α)) :
    E.card + A.card ≤ s.card := by
  classical
  obtain ⟨C, hC, -, hcov, hcard⟩ := hE.exists_chainPartition
  have hAC : A.card ≤ C.card :=
    hA.card_le_card_of_chainCover (fun c hc ↦ (hC c hc).2) fun a ha ↦ by
      simpa [← hcov] using hAs ha
  omega

/-- **Split-graph matching duality for finite partial orders.** On any finite subset `s` of a
partial order, the maximum size of a strict-order matching plus the antichain width equals
`s.card`. -/
theorem orderMatchingNumber_add_antichainWidth {α : Type*} [PartialOrder α] (s : Finset α) :
    s.orderMatchingNumber + s.antichainWidth = s.card := by
  classical
  apply le_antisymm
  · obtain ⟨E, hE, hEcard⟩ := s.exists_isOrderMatching_card_eq_orderMatchingNumber
    obtain ⟨A, hAs, hA, hAcard⟩ := s.exists_isAntichain_card_eq_antichainWidth
    rw [← hEcard, ← hAcard]
    exact hE.card_add_card_le_of_isAntichain hAs (hA.mono fun _ _ h ↦ h.le)
  · obtain ⟨A, C, hAs, hA, hC, hdisj, hcov, hcard⟩ := s.exists_isAntichain_chainPartition
    obtain ⟨E, hE, hEC⟩ := exists_isOrderMatching_of_chainPartition
      (fun c hc ↦ ⟨(hC c hc).1, (hC c hc).2.lt_of_le⟩) hdisj hcov
    have h1 : E.card ≤ s.orderMatchingNumber := card_le_orderMatchingNumber hE
    have h2 : A.card ≤ s.antichainWidth := card_le_antichainWidth hAs hA
    omega

end Finset

end ChainMatchingBridge

end OrderMatching
