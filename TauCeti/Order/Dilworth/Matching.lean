/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Prod
public import TauCeti.Order.Dilworth.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Preimage

/-!
# Split-graph order matchings and Dilworth duality

An order matching on a finite set `s` for a binary relation `r` (`Finset.IsOrderMatching`) is a
finite set of `r`-related pairs in `s × s` whose left and right projections are injective,
modeling matchings in the split bipartite graph of `(s, r)`. Its maximum cardinality is
`Finset.orderMatchingNumber`.

Every nonempty finite `r`-chain admits an `r`-order matching of size `c.card - 1` by Rédei's
edge-splitting induction (`IsChain.exists_isOrderMatching_card_add_one`), so pairwise-disjoint
partitions into nonempty `r`-chains convert to `r`-order matchings with `E.card + C.card = s.card`
(`Finset.exists_isOrderMatching_of_chainPartition`). Conversely, when `r` is a strict order
(`[IsStrictOrder α r]`), every `r`-order matching `E` induces a partition of `s` into
`s.card - E.card` nonempty `r`-chains (`Finset.IsOrderMatching.exists_chainPartition`). Combined
with Dilworth's theorem, this yields the split-graph matching duality
`s.orderMatchingNumber r + s.antichainWidth r = s.card`
(`Finset.orderMatchingNumber_add_antichainWidth`), specializing in a partial order to
`s.orderMatchingNumber (· < ·) + s.antichainWidth (· ≤ ·) = s.card`
(`Finset.orderMatchingNumber_lt_add_antichainWidth_le`).

## Main definitions

* `Finset.IsOrderMatching`: predicate for a finite set of `r`-related pairs in `s × s` whose
  first and second projections are injective.
* `Finset.orderMatchingNumber`: the maximum number of edges in an `r`-order matching on `s`.

## Main results

* `IsChain.exists_isOrderMatching_card_add_one`: every nonempty finite `r`-chain admits an
  `r`-order matching of size `c.card - 1` (Rédei's edge-splitting theorem).
* `Finset.exists_isOrderMatching_of_chainPartition` and
  `Finset.IsOrderMatching.exists_chainPartition`: conversion between pairwise-disjoint chain
  partitions and order matchings with `E.card + C.card = s.card`.
* `Finset.IsOrderMatching.card_add_card_le_of_isAntichain`: weak duality between order matchings
  and antichains for a strict order.
* `Finset.orderMatchingNumber_add_antichainWidth` and
  `Finset.orderMatchingNumber_lt_add_antichainWidth_le`: split-graph matching duality for strict
  orders and partial orders.

## References

* L. Rédei, *Ein kombinatorischer Satz*, Acta Litt. Sci. Szeged **7** (1934), 39–43.
* M. X. Goemans, *18.997 Topics in Combinatorial Optimization, Lecture 6* (MIT, 2004),
  Theorem 3 and split-poset matching duality.
-/

public section

section OrderMatching

namespace Finset

section Basic

variable {α : Type*}

/-- An order matching on `s` for a binary relation `r` is a finite set of `r`-related pairs in
`s × s` whose first and second projections are injective. In the split bipartite graph of `(s, r)`,
each element appears at most once on the left and at most once on the right. -/
structure IsOrderMatching (s : Finset α) (r : α → α → Prop) (E : Finset (α × α)) : Prop where
  /-- Every edge in the matching has its left endpoint in `s`. -/
  fst_mem : ∀ ⦃e : α × α⦄, e ∈ E → e.1 ∈ s
  /-- Every edge in the matching has its right endpoint in `s`. -/
  snd_mem : ∀ ⦃e : α × α⦄, e ∈ E → e.2 ∈ s
  /-- Every edge in the matching is related by `r`. -/
  rel : ∀ ⦃e : α × α⦄, e ∈ E → r e.1 e.2
  /-- Distinct edges in the matching have distinct left endpoints. -/
  injOn_fst : (E : Set (α × α)).InjOn Prod.fst
  /-- Distinct edges in the matching have distinct right endpoints. -/
  injOn_snd : (E : Set (α × α)).InjOn Prod.snd

/-- Explicit characterization of an order matching on `s` for a binary relation `r`. -/
theorem isOrderMatching_iff {s : Finset α} {r : α → α → Prop} {E : Finset (α × α)} :
    s.IsOrderMatching r E ↔
      (∀ e ∈ E, e.1 ∈ s ∧ e.2 ∈ s ∧ r e.1 e.2) ∧
      (∀ e ∈ E, ∀ f ∈ E, e.1 = f.1 → e = f) ∧
      (∀ e ∈ E, ∀ f ∈ E, e.2 = f.2 → e = f) :=
  ⟨fun h ↦ ⟨fun _ he ↦ ⟨h.fst_mem he, h.snd_mem he, h.rel he⟩, h.injOn_fst, h.injOn_snd⟩,
    fun ⟨hmem, hfst, hsnd⟩ ↦
      ⟨fun _ he ↦ (hmem _ he).1, fun _ he ↦ (hmem _ he).2.1, fun _ he ↦ (hmem _ he).2.2,
        fun _ he _ hf ↦ hfst _ he _ hf, fun _ he _ hf ↦ hsnd _ he _ hf⟩⟩

@[simp]
theorem isOrderMatching_empty (s : Finset α) (r : α → α → Prop) : s.IsOrderMatching r ∅ := by
  simp [isOrderMatching_iff]

/-- The only order matching on the empty set is the empty matching. -/
@[simp]
theorem empty_isOrderMatching_iff {r : α → α → Prop} {E : Finset (α × α)} :
    (∅ : Finset α).IsOrderMatching r E ↔ E = ∅ :=
  ⟨fun h ↦ eq_empty_iff_forall_notMem.mpr fun _ he ↦ notMem_empty _ (h.fst_mem he),
    fun h ↦ h ▸ isOrderMatching_empty ∅ r⟩

@[simp]
theorem isOrderMatching_singleton_iff {s : Finset α} {r : α → α → Prop} {e : α × α} :
    s.IsOrderMatching r {e} ↔ e.1 ∈ s ∧ e.2 ∈ s ∧ r e.1 e.2 := by
  simp [isOrderMatching_iff]

/-- Any subset of an order matching is an order matching. -/
theorem IsOrderMatching.subset {s : Finset α} {r : α → α → Prop} {E E' : Finset (α × α)}
    (hE : s.IsOrderMatching r E) (h : E' ⊆ E) : s.IsOrderMatching r E' :=
  ⟨fun _ he ↦ hE.fst_mem (h he), fun _ he ↦ hE.snd_mem (h he), fun _ he ↦ hE.rel (h he),
    hE.injOn_fst.mono (coe_subset.mpr h), hE.injOn_snd.mono (coe_subset.mpr h)⟩

/-- An order matching on `s` remains an order matching on any superset of `s`. -/
theorem IsOrderMatching.mono {s t : Finset α} {r : α → α → Prop} {E : Finset (α × α)}
    (hE : s.IsOrderMatching r E) (h : s ⊆ t) : t.IsOrderMatching r E :=
  ⟨fun _ he ↦ h (hE.fst_mem he), fun _ he ↦ h (hE.snd_mem he), hE.rel, hE.injOn_fst, hE.injOn_snd⟩

/-- Every edge of an order matching on `s` lies in `s ×ˢ s`. -/
theorem IsOrderMatching.subset_product {s : Finset α} {r : α → α → Prop} {E : Finset (α × α)}
    (hE : s.IsOrderMatching r E) : E ⊆ s ×ˢ s := fun _ he ↦
  mem_product.mpr ⟨hE.fst_mem he, hE.snd_mem he⟩

/-- An order matching on `s` has at most `s.card` edges. -/
theorem IsOrderMatching.card_le_card {s : Finset α} {r : α → α → Prop} {E : Finset (α × α)}
    (hE : s.IsOrderMatching r E) : E.card ≤ s.card :=
  Finset.card_le_card_of_injOn Prod.fst hE.fst_mem hE.injOn_fst

/-- `insert (a, b) E` is an order matching on `s` for `r` if and only if `E` is an order matching
on `s` for `r`, `a ∈ s`, `b ∈ s`, `r a b`, and no distinct edge in `E` has left endpoint `a` or
right endpoint `b`. -/
theorem isOrderMatching_insert_iff [DecidableEq α] {s : Finset α} {r : α → α → Prop}
    {E : Finset (α × α)} {a b : α} :
    s.IsOrderMatching r (insert (a, b) E) ↔
      s.IsOrderMatching r E ∧ a ∈ s ∧ b ∈ s ∧ r a b ∧
      (∀ e ∈ E, e.1 = a → e = (a, b)) ∧ (∀ e ∈ E, e.2 = b → e = (a, b)) := by
  by_cases habE : (a, b) ∈ E
  · rw [insert_eq_of_mem habE]
    exact ⟨fun h ↦ ⟨h, h.fst_mem habE, h.snd_mem habE, h.rel habE,
      fun _ he ↦ h.injOn_fst he habE, fun _ he ↦ h.injOn_snd he habE⟩, And.left⟩
  · have hnot : (a, b) ∉ (E : Set (α × α)) := mem_coe.not.mpr habE
    have hinj {p : α × α → α} :
        ((insert (a, b) E : Finset (α × α)) : Set (α × α)).InjOn p ↔
          (E : Set (α × α)).InjOn p ∧ ∀ e ∈ E, p e = p (a, b) → e = (a, b) := by
      rw [coe_insert, Set.injOn_insert hnot]
      exact and_congr_right fun _ ↦
        ⟨fun h e he hp ↦ absurd ⟨e, he, hp⟩ h, fun h ⟨e, he, hp⟩ ↦ habE (h e he hp ▸ he)⟩
    constructor
    · intro h
      exact ⟨h.subset (subset_insert _ _), h.fst_mem (mem_insert_self _ _),
        h.snd_mem (mem_insert_self _ _), h.rel (mem_insert_self _ _),
        (hinj.mp h.injOn_fst).2, (hinj.mp h.injOn_snd).2⟩
    · rintro ⟨hE, has, hbs, hab, hfst, hsnd⟩
      exact ⟨(forall_mem_insert _ _ _).mpr ⟨has, fun _ he ↦ hE.fst_mem he⟩,
        (forall_mem_insert _ _ _).mpr ⟨hbs, fun _ he ↦ hE.snd_mem he⟩,
        (forall_mem_insert _ _ _).mpr ⟨hab, fun _ he ↦ hE.rel he⟩,
        hinj.mpr ⟨hE.injOn_fst, hfst⟩, hinj.mpr ⟨hE.injOn_snd, hsnd⟩⟩

/-- Relation embeddings preserve and reflect order matchings. -/
@[simp]
theorem isOrderMatching_map_iff {β : Type*} {r : α → α → Prop} {r' : β → β → Prop}
    {s : Finset α} {E : Finset (α × α)} (f : r ↪r r') :
    (s.map f.toEmbedding).IsOrderMatching r' (E.map (f.toEmbedding.prodMap f.toEmbedding)) ↔
      s.IsOrderMatching r E := by
  let ff : α × α ↪ β × β := f.toEmbedding.prodMap f.toEmbedding
  have hff : (ff : α × α → β × β) = Prod.map f f := by
    dsimp only [ff]
    rw [Function.Embedding.coe_prodMap, RelEmbedding.coe_toEmbedding]
  have hinj (p : β × β → β) (q : α × α → α) (hpq : p ∘ ff = f ∘ q) :
      ((E.map ff : Finset (β × β)) : Set (β × β)).InjOn p ↔
        (E : Set (α × α)).InjOn q := by
    rw [coe_map, ← ff.injective.injOn.comp_iff, hpq]
    exact ⟨Set.InjOn.of_comp, f.injective.comp_injOn⟩
  have hfst := hinj Prod.fst Prod.fst (by rw [hff, Prod.map_fst'])
  have hsnd := hinj Prod.snd Prod.snd (by rw [hff, Prod.map_snd'])
  refine ⟨fun h ↦ ⟨?_, ?_, ?_, hfst.mp h.injOn_fst, hsnd.mp h.injOn_snd⟩,
    fun h ↦ ⟨?_, ?_, ?_, hfst.mpr h.injOn_fst, hsnd.mpr h.injOn_snd⟩⟩
  · exact fun _ he ↦ (mem_map' f.toEmbedding).mp (h.fst_mem (mem_map_of_mem ff he))
  · exact fun _ he ↦ (mem_map' f.toEmbedding).mp (h.snd_mem (mem_map_of_mem ff he))
  · exact fun _ he ↦ f.map_rel_iff.mp (h.rel (mem_map_of_mem ff he))
  · intro _ he
    obtain ⟨p, hp, rfl⟩ := mem_map.mp he
    exact mem_map_of_mem f.toEmbedding (h.fst_mem hp)
  · intro _ he
    obtain ⟨p, hp, rfl⟩ := mem_map.mp he
    exact mem_map_of_mem f.toEmbedding (h.snd_mem hp)
  · intro _ he
    obtain ⟨p, hp, rfl⟩ := mem_map.mp he
    exact f.map_rel_iff.mpr (h.rel hp)

open scoped Classical in
/-- The maximum number of edges in an `r`-order matching on `s`. -/
noncomputable def orderMatchingNumber (s : Finset α) (r : α → α → Prop) : ℕ :=
  ((s ×ˢ s).powerset.filter (s.IsOrderMatching r)).sup Finset.card

/-- Every `r`-order matching on `s` has at most `s.orderMatchingNumber r` edges. -/
theorem card_le_orderMatchingNumber {s : Finset α} {r : α → α → Prop} {E : Finset (α × α)}
    (hE : s.IsOrderMatching r E) : E.card ≤ s.orderMatchingNumber r := by
  classical
  exact Finset.le_sup (f := Finset.card)
    (mem_filter.mpr ⟨mem_powerset.mpr hE.subset_product, hE⟩)

/-- `s.orderMatchingNumber r ≤ n` if and only if every `r`-order matching on `s` has at most `n`
edges. -/
theorem orderMatchingNumber_le_iff {s : Finset α} {r : α → α → Prop} {n : ℕ} :
    s.orderMatchingNumber r ≤ n ↔ ∀ E, s.IsOrderMatching r E → E.card ≤ n := by
  classical
  simp only [orderMatchingNumber, Finset.sup_le_iff, mem_filter, mem_powerset, and_imp]
  exact ⟨fun h E hE ↦ h E hE.subset_product hE, fun h E _ hE ↦ h E hE⟩

/-- Some `r`-order matching on `s` attains `s.orderMatchingNumber r`. -/
theorem exists_isOrderMatching_card_eq_orderMatchingNumber (s : Finset α) (r : α → α → Prop) :
    ∃ E, s.IsOrderMatching r E ∧ E.card = s.orderMatchingNumber r := by
  classical
  have hne : ((s ×ˢ s).powerset.filter (s.IsOrderMatching r)).Nonempty :=
    ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _), isOrderMatching_empty s r⟩⟩
  obtain ⟨E, hE, hEq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  exact ⟨E, (mem_filter.mp hE).2, hEq.symm⟩

/-- `n ≤ s.orderMatchingNumber r` if and only if some `r`-order matching on `s` has at least `n`
edges. -/
theorem le_orderMatchingNumber_iff {s : Finset α} {r : α → α → Prop} {n : ℕ} :
    n ≤ s.orderMatchingNumber r ↔ ∃ E, s.IsOrderMatching r E ∧ n ≤ E.card := by
  refine ⟨fun h ↦ ?_, fun ⟨_, hE, hn⟩ ↦ hn.trans (card_le_orderMatchingNumber hE)⟩
  obtain ⟨E, hE, hcard⟩ := s.exists_isOrderMatching_card_eq_orderMatchingNumber r
  exact ⟨E, hE, hcard.symm ▸ h⟩

/-- The `r`-order matching number of `s` is zero if and only if no pair of elements in `s` is
related by `r`. -/
theorem orderMatchingNumber_eq_zero_iff {s : Finset α} {r : α → α → Prop} :
    s.orderMatchingNumber r = 0 ↔ ∀ a ∈ s, ∀ b ∈ s, ¬ r a b := by
  constructor
  · intro h a ha b hb hr
    have h1 : 1 ≤ s.orderMatchingNumber r :=
      (card_singleton (a, b)) ▸ card_le_orderMatchingNumber
        (isOrderMatching_singleton_iff.mpr ⟨ha, hb, hr⟩)
    omega
  · intro hno
    apply Nat.eq_zero_of_le_zero
    rw [orderMatchingNumber_le_iff]
    intro E hE
    have hEempty : E = ∅ := eq_empty_iff_forall_notMem.mpr fun _ he ↦
      hno _ (hE.fst_mem he) _ (hE.snd_mem he) (hE.rel he)
    simp [hEempty]

/-- The `r`-order matching number of `s` is positive if and only if `s` contains an `r`-related
pair. -/
theorem orderMatchingNumber_pos_iff {s : Finset α} {r : α → α → Prop} :
    0 < s.orderMatchingNumber r ↔ ∃ a ∈ s, ∃ b ∈ s, r a b := by
  rw [Nat.pos_iff_ne_zero, ne_eq, orderMatchingNumber_eq_zero_iff]
  push Not
  rfl

@[simp]
theorem orderMatchingNumber_empty (r : α → α → Prop) :
    (∅ : Finset α).orderMatchingNumber r = 0 :=
  orderMatchingNumber_eq_zero_iff.mpr fun _ h ↦ absurd h (notMem_empty _)

@[simp]
theorem orderMatchingNumber_singleton (a : α) (r : α → α → Prop) [Std.Irrefl r] :
    ({a} : Finset α).orderMatchingNumber r = 0 :=
  orderMatchingNumber_eq_zero_iff.mpr fun _ hx _ hy hr ↦
    irrefl a (mem_singleton.mp hx ▸ mem_singleton.mp hy ▸ hr)

/-- The `r`-order matching number of `s` is at most the cardinality of `s`. -/
theorem orderMatchingNumber_le_card (s : Finset α) (r : α → α → Prop) :
    s.orderMatchingNumber r ≤ s.card :=
  orderMatchingNumber_le_iff.mpr fun _ hE ↦ hE.card_le_card

/-- The `r`-order matching number is monotone under set inclusion. -/
theorem orderMatchingNumber_mono {s t : Finset α} {r : α → α → Prop} (h : s ⊆ t) :
    s.orderMatchingNumber r ≤ t.orderMatchingNumber r :=
  orderMatchingNumber_le_iff.mpr fun _ hE ↦ card_le_orderMatchingNumber (hE.mono h)

/-- Relation embeddings preserve the order matching number. -/
@[simp]
theorem orderMatchingNumber_map {β : Type*} {r : α → α → Prop} {r' : β → β → Prop} (s : Finset α)
    (f : r ↪r r') :
    (s.map f.toEmbedding).orderMatchingNumber r' = s.orderMatchingNumber r := by
  apply le_antisymm
  · rw [orderMatchingNumber_le_iff]
    intro F hF
    obtain ⟨E, -, rfl⟩ := Finset.subset_map_iff.mp
      ((Finset.prodMap_map_product f.toEmbedding f.toEmbedding s s).symm ▸ hF.subset_product)
    simpa using card_le_orderMatchingNumber ((isOrderMatching_map_iff f).mp hF)
  · rw [orderMatchingNumber_le_iff]
    intro E hE
    simpa using card_le_orderMatchingNumber ((isOrderMatching_map_iff f).mpr hE)

/-- In an irreflexive relation `r`, `s` has `r`-order matching number zero if and only if `s` is an
`r`-antichain. -/
theorem orderMatchingNumber_eq_zero_iff_isAntichain {s : Finset α} {r : α → α → Prop}
    [Std.Irrefl r] : s.orderMatchingNumber r = 0 ↔ IsAntichain r (s : Set α) := by
  rw [orderMatchingNumber_eq_zero_iff]
  refine ⟨fun h _ ha _ hb _ ↦ h _ ha _ hb, fun hs _ ha b hb hr ↦ ?_⟩
  exact hs ha hb (fun h ↦ irrefl b (h ▸ hr)) hr

end Basic

end Finset

section ChainMatchingBridge

/-- In an `r`-order matching `E` on `t` with `E.card + 1 = t.card`, unmatched right endpoint `a`,
and unmatched left endpoint `b`, any subset `B ⊆ t` containing `a` and omitting `b` has an edge of
`E` leaving `B`. -/
private theorem exists_crossing_edge_of_isOrderMatching {α : Type*} {r : α → α → Prop}
    {t B : Finset α} {E : Finset (α × α)} {a b : α} (hE : t.IsOrderMatching r E)
    (hcard : E.card + 1 = t.card) (hbt : b ∈ t) (ha_in : ∀ e ∈ E, e.2 ≠ a)
    (hb_out : ∀ e ∈ E, e.1 ≠ b) (hBt : B ⊆ t) (haB : a ∈ B) (hbB : b ∉ B) :
    ∃ e ∈ E, e.1 ∈ B ∧ e.2 ∉ B := by
  classical
  by_contra hno
  have hclosed : ∀ e ∈ E, e.1 ∈ B → e.2 ∈ B := fun e he h1 ↦ by
    by_contra h2
    exact hno ⟨e, he, h1, h2⟩
  have hmaps : Set.MapsTo Prod.fst (E : Set (α × α)) ((t.erase b : Finset α) : Set α) :=
    fun _ he ↦ Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hb_out _ he, hE.fst_mem he⟩)
  have hcard_le : (t.erase b).card ≤ E.card := by
    rw [Finset.card_erase_of_mem hbt]
    omega
  have hsurj := Finset.surjOn_of_injOn_of_card_le Prod.fst hmaps hE.injOn_fst hcard_le
  have hle : B.card ≤ (B.erase a).card :=
    Finset.card_le_card_of_forall_subsingleton (fun x y ↦ (x, y) ∈ E)
      (fun x hx ↦ by
        obtain ⟨⟨u, y⟩, huy, rfl⟩ :=
          hsurj (Finset.mem_erase.mpr ⟨fun hxb ↦ hbB (hxb ▸ hx), hBt hx⟩)
        exact ⟨y, Finset.mem_erase.mpr ⟨ha_in (u, y) huy, hclosed (u, y) huy hx⟩, huy⟩)
      (fun _ _ _ hx₁ _ hx₂ ↦ congrArg Prod.fst (hE.injOn_snd hx₁.2 hx₂.2 rfl))
  have hlt : (B.erase a).card < B.card := Finset.card_erase_lt_of_mem haB
  omega

/-- Inserting `(x, z)` into an `r`-order matching `E` on `t` when `x, z ∈ t`, `r x z`, and no edge
of `E` uses `x` as a left endpoint or `z` as a right endpoint produces an `r`-order matching on `t`
with one additional edge. -/
private theorem isOrderMatching_insert_of_unused {α : Type*} {r : α → α → Prop} [DecidableEq α]
    {t : Finset α} {E : Finset (α × α)} {x z : α}
    (hE : t.IsOrderMatching r E) (hx : x ∈ t) (hz : z ∈ t) (hr : r x z)
    (hleft : ∀ e ∈ E, e.1 ≠ x) (hright : ∀ e ∈ E, e.2 ≠ z) :
    t.IsOrderMatching r (insert (x, z) E) ∧ (insert (x, z) E).card = E.card + 1 :=
  ⟨Finset.isOrderMatching_insert_iff.mpr
      ⟨hE, hx, hz, hr, fun e he h ↦ (hleft e he h).elim, fun e he h ↦ (hright e he h).elim⟩,
    Finset.card_insert_of_notMem fun h ↦ hleft (x, z) h rfl⟩

/-- Replacing an edge `(u, v) ∈ E` by `(u, y)` and `(y, v)` for a fresh vertex `y ∉ t` with
`r u y` and `r y v` yields an `r`-order matching on `insert y t` with one additional edge and the
same unmatched endpoints `a` and `b`. -/
private theorem isOrderMatching_split_edge {α : Type*} {r : α → α → Prop} [DecidableEq α]
    {t : Finset α} {E : Finset (α × α)} {y u v a b : α}
    (hE : t.IsOrderMatching r E) (hyt : y ∉ t) (huv : (u, v) ∈ E) (huy : r u y) (hyv : r y v)
    (hat : a ∈ t) (hbt : b ∈ t) (ha_in : ∀ e ∈ E, e.2 ≠ a) (hb_out : ∀ e ∈ E, e.1 ≠ b) :
    let E' := insert (u, y) (insert (y, v) (E.erase (u, v)))
    (insert y t).IsOrderMatching r E' ∧ E'.card = E.card + 1 ∧
      (∀ e ∈ E', e.2 ≠ a) ∧ (∀ e ∈ E', e.1 ≠ b) := by
  have hu : u ∈ t := hE.fst_mem huv
  have hv : v ∈ t := hE.snd_mem huv
  obtain ⟨hE1, hcard1⟩ := isOrderMatching_insert_of_unused
    ((hE.subset (Finset.erase_subset _ _)).mono (Finset.subset_insert _ _))
    (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hv) hyv
    (fun e he he1 ↦ hyt (he1 ▸ hE.fst_mem (Finset.mem_erase.mp he).2))
    (fun e he he2 ↦ (Finset.mem_erase.mp he).1
      (hE.injOn_snd (Finset.mem_erase.mp he).2 huv he2))
  obtain ⟨hE2, hcard2⟩ := isOrderMatching_insert_of_unused hE1
    (Finset.mem_insert_of_mem hu) (Finset.mem_insert_self _ _) huy
    (fun e he he1 ↦ by
      rcases Finset.mem_insert.mp he with rfl | he'
      · dsimp at he1; exact hyt (he1.symm ▸ hu)
      · exact (Finset.mem_erase.mp he').1 (hE.injOn_fst (Finset.mem_erase.mp he').2 huv he1))
    (fun e he he2 ↦ by
      rcases Finset.mem_insert.mp he with rfl | he'
      · dsimp at he2; exact hyt (he2 ▸ hv)
      · exact hyt (he2 ▸ hE.snd_mem (Finset.mem_erase.mp he').2))
  refine ⟨hE2, ?_, fun e he ↦ ?_, fun e he ↦ ?_⟩
  · have : 1 ≤ E.card := Finset.card_pos.mpr ⟨(u, v), huv⟩
    rw [hcard2, hcard1, Finset.card_erase_of_mem huv]
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
extends an `r`-order matching on `t` to `insert y t`. -/
private theorem isOrderMatching_prepend_edge {α : Type*} {r : α → α → Prop} [DecidableEq α]
    {t : Finset α} {E : Finset (α × α)} {y a b : α}
    (hE : t.IsOrderMatching r E) (hyt : y ∉ t) (hat : a ∈ t) (hbt : b ∈ t) (hya : r y a)
    (ha_in : ∀ e ∈ E, e.2 ≠ a) (hb_out : ∀ e ∈ E, e.1 ≠ b) :
    (insert y t).IsOrderMatching r (insert (y, a) E) ∧ (insert (y, a) E).card = E.card + 1 ∧
      (∀ e ∈ insert (y, a) E, e.2 ≠ y) ∧ (∀ e ∈ insert (y, a) E, e.1 ≠ b) := by
  obtain ⟨hE', hcard'⟩ := isOrderMatching_insert_of_unused
    (hE.mono (Finset.subset_insert _ _)) (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem hat) hya (fun _ he h ↦ hyt (h ▸ hE.fst_mem he)) ha_in
  refine ⟨hE', hcard', fun e he h ↦ ?_, fun e he h ↦ ?_⟩
  · rcases Finset.mem_insert.mp he with rfl | he'
    · dsimp at h; exact hyt (h ▸ hat)
    · exact hyt (h ▸ hE.snd_mem he')
  · rcases Finset.mem_insert.mp he with rfl | he'
    · dsimp at h; exact hyt (h.symm ▸ hbt)
    · exact hb_out e he' h

/-- Appending an edge `(b, y)` from an unmatched left endpoint `b ∈ t` to a fresh vertex `y ∉ t`
extends an `r`-order matching on `t` to `insert y t`. -/
private theorem isOrderMatching_append_edge {α : Type*} {r : α → α → Prop} [DecidableEq α]
    {t : Finset α} {E : Finset (α × α)} {y a b : α}
    (hE : t.IsOrderMatching r E) (hyt : y ∉ t) (hat : a ∈ t) (hbt : b ∈ t) (hby : r b y)
    (ha_in : ∀ e ∈ E, e.2 ≠ a) (hb_out : ∀ e ∈ E, e.1 ≠ b) :
    (insert y t).IsOrderMatching r (insert (b, y) E) ∧ (insert (b, y) E).card = E.card + 1 ∧
      (∀ e ∈ insert (b, y) E, e.2 ≠ a) ∧ (∀ e ∈ insert (b, y) E, e.1 ≠ y) := by
  obtain ⟨hE', hcard'⟩ := isOrderMatching_insert_of_unused
    (hE.mono (Finset.subset_insert _ _)) (Finset.mem_insert_of_mem hbt)
    (Finset.mem_insert_self _ _) hby hb_out (fun _ he h ↦ hyt (h ▸ hE.snd_mem he))
  refine ⟨hE', hcard', fun e he h ↦ ?_, fun e he h ↦ ?_⟩
  · rcases Finset.mem_insert.mp he with rfl | he'
    · dsimp at h; exact hyt (h.symm ▸ hat)
    · exact ha_in e he' h
  · rcases Finset.mem_insert.mp he with rfl | he'
    · dsimp at h; exact hyt (h ▸ hbt)
    · exact hyt (h ▸ hE.fst_mem he')

/-- A nonempty finite `r`-chain `c` (for any binary relation `r`, not necessarily transitive) admits
an `r`-order matching on `c` with `c.card - 1` edges, proved by Rédei's edge-splitting induction. -/
theorem IsChain.exists_isOrderMatching_card_add_one {α : Type*} {r : α → α → Prop} {c : Finset α}
    (hchain : IsChain r (c : Set α)) (hc : c.Nonempty) :
    ∃ E, c.IsOrderMatching r E ∧ E.card + 1 = c.card := by
  classical
  suffices ∃ (E : Finset (α × α)) (a b : α),
      c.IsOrderMatching r E ∧ E.card + 1 = c.card ∧
      a ∈ c ∧ b ∈ c ∧ (∀ e ∈ E, e.2 ≠ a) ∧ (∀ e ∈ E, e.1 ≠ b) by
    obtain ⟨E, _, _, hE, hcard, -, -, -, -⟩ := this
    exact ⟨E, hE, hcard⟩
  induction hc using Finset.Nonempty.cons_induction with
  | singleton x =>
    exact ⟨∅, x, x, Finset.isOrderMatching_empty _ r, by simp, Finset.mem_singleton_self x,
      Finset.mem_singleton_self x, by simp, by simp⟩
  | @cons y t hyt _ ih =>
    rw [Finset.cons_eq_insert] at hchain ⊢
    obtain ⟨E, a, b, hE, hcard, hat, hbt, ha_in, hb_out⟩ :=
      ih (hchain.mono (Finset.coe_subset.mpr (Finset.subset_insert y t)))
    by_cases h1 : r y a
    · obtain ⟨hE', hcard', ha', hb'⟩ :=
        isOrderMatching_prepend_edge hE hyt hat hbt h1 ha_in hb_out
      exact ⟨_, y, b, hE', by rw [hcard', Finset.card_insert_of_notMem hyt]; omega,
        Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hbt, ha', hb'⟩
    · by_cases h2 : r b y
      · obtain ⟨hE', hcard', ha', hb'⟩ :=
          isOrderMatching_append_edge hE hyt hat hbt h2 ha_in hb_out
        exact ⟨_, a, y, hE', by rw [hcard', Finset.card_insert_of_notMem hyt]; omega,
          Finset.mem_insert_of_mem hat, Finset.mem_insert_self _ _, ha', hb'⟩
      · have hay : r a y := (hchain (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hat)
          (fun h ↦ hyt (h ▸ hat))).resolve_left h1
        obtain ⟨⟨u, v⟩, huv, huB, hvB⟩ := exists_crossing_edge_of_isOrderMatching hE hcard hbt ha_in
          hb_out (Finset.filter_subset (r · y) t) (Finset.mem_filter.mpr ⟨hat, hay⟩)
          (fun h ↦ h2 (Finset.mem_filter.mp h).2)
        have hv_t : v ∈ t := hE.snd_mem huv
        have hyv : r y v := (hchain (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hv_t)
          (fun h ↦ hyt (h ▸ hv_t))).resolve_right (fun h ↦ hvB (Finset.mem_filter.mpr ⟨hv_t, h⟩))
        obtain ⟨hE', hcard', ha', hb'⟩ := isOrderMatching_split_edge hE hyt huv
          (Finset.mem_filter.mp huB).2 hyv hat hbt ha_in hb_out
        exact ⟨_, a, b, hE', by rw [hcard', Finset.card_insert_of_notMem hyt]; omega,
          Finset.mem_insert_of_mem hat, Finset.mem_insert_of_mem hbt, ha', hb'⟩

namespace Finset

/-- Every pairwise-disjoint partition `C` of `s` into nonempty `r`-chains yields an `r`-order
matching `E` on `s` satisfying `E.card + C.card = s.card`. -/
theorem exists_isOrderMatching_of_chainPartition {α : Type*} {r : α → α → Prop} [DecidableEq α]
    {s : Finset α} {C : Finset (Finset α)}
    (hC : ∀ c ∈ C, c.Nonempty ∧ IsChain r (c : Set α))
    (hdisj : (C : Set (Finset α)).Pairwise Disjoint)
    (hcov : C.biUnion id = s) :
    ∃ E, s.IsOrderMatching r E ∧ E.card + C.card = s.card := by
  classical
  let edgeOf : Finset α → Finset (α × α) := fun c ↦
    if hc : c ∈ C then ((hC c hc).2.exists_isOrderMatching_card_add_one (hC c hc).1).choose else ∅
  have hedge : ∀ c ∈ C, c.IsOrderMatching r (edgeOf c) ∧ (edgeOf c).card + 1 = c.card :=
    fun c hc ↦ by
      simpa only [edgeOf, hc, ↓reduceDIte] using
        ((hC c hc).2.exists_isOrderMatching_card_add_one (hC c hc).1).choose_spec
  have hsame (p : α × α → α) (hp_mem : ∀ c ∈ C, ∀ e ∈ edgeOf c, p e ∈ c)
      {c₁ c₂} (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C) {e₁ e₂ : α × α}
      (h₁ : e₁ ∈ edgeOf c₁) (h₂ : e₂ ∈ edgeOf c₂) (heq : p e₁ = p e₂) : c₁ = c₂ := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj hc₁ hc₂ hne)
      (hp_mem c₁ hc₁ e₁ h₁) (heq ▸ hp_mem c₂ hc₂ e₂ h₂)
  have hdisjE : (C : Set (Finset α)).PairwiseDisjoint edgeOf := fun c₁ hc₁ c₂ hc₂ hne ↦
    Finset.disjoint_left.mpr fun _ he₁ he₂ ↦
      hne (hsame Prod.fst (fun c hc _ he ↦ (hedge c hc).1.fst_mem he) hc₁ hc₂ he₁ he₂ rfl)
  have hinjOn (p : α × α → α) (hp_mem : ∀ c ∈ C, ∀ e ∈ edgeOf c, p e ∈ c)
      (hp_inj : ∀ c ∈ C, ((edgeOf c : Finset (α × α)) : Set (α × α)).InjOn p) :
      ((C.biUnion edgeOf : Finset (α × α)) : Set (α × α)).InjOn p := by
    intro _ he₁ _ he₂ heq
    obtain ⟨c₁, hc₁, h₁⟩ := mem_biUnion.mp (mem_coe.mp he₁)
    obtain ⟨c₂, hc₂, h₂⟩ := mem_biUnion.mp (mem_coe.mp he₂)
    obtain rfl := hsame p hp_mem hc₁ hc₂ h₁ h₂ heq
    exact hp_inj c₁ hc₁ h₁ h₂ heq
  refine ⟨C.biUnion edgeOf, ⟨?_, ?_, ?_,
    hinjOn Prod.fst (fun c hc _ he ↦ (hedge c hc).1.fst_mem he)
      fun c hc ↦ (hedge c hc).1.injOn_fst,
    hinjOn Prod.snd (fun c hc _ he ↦ (hedge c hc).1.snd_mem he)
      fun c hc ↦ (hedge c hc).1.injOn_snd⟩,
    ?_⟩
  · intro _ he
    obtain ⟨c, hc, hec⟩ := mem_biUnion.mp he
    exact (hcov ▸ subset_biUnion_of_mem id hc) ((hedge c hc).1.fst_mem hec)
  · intro _ he
    obtain ⟨c, hc, hec⟩ := mem_biUnion.mp he
    exact (hcov ▸ subset_biUnion_of_mem id hc) ((hedge c hc).1.snd_mem hec)
  · intro _ he
    obtain ⟨c, hc, hec⟩ := mem_biUnion.mp he
    exact (hedge c hc).1.rel hec
  · have hdisjId : (C : Set (Finset α)).PairwiseDisjoint id := hdisj
    rw [card_biUnion hdisjE, ← hcov, card_biUnion hdisjId]
    calc
      ∑ c ∈ C, (edgeOf c).card + C.card = ∑ c ∈ C, ((edgeOf c).card + 1) := by
        simp [Finset.sum_add_distrib]
      _ = ∑ c ∈ C, (id c).card := Finset.sum_congr rfl fun c hc ↦ (hedge c hc).2

/-- Endpoint invariants after merging `cₐ` and `c_b` along an edge `(a, b)` in a strict order `r`:
every unmatched left endpoint remains strictly greatest in its chain, and every unmatched right
endpoint remains strictly least in its chain. -/
private theorem merge_strictChain_endpoints {α : Type*} {r : α → α → Prop} [IsStrictOrder α r]
    [DecidableEq α] {E : Finset (α × α)} {C : Finset (Finset α)} {a b : α} {cₐ c_b : Finset α}
    (hmax : ∀ c ∈ C, ∀ x ∈ c, (∀ e ∈ E, e.1 ≠ x) → ∀ u ∈ c, u ≠ x → r u x)
    (hmin : ∀ c ∈ C, ∀ x ∈ c, (∀ e ∈ E, e.2 ≠ x) → ∀ v ∈ c, v ≠ x → r x v)
    (hcₐ : cₐ ∈ C) (ha : a ∈ cₐ) (ha_top : ∀ u ∈ cₐ, u ≠ a → r u a)
    (hc_b : c_b ∈ C) (hb : b ∈ c_b) (hb_bot : ∀ v ∈ c_b, v ≠ b → r b v)
    (hcross : ∀ u ∈ cₐ, ∀ v ∈ c_b, r u v) :
    let C' := insert (cₐ ∪ c_b) ((C.erase cₐ).erase c_b)
    (∀ c ∈ C', ∀ x ∈ c, (∀ e ∈ insert (a, b) E, e.1 ≠ x) → ∀ u ∈ c, u ≠ x → r u x) ∧
    (∀ c ∈ C', ∀ x ∈ c, (∀ e ∈ insert (a, b) E, e.2 ≠ x) → ∀ v ∈ c, v ≠ x → r x v) := by
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

/-- Merging the chain ending at `a` and the chain starting at `b` along an edge `r a b` produces an
`r`-chain whose strictly greatest and least elements stay unmatched. -/
private theorem merge_strictChain_step {α : Type*} {r : α → α → Prop} [IsStrictOrder α r]
    [DecidableEq α] {s : Finset α} {E : Finset (α × α)} {C : Finset (Finset α)} {a b : α}
    {cₐ c_b : Finset α} (hab : r a b) (hC : ∀ c ∈ C, c.Nonempty ∧ IsChain r (c : Set α))
    (hdisj : (C : Set (Finset α)).Pairwise Disjoint) (hcov : C.biUnion id = s)
    (hcard : E.card + C.card = s.card)
    (hmax : ∀ c ∈ C, ∀ x ∈ c, (∀ e ∈ E, e.1 ≠ x) → ∀ u ∈ c, u ≠ x → r u x)
    (hmin : ∀ c ∈ C, ∀ x ∈ c, (∀ e ∈ E, e.2 ≠ x) → ∀ v ∈ c, v ≠ x → r x v)
    (hcₐ : cₐ ∈ C) (ha : a ∈ cₐ) (ha_out : ∀ e ∈ E, e.1 ≠ a)
    (hc_b : c_b ∈ C) (hb : b ∈ c_b) (hb_in : ∀ e ∈ E, e.2 ≠ b) :
    ∃ C' : Finset (Finset α),
      (∀ c ∈ C', c.Nonempty ∧ IsChain r (c : Set α)) ∧
      (C' : Set (Finset α)).Pairwise Disjoint ∧
      C'.biUnion id = s ∧
      (insert (a, b) E).card + C'.card = s.card ∧
      (∀ c ∈ C', ∀ x ∈ c, (∀ e ∈ insert (a, b) E, e.1 ≠ x) → ∀ u ∈ c, u ≠ x → r u x) ∧
      (∀ c ∈ C', ∀ x ∈ c, (∀ e ∈ insert (a, b) E, e.2 ≠ x) → ∀ v ∈ c, v ≠ x → r x v) := by
  have ha_top : ∀ u ∈ cₐ, u ≠ a → r u a := hmax cₐ hcₐ a ha ha_out
  have hb_bot : ∀ v ∈ c_b, v ≠ b → r b v := hmin c_b hc_b b hb hb_in
  have hne_c : cₐ ≠ c_b := fun h ↦
    asymm hab (ha_top b (h ▸ hb) fun hba ↦ irrefl a (hba ▸ hab))
  have hcross : ∀ u ∈ cₐ, ∀ v ∈ c_b, r u v := fun u hu v hv ↦ by
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
    have hab_notMem : (a, b) ∉ E := fun he ↦ ha_out (a, b) he rfl
    rw [card_insert_of_notMem hab_notMem, card_insert_of_notMem hunion_notMem]
    omega

/-- Every `r`-order matching `E` on `s` in a strict order `r` yields a pairwise-disjoint partition
`C` of `s` into nonempty `r`-chains satisfying `E.card + C.card = s.card`. -/
theorem IsOrderMatching.exists_chainPartition {α : Type*} {r : α → α → Prop} [IsStrictOrder α r]
    [DecidableEq α] {s : Finset α} {E : Finset (α × α)} (hE : s.IsOrderMatching r E) :
    ∃ C : Finset (Finset α),
      (∀ c ∈ C, c.Nonempty ∧ IsChain r (c : Set α)) ∧
      (C : Set (Finset α)).Pairwise Disjoint ∧
      C.biUnion id = s ∧ E.card + C.card = s.card := by
  suffices ∃ C : Finset (Finset α),
      (∀ c ∈ C, c.Nonempty ∧ IsChain r (c : Set α)) ∧
      (C : Set (Finset α)).Pairwise Disjoint ∧
      C.biUnion id = s ∧ E.card + C.card = s.card ∧
      (∀ c ∈ C, ∀ x ∈ c, (∀ e ∈ E, e.1 ≠ x) → ∀ u ∈ c, u ≠ x → r u x) ∧
      (∀ c ∈ C, ∀ x ∈ c, (∀ e ∈ E, e.2 ≠ x) → ∀ v ∈ c, v ≠ x → r x v) by
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

/-- Weak duality between order matchings and antichains: in a strict order `r`,
`E.card + A.card ≤ s.card` whenever `E` is an `r`-order matching on `s` and `A ⊆ s` is an
`r`-antichain. -/
theorem IsOrderMatching.card_add_card_le_of_isAntichain {α : Type*} {r : α → α → Prop}
    [IsStrictOrder α r] {s A : Finset α} {E : Finset (α × α)}
    (hE : s.IsOrderMatching r E) (hAs : A ⊆ s) (hA : IsAntichain r (A : Set α)) :
    E.card + A.card ≤ s.card := by
  classical
  obtain ⟨C, hC, -, hcov, hcard⟩ := hE.exists_chainPartition
  have hAC : A.card ≤ C.card :=
    hA.card_le_card_of_chainCover (fun c hc ↦ (hC c hc).2) fun a ha ↦ by
      simpa [← hcov] using hAs ha
  omega

/-- **Split-graph matching duality for finite strict orders.** On any finite subset `s` under a
strict order `r`, the maximum size of an `r`-order matching plus the `r`-antichain width equals
`s.card`. -/
theorem orderMatchingNumber_add_antichainWidth {α : Type*} (s : Finset α) (r : α → α → Prop)
    [IsStrictOrder α r] :
    s.orderMatchingNumber r + s.antichainWidth r = s.card := by
  classical
  apply le_antisymm
  · obtain ⟨E, hE, hEcard⟩ := s.exists_isOrderMatching_card_eq_orderMatchingNumber r
    obtain ⟨A, hAs, hA, hAcard⟩ := s.exists_isAntichain_card_eq_antichainWidth r
    rw [← hEcard, ← hAcard]
    exact hE.card_add_card_le_of_isAntichain hAs hA
  · obtain ⟨A, C, hAs, hA, hC, hdisj, hcov, hcard⟩ := s.exists_isAntichain_chainPartition r
    obtain ⟨E, hE, hEC⟩ := exists_isOrderMatching_of_chainPartition hC hdisj hcov
    have h1 : E.card ≤ s.orderMatchingNumber r := card_le_orderMatchingNumber hE
    have h2 : A.card ≤ s.antichainWidth r := card_le_antichainWidth hAs hA
    omega

/-- **Split-graph matching duality for finite partial orders.** On any finite subset `s` of a
partial order, the maximum size of a `<`-order matching plus the `≤`-antichain width equals
`s.card`. -/
theorem orderMatchingNumber_lt_add_antichainWidth_le {α : Type*} [PartialOrder α] (s : Finset α) :
    s.orderMatchingNumber (· < ·) + s.antichainWidth (· ≤ ·) = s.card := by
  rw [← antichainWidth_lt_eq_le]
  exact orderMatchingNumber_add_antichainWidth s (· < ·)

end Finset

end ChainMatchingBridge

end OrderMatching
