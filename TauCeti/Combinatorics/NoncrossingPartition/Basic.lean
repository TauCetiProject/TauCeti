/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Interval.Finset.Defs
public import TauCeti.Order.Partition.Finpartition

/-!
# Noncrossing partitions

Let `s` be a finite set of positions in a linear order. A finite partition `P` of `s` is
*noncrossing* if there are no positions `a < b < c < d` with `a` and `c` in one part of `P`
and `b` and `d` in a different part. For `s = Finset.univ : Finset (Fin n)` these are the
noncrossing partitions of `n` ordered positions, which index the moment–cumulant formula of free
probability.

The noncrossing partitions of `s`, ordered by refinement, form a finite lattice `NC(s)`. Its
meet is the common refinement of `Finpartition`, its bottom element is the partition into
singletons and its top element is the partition with one part (no parts when `s = ∅`). Its join
is the least noncrossing partition coarser than both arguments; mathematically it can be strictly
coarser than their join among all partitions, which may cross. Mathlib's `Finpartition s` has
only a meet, not a join, so the join in `NC(s)` is characterised by its universal property
(`le_sup_left`, `le_sup_right`, `sup_le`) rather than by a comparison lemma.

## Main definitions

* `Finpartition.IsNoncrossing P` — the finite partition `P` of `s` is noncrossing.
* `TauCeti.NoncrossingPartition s` — the noncrossing partitions of `s`, with the refinement order
  inherited from `Finpartition s`.
* `TauCeti.NoncrossingPartition.singletonPartEquiv` — the noncrossing partitions of `s` in which
  `i` forms a part on its own correspond to the noncrossing partitions of `s.erase i`.

## Main results

* `Finpartition.isNoncrossing_bot`, `Finpartition.isNoncrossing_top` — the partitions into
  singletons and into one part are noncrossing.
* `Finpartition.IsNoncrossing.part_eq_part` — in a noncrossing partition, positions
  `a < b < c < d` with `a, c` in one part and `b, d` in one part all lie in one part.
* `Finpartition.IsNoncrossing.inf` — common refinements of noncrossing partitions are
  noncrossing.
* `Finpartition.IsNoncrossing.restrict` — restricting a noncrossing partition of `s` to a subset
  of `s` gives a noncrossing partition.
* `Finpartition.IsNoncrossing.bind` — juxtaposing noncrossing partitions of the parts of a
  noncrossing partition gives a noncrossing partition.
* `Finpartition.IsNoncrossing.extend_singleton` — adding a singleton part to a noncrossing
  partition gives a noncrossing partition.
* `TauCeti.NoncrossingPartition.instLattice` — the noncrossing partitions of `s` form a lattice,
  with meets computed in `Finpartition s`; it is bounded, and locally finite so that its
  incidence algebra is available.
* `TauCeti.NoncrossingPartition.univ_eq_bot_top_of_pair` — a set with at most two elements has
  only the partitions into singletons and into one part, which differ by
  `TauCeti.NoncrossingPartition.bot_ne_top_of_one_lt_card` once it has two elements; a
  one-element set has a unique noncrossing partition.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 9.
* G. Kreweras, *Sur les partitions non croisées d'un cycle*, Discrete Math. 1 (1972), 333–350.
-/

public section

open Finset

namespace Finpartition

variable {α : Type*} [LinearOrder α] {s t : Finset α} {P Q : Finpartition s}

/-- A finite partition of a set of positions in a linear order is *noncrossing* if whenever
`a < b < c < d` with `a, c` in a part `B` and `b, d` in a part `C`, the parts coincide. -/
def IsNoncrossing (P : Finpartition s) : Prop :=
  ∀ B ∈ P.parts, ∀ C ∈ P.parts, ∀ a ∈ B, ∀ b ∈ C, ∀ c ∈ B, ∀ d ∈ C,
    a < b → b < c → c < d → B = C

theorem isNoncrossing_iff :
    P.IsNoncrossing ↔ ∀ B ∈ P.parts, ∀ C ∈ P.parts, ∀ a ∈ B, ∀ b ∈ C, ∀ c ∈ B, ∀ d ∈ C,
      a < b → b < c → c < d → B = C :=
  Iff.rfl

instance : DecidablePred (IsNoncrossing (s := s)) := fun _ =>
  decidable_of_iff _ isNoncrossing_iff.symm

/-- Noncrossingness in terms of the part `P.part a` containing each position: if `a < b < c < d`
are positions of `s` with `c` in the part of `a` and `d` in the part of `b`, then `a` and `b`
lie in the same part. -/
theorem isNoncrossing_iff_part :
    P.IsNoncrossing ↔ ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ P.part a, ∀ d ∈ P.part b,
      a < b → b < c → c < d → P.part a = P.part b := by
  refine ⟨fun h a ha b hb c hc d hd => h _ (P.part_mem.2 ha) _ (P.part_mem.2 hb) a
    (P.mem_part_self.2 ha) b (P.mem_part_self.2 hb) c hc d hd, fun h B hB C hC a ha b hb c hc d hd
    hab hbc hcd => ?_⟩
  rw [← P.part_eq_of_mem hB ha] at hc
  rw [← P.part_eq_of_mem hC hb] at hd
  rw [← P.part_eq_of_mem hB ha, ← P.part_eq_of_mem hC hb]
  exact h a (P.le hB ha) b (P.le hC hb) c hc d hd hab hbc hcd

/-- In a noncrossing partition, positions `a < b < c < d` with `a, c` in a common part and `b, d`
in a common part all lie in one part. -/
theorem IsNoncrossing.part_eq_part (hP : P.IsNoncrossing) {a b c d : α} (ha : a ∈ s)
    (hb : b ∈ s) (hac : P.part a = P.part c) (hbd : P.part b = P.part d) (hab : a < b)
    (hbc : b < c) (hcd : c < d) : P.part a = P.part b :=
  isNoncrossing_iff_part.1 hP a ha b hb c
    (hac ▸ P.mem_part_self.2 (P.part_nonempty.1 (hac ▸ P.part_nonempty.2 ha))) d
    (hbd ▸ P.mem_part_self.2 (P.part_nonempty.1 (hbd ▸ P.part_nonempty.2 hb))) hab hbc hcd

/-- The partition into singletons is noncrossing. -/
@[simp]
theorem isNoncrossing_bot : (⊥ : Finpartition s).IsNoncrossing := by
  intro B hB C _ a ha b _ c hc _ _ hab hbc _
  obtain ⟨x, -, rfl⟩ := mem_bot_iff.1 hB
  rw [mem_singleton] at ha hc
  subst ha hc
  exact absurd (hab.trans hbc) (lt_irrefl _)

/-- The partition with at most one part is noncrossing. -/
@[simp]
theorem isNoncrossing_top : (⊤ : Finpartition s).IsNoncrossing :=
  fun _ hB _ hC _ _ _ _ _ _ _ _ _ _ _ => parts_top_subsingleton s hB hC

/-- Common refinements of noncrossing partitions are noncrossing. -/
theorem IsNoncrossing.inf (hP : P.IsNoncrossing) (hQ : Q.IsNoncrossing) :
    (P ⊓ Q).IsNoncrossing := by
  intro B hB C hC a ha b hb c hc d hd hab hbc hcd
  simp only [parts_inf, mem_erase, mem_image, mem_product, Prod.exists] at hB hC
  obtain ⟨-, B₁, B₂, ⟨hB₁, hB₂⟩, rfl⟩ := hB
  obtain ⟨-, C₁, C₂, ⟨hC₁, hC₂⟩, rfl⟩ := hC
  rw [inf_eq_inter, mem_inter] at ha hb hc hd
  rw [hP B₁ hB₁ C₁ hC₁ a ha.1 b hb.1 c hc.1 d hd.1 hab hbc hcd,
    hQ B₂ hB₂ C₂ hC₂ a ha.2 b hb.2 c hc.2 d hd.2 hab hbc hcd]

/-- Restricting a noncrossing partition of `s` to a subset `t ⊆ s`, by intersecting each part
with `t`, gives a noncrossing partition of `t`. -/
theorem IsNoncrossing.restrict (hP : P.IsNoncrossing) (hts : t ≤ s) :
    (P.restrict hts).IsNoncrossing := by
  intro B hB C hC a ha b hb c hc d hd hab hbc hcd
  simp only [parts_restrict, mem_erase, mem_image] at hB hC
  obtain ⟨-, B, hB, rfl⟩ := hB
  obtain ⟨-, C, hC, rfl⟩ := hC
  rw [inf_eq_inter, mem_inter] at ha hb hc hd
  rw [hP B hB C hC a ha.1 b hb.1 c hc.1 d hd.1 hab hbc hcd]

/-- Juxtaposing noncrossing partitions of the parts of a noncrossing partition gives a noncrossing
partition. -/
theorem IsNoncrossing.bind {Q : ∀ B ∈ P.parts, Finpartition B} (hP : P.IsNoncrossing)
    (hQ : ∀ B hB, (Q B hB).IsNoncrossing) : (P.bind Q).IsNoncrossing := by
  refine isNoncrossing_iff.2 fun X hX Y hY a ha b hb c hc d hd hab hbc hcd => ?_
  obtain ⟨B, hB, hXB⟩ := mem_bind.1 hX
  obtain ⟨C, hC, hYC⟩ := mem_bind.1 hY
  obtain rfl := isNoncrossing_iff.1 hP B hB C hC a ((Q B hB).le hXB ha) b ((Q C hC).le hYC hb) c
    ((Q B hB).le hXB hc) d ((Q C hC).le hYC hd) hab hbc hcd
  exact isNoncrossing_iff.1 (hQ B hB) X hXB Y hYC a ha b hb c hc d hd hab hbc hcd

/-- Adding a singleton part to a noncrossing partition gives a noncrossing partition. -/
theorem IsNoncrossing.extend_singleton {P : Finpartition t} (hP : P.IsNoncrossing) {i : α}
    (hi : ({i} : Finset α) ≠ ⊥) (hti : Disjoint t {i}) (hts : t ⊔ {i} = s) :
    (P.extend hi hti hts).IsNoncrossing := by
  intro B hB C hC a ha b hb c hc d hd hab hbc hcd
  rw [extend_parts, mem_insert] at hB hC
  obtain rfl | hB := hB
  · rw [mem_singleton] at ha hc
    exact absurd (hab.trans hbc) (ha ▸ hc ▸ lt_irrefl i)
  obtain rfl | hC := hC
  · rw [mem_singleton] at hb hd
    exact absurd (hbc.trans hcd) (hb ▸ hd ▸ lt_irrefl i)
  exact hP B hB C hC a ha b hb c hc d hd hab hbc hcd

end Finpartition

namespace TauCeti

variable {α : Type*} [LinearOrder α] {s : Finset α}

variable (s) in
/-- The noncrossing partitions of a finite set `s` of positions in a linear order, ordered by
refinement. For `s = Finset.univ : Finset (Fin n)` this is the lattice `NC(n)` of noncrossing
partitions of `n` ordered positions. -/
abbrev NoncrossingPartition : Type _ :=
  {P : Finpartition s // P.IsNoncrossing}

namespace NoncrossingPartition

/-- The noncrossing partitions of `s` form a lattice. The meet is the common refinement, and the
join of `P` and `Q` is the meet of all noncrossing partitions coarser than both. -/
noncomputable instance instLattice : Lattice (NoncrossingPartition s) where
  __ := Subtype.partialOrder _
  inf P Q := ⟨P.1 ⊓ Q.1, P.2.inf Q.2⟩
  inf_le_left _ _ := inf_le_left (α := Finpartition s)
  inf_le_right _ _ := inf_le_right (α := Finpartition s)
  le_inf _ _ _ := le_inf (α := Finpartition s)
  sup P Q := open Classical in
    ⟨(univ.filter fun R : Finpartition s => R.IsNoncrossing ∧ P.1 ≤ R ∧ Q.1 ≤ R).inf id,
      Finset.inf_induction Finpartition.isNoncrossing_top (fun _ h₁ _ h₂ => h₁.inf h₂)
        fun _ hR => (mem_filter.1 hR).2.1⟩
  le_sup_left P Q := by
    classical
    exact Subtype.coe_le_coe.1 <| Finset.le_inf fun R hR => (mem_filter.1 hR).2.2.1
  le_sup_right P Q := by
    classical
    exact Subtype.coe_le_coe.1 <| Finset.le_inf fun R hR => (mem_filter.1 hR).2.2.2
  sup_le P Q R hPR hQR := by
    classical
    exact Subtype.coe_le_coe.1 <|
      Finset.inf_le (f := id) (mem_filter.2 ⟨mem_univ R.1, R.2, hPR, hQR⟩)

instance : BoundedOrder (NoncrossingPartition s) where
  __ := Subtype.orderBot Finpartition.isNoncrossing_bot
  __ := Subtype.orderTop Finpartition.isNoncrossing_top

@[simp, norm_cast]
theorem coe_inf (P Q : NoncrossingPartition s) :
    ((P ⊓ Q : NoncrossingPartition s) : Finpartition s) = (P : Finpartition s) ⊓ Q :=
  rfl

@[simp, norm_cast]
theorem coe_bot : ((⊥ : NoncrossingPartition s) : Finpartition s) = ⊥ :=
  rfl

@[simp, norm_cast]
theorem coe_top : ((⊤ : NoncrossingPartition s) : Finpartition s) = ⊤ :=
  rfl

/-- The noncrossing partitions of `s` form a finite poset with decidable order, hence a locally
finite order; this makes its incidence algebra, with its zeta and Möbius functions, available. -/
instance : LocallyFiniteOrder (NoncrossingPartition s) :=
  letI := decidableLTOfDecidableLE (α := NoncrossingPartition s)
  Fintype.toLocallyFiniteOrder

/-- A noncrossing partition of the empty set is the partition into no parts. -/
theorem eq_bot_of_eq_empty (hs : s = ∅) (P : NoncrossingPartition s) : P = ⊥ := by
  have hs : s = ⊥ := hs.trans Finset.bot_eq_empty.symm
  exact Subtype.ext <| Finpartition.ext <| by
    rw [Finpartition.parts_eq_empty_iff.2 hs, Finpartition.parts_eq_empty_iff.2 hs]

/-- The partition of the empty set into no parts is its only noncrossing partition. -/
instance : Unique (NoncrossingPartition (∅ : Finset α)) where
  default := ⊥
  uniq := eq_bot_of_eq_empty rfl

/-- Over an empty type of positions, such as `Fin 0`, the partition into no parts is the only
noncrossing partition; in particular `NC(0)` has a single element. -/
instance [IsEmpty α] : Unique (NoncrossingPartition s) where
  default := ⊥
  uniq := eq_bot_of_eq_empty s.eq_empty_of_isEmpty

/-- The partition of a one-element set into its single part is its only noncrossing
partition. -/
instance (i : α) : Unique (NoncrossingPartition ({i} : Finset α)) where
  default := ⊥
  uniq P := le_bot_iff.1 <| le_top.trans_eq <| Subtype.ext <| Finpartition.ext <| by
    simp [Finpartition.parts_top (singleton_ne_empty i)]

/-- If `s` has at least two elements, the partition into singletons and the partition into one
part are different noncrossing partitions of `s`. -/
theorem bot_ne_top_of_one_lt_card (hs : 1 < #s) : (⊥ : NoncrossingPartition s) ≠ ⊤ := fun h => by
  have := congrArg (fun P : NoncrossingPartition s => #P.1.parts) h
  simp only [coe_bot, coe_top, Finpartition.card_bot,
    Finpartition.parts_top (card_pos.1 (zero_lt_one.trans hs)).ne_empty, card_singleton] at this
  omega

/-- A noncrossing partition of a set with at most two elements is either the partition into
singletons or the partition into one part. -/
theorem eq_bot_or_eq_top_of_pair {i j : α} (P : NoncrossingPartition ({i, j} : Finset α)) :
    P = ⊥ ∨ P = ⊤ :=
  (Finpartition.eq_bot_or_eq_top_of_pair P.1).imp Subtype.ext Subtype.ext

/-- The noncrossing partitions of a set with at most two elements are the partition into
singletons and the partition into one part. -/
theorem univ_eq_bot_top_of_pair {i j : α} :
    (univ : Finset (NoncrossingPartition ({i, j} : Finset α))) = {⊥, ⊤} := by
  ext P
  simpa using eq_bot_or_eq_top_of_pair P

/-- The noncrossing partitions of `s` in which `i` forms a part on its own correspond to the
noncrossing partitions of `s.erase i`: delete the part `{i}`, or insert it back. -/
noncomputable def singletonPartEquiv {i : α} (hi : i ∈ s) :
    {π : NoncrossingPartition s // {i} ∈ π.1.parts} ≃ NoncrossingPartition (s.erase i) where
  toFun π := ⟨π.1.1.restrict (s.erase_subset i), π.1.2.restrict _⟩
  invFun τ :=
    ⟨⟨τ.1.extend (singleton_ne_empty i) (disjoint_singleton_right.2 (s.notMem_erase i))
        (by rw [sup_eq_union, union_singleton, insert_erase hi]),
      τ.2.extend_singleton _ _ _⟩, mem_insert_self _ _⟩
  left_inv π := Subtype.ext <| Subtype.ext <| Finpartition.ext <| by
    rw [Finpartition.extend_parts, Finpartition.parts_restrict_erase_of_singleton_mem π.2,
      insert_erase π.2]
  right_inv τ := Subtype.ext <| by simp

/-- Deleting the singleton part `{i}` leaves the other parts. -/
@[simp]
theorem parts_singletonPartEquiv_apply {i : α} (hi : i ∈ s)
    (π : {π : NoncrossingPartition s // {i} ∈ π.1.parts}) :
    (singletonPartEquiv hi π).1.parts = π.1.1.parts.erase {i} :=
  Finpartition.parts_restrict_erase_of_singleton_mem π.2

/-- Inserting the singleton part `{i}` adds it to the parts. -/
@[simp]
theorem parts_singletonPartEquiv_symm_apply {i : α} (hi : i ∈ s)
    (τ : NoncrossingPartition (s.erase i)) :
    ((singletonPartEquiv hi).symm τ).1.1.parts = insert {i} τ.1.parts := by
  simp [singletonPartEquiv]

end NoncrossingPartition

end TauCeti
