/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Order.Partition.Finpartition

/-!
# Pair partitions

A finite partition of a finite set `s` is a *pairing* (or *pair partition*) if each of its parts
has exactly two elements. Pairings index the Wick formula for the moments of Gaussian variables,
and the noncrossing pairings index the moments of semicircular variables in free probability.

## Main definitions

* `Finpartition.IsPairing P` — every part of the finite partition `P` has two elements.
* `Finpartition.orderedPairs P` — the ordered pairs `(a, b)` with `a < b` forming the two-element
  parts `{a, b}` of `P` in a linear order.

## Main results

* `Finpartition.isPairing_iff_part` — `P` is a pairing iff the part through each position has two
  elements.
* `Finpartition.IsPairing.card_eq_two_mul` — a pairing of `s` has `#s / 2` parts.
* `Finpartition.IsPairing.even_card` — only a set of even size has a pairing.
* `Finpartition.IsPairing.prod_orderedPairs` — for a pairing on a linear order, products over
  `P.parts` agree with products over `P.orderedPairs`.
-/

public section

open Finset

namespace Finpartition

section DecidableEq

variable {α : Type*} [DecidableEq α] {s : Finset α} {P : Finpartition s}

/-- A finite partition of a finite set is a *pairing* (a pair partition) if each of its parts has
exactly two elements. -/
def IsPairing (P : Finpartition s) : Prop :=
  ∀ B ∈ P.parts, #B = 2

/-- Unfolding of `IsPairing`: every part has two elements. -/
theorem isPairing_iff : P.IsPairing ↔ ∀ B ∈ P.parts, #B = 2 :=
  Iff.rfl

instance : DecidablePred (IsPairing (s := s)) := fun _ =>
  decidable_of_iff _ isPairing_iff.symm

/-- A finite partition is a pairing iff the part through each position has two elements. -/
theorem isPairing_iff_part : P.IsPairing ↔ ∀ a ∈ s, #(P.part a) = 2 := by
  refine ⟨fun h a ha => h _ (P.part_mem.2 ha), fun h B hB => ?_⟩
  obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hB
  rw [← P.part_eq_of_mem hB ha]
  exact h a (P.le hB ha)

/-- In a pair partition, each point has a unique distinct partner in its block. -/
theorem IsPairing.existsUnique_mem_part_ne (hP : P.IsPairing) {a : α} (ha : a ∈ s) :
    ∃! b, b ∈ P.part a ∧ b ≠ a := by
  -- Removing `a` from its two-element block leaves exactly one element.
  have h : #((P.part a).erase a) = 1 := by
    rw [card_erase_of_mem (P.mem_part ha), hP _ (P.part_mem.2 ha)]
  simpa only [mem_erase, and_comm] using card_eq_one_iff_existsUnique.1 h

/-- A pairing of `s` has half as many parts as `s` has elements. -/
theorem IsPairing.card_eq_two_mul (hP : P.IsPairing) : #s = 2 * #P.parts := by
  rw [← P.sum_card_parts, sum_const_nat hP, mul_comm]

/-- A finite set with a pairing has an even number of elements. -/
theorem IsPairing.even_card (hP : P.IsPairing) : Even #s :=
  ⟨#P.parts, by rw [hP.card_eq_two_mul]; omega⟩

end DecidableEq

section LinearOrder

variable {α M : Type*} [LinearOrder α] [CommMonoid M] {s : Finset α} {P : Finpartition s}

/-- The ordered pairs `(a, b)` with `a < b` forming the two-element parts `{a, b}` of a finite
partition `P` of `s` in a linear order. When `P` is a pairing, every part appears once with its
elements in increasing order. -/
def orderedPairs (P : Finpartition s) : Finset (α × α) :=
  {p ∈ s ×ˢ s | p.1 < p.2 ∧ {p.1, p.2} ∈ P.parts}

/-- Defining formula for `Finpartition.orderedPairs`. -/
theorem orderedPairs_def (P : Finpartition s) :
    P.orderedPairs = {p ∈ s ×ˢ s | p.1 < p.2 ∧ {p.1, p.2} ∈ P.parts} :=
  (rfl)

@[simp]
theorem mem_orderedPairs {p : α × α} :
    p ∈ P.orderedPairs ↔ p.1 < p.2 ∧ {p.1, p.2} ∈ P.parts := by
  rw [orderedPairs, mem_filter, mem_product, and_iff_right_iff_imp]
  rintro ⟨_, hp⟩
  exact ⟨P.le hp (mem_insert_self _ _), P.le hp (mem_insert_of_mem (mem_singleton_self _))⟩

theorem lt_of_mem_orderedPairs {p : α × α} (hp : p ∈ P.orderedPairs) : p.1 < p.2 :=
  (mem_orderedPairs.1 hp).1

theorem pair_mem_parts_of_mem_orderedPairs {p : α × α} (hp : p ∈ P.orderedPairs) :
    {p.1, p.2} ∈ P.parts :=
  (mem_orderedPairs.1 hp).2

theorem fst_mem_of_mem_orderedPairs {p : α × α} (hp : p ∈ P.orderedPairs) : p.1 ∈ s :=
  P.le (pair_mem_parts_of_mem_orderedPairs hp) (mem_insert_self _ _)

theorem snd_mem_of_mem_orderedPairs {p : α × α} (hp : p ∈ P.orderedPairs) : p.2 ∈ s :=
  P.le (pair_mem_parts_of_mem_orderedPairs hp) (mem_insert_of_mem (mem_singleton_self _))

@[simp]
theorem orderedPairs_bot : (⊥ : Finpartition s).orderedPairs = ∅ := by
  refine eq_empty_of_forall_notMem fun p hp => ?_
  obtain ⟨hlt, hpart⟩ := mem_orderedPairs.1 hp
  -- Every part of `⊥` is a singleton, but `{p.1, p.2}` has two elements.
  obtain ⟨c, -, hc⟩ := mem_bot_iff.1 hpart
  exact absurd (congrArg card hc) (by rw [card_singleton, card_pair hlt.ne]; omega)

/-- For a pairing `P`, sending `(a, b)` to `{a, b}` identifies `P.orderedPairs` with `P.parts`, so
products of block weights over `P.orderedPairs` agree with products over `P.parts`. -/
@[to_additive /-- For a pairing `P`, sending `(a, b)` to `{a, b}` identifies `P.orderedPairs` with
`P.parts`, so sums of block weights over `P.orderedPairs` agree with sums over `P.parts`. -/]
theorem IsPairing.prod_orderedPairs (hP : P.IsPairing) (F : Finset α → M) :
    (∏ p ∈ P.orderedPairs, F {p.1, p.2}) = ∏ B ∈ P.parts, F B := by
  refine Finset.prod_bij (fun p _ => {p.1, p.2})
    (fun p hp => pair_mem_parts_of_mem_orderedPairs hp) ?_ ?_ fun _ _ => rfl
  · rintro ⟨a₁, b₁⟩ hp₁ ⟨a₂, b₂⟩ hp₂ hEq
    -- Equal pairs `{a₁, b₁} = {a₂, b₂}` agree up to swapping; the order rules out the swap.
    have hEq' : ({a₁, b₁} : Set α) = {a₂, b₂} := by rw [← coe_pair, ← coe_pair, hEq]
    rcases Set.pair_eq_pair_iff.1 hEq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (lt_asymm (lt_of_mem_orderedPairs hp₁) (lt_of_mem_orderedPairs hp₂)).elim
  · intro B hB
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.1 (hP B hB)
    rcases hab.lt_or_gt with hlt | hlt
    · exact ⟨(a, b), mem_orderedPairs.2 ⟨hlt, hB⟩, rfl⟩
    · exact ⟨(b, a), mem_orderedPairs.2 ⟨hlt, pair_comm a b ▸ hB⟩, pair_comm b a⟩

/-- A pairing has as many ordered pairs as parts. -/
theorem IsPairing.card_orderedPairs (hP : P.IsPairing) : #P.orderedPairs = #P.parts := by
  simpa using hP.sum_orderedPairs fun _ => (1 : ℕ)

end LinearOrder

end Finpartition
