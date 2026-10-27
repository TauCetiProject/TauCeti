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

## Main results

* `Finpartition.isPairing_iff_part` — `P` is a pairing iff the part through each position has two
  elements.
* `Finpartition.IsPairing.card_eq_two_mul` — a pairing of `s` has `#s / 2` parts.
* `Finpartition.IsPairing.even_card` — only a set of even size has a pairing.
-/

public section

open Finset

namespace Finpartition

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

/-- A pairing of `s` has half as many parts as `s` has elements. -/
theorem IsPairing.card_eq_two_mul (hP : P.IsPairing) : #s = 2 * #P.parts := by
  rw [← P.sum_card_parts, sum_const_nat hP, mul_comm]

/-- A finite set with a pairing has an even number of elements. -/
theorem IsPairing.even_card (hP : P.IsPairing) : Even #s :=
  ⟨#P.parts, by rw [hP.card_eq_two_mul]; omega⟩

end Finpartition
