/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors

/-!
# Irreducibility from the number of normalized factors

In a unique factorization monoid with a normalization, an element is irreducible exactly when its
normalized factors, counted with multiplicity, consist of a single element. This complements
Mathlib's `UniqueFactorizationMonoid.normalizedFactors_irreducible`, which computes the normalized
factors of an irreducible element.

## Main results

* `UniqueFactorizationMonoid.card_normalizedFactors_eq_one_iff`: `a` has exactly one normalized
  factor, counted with multiplicity, if and only if `a` is irreducible.
-/

public section

namespace UniqueFactorizationMonoid

variable {α : Type*} [CommMonoidWithZero α] [NormalizationMonoid α] [UniqueFactorizationMonoid α]

/-- An element of a unique factorization monoid has exactly one normalized factor, counted with
multiplicity, if and only if it is irreducible. -/
theorem card_normalizedFactors_eq_one_iff {a : α} :
    (normalizedFactors a).card = 1 ↔ Irreducible a := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [normalizedFactors_irreducible h, Multiset.card_singleton]⟩
  obtain ⟨q, hq⟩ := Multiset.card_eq_one.mp h
  have ha : a ≠ 0 := by rintro rfl; simp at h
  -- `a` is associated to the product of its normalized factors, which is the irreducible `q`.
  have hprod := prod_normalizedFactors ha
  rw [hq, Multiset.prod_singleton] at hprod
  exact hprod.irreducible
    (irreducible_of_normalized_factor q (hq ▸ Multiset.mem_singleton_self q))

end UniqueFactorizationMonoid
