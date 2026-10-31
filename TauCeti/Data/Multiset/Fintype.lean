/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Multiset.Fintype

/-!
# Elements of a multiset without duplicates

Mathlib coerces a multiset `m` to the type of its elements, where an element is a value of `m`
together with an occurrence index below its multiplicity. When `m` has no duplicates every value
occurs once, so an element is determined by its value: this file records that the coercion to
the ambient type is injective.
-/

public section

namespace Multiset

variable {α : Type*} [DecidableEq α] {m : Multiset α}

/-- For a multiset without duplicates, an element is determined by its value. -/
theorem Nodup.coe_injective (h : m.Nodup) : Function.Injective fun x : m ↦ (x : α) := by
  intro x y hxy
  apply (coeEmbedding m).injective
  have hx := x.2.2
  have hy := y.2.2
  simp only [count_eq_one_of_mem h coe_mem] at hx hy
  simp only [coeEmbedding_apply, Prod.mk.injEq]
  exact ⟨hxy, by lia⟩

end Multiset
