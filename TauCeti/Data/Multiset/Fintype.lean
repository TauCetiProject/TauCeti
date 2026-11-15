/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Multiset.Fintype

/-!
# Finite indexing of multisets

Mathlib coerces a multiset `m` to the type of its elements, where an element is a value of `m`
together with an occurrence index below its multiplicity. When `m` has no duplicates every value
occurs once, so an element is determined by its value: `Multiset.Nodup.coe_injective` records that
the coercion to the ambient type is injective.

Without decidable equality on the ambient type, a multiset `m` can still be indexed over
`Fin m.toList.length` through `m.toList`: mapping `Finset.univ` by `i ↦ m.toList[i]` recovers `m`
(`Multiset.map_univ_toList`), and products or sums over `Fin m.toList.length` reindex to multiset
products or sums (`Multiset.prod_toList_getElem`, `Multiset.sum_toList_getElem`).
-/

public section

namespace Multiset

/-- For a multiset without duplicates, an element is determined by its value. -/
theorem Nodup.coe_injective {α : Type*} [DecidableEq α] {m : Multiset α} (h : m.Nodup) :
    Function.Injective fun x : m ↦ (x : α) := by
  intro x y hxy
  apply (coeEmbedding m).injective
  have hx := x.2.2
  have hy := y.2.2
  simp only [count_eq_one_of_mem h coe_mem] at hx hy
  simp only [coeEmbedding_apply, Prod.mk.injEq]
  exact ⟨hxy, by lia⟩

/-- Indexing `m.toList` over `Fin m.toList.length` recovers the multiset `m`. -/
theorem map_univ_toList {α : Type*} (m : Multiset α) :
    (Finset.univ : Finset (Fin m.toList.length)).val.map (fun i ↦ m.toList[i]) = m := by
  rw [Fin.univ_def, map_coe]
  exact (congrArg ofList (List.map_getElem_finRange m.toList)).trans (coe_toList m)

/-- A product indexed by `Fin m.toList.length` through `m.toList` equals the multiset product of
`m.map f`. -/
@[to_additive /-- A sum indexed by `Fin m.toList.length` through `m.toList` equals the multiset
sum of `m.map f`. -/]
theorem prod_toList_getElem {α M : Type*} [CommMonoid M] (m : Multiset α) (f : α → M) :
    (∏ i : Fin m.toList.length, f m.toList[i]) = (m.map f).prod := by
  rw [Finset.prod_eq_multiset_prod,
    show (fun i : Fin m.toList.length ↦ f m.toList[i]) = f ∘ fun i ↦ m.toList[i] from
      funext fun _ ↦ (Function.comp_apply).symm,
    ← map_map, map_univ_toList]

end Multiset
