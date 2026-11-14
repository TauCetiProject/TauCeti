/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Set.Card
import Mathlib.Data.Multiset.Filter

/-!
# Multisets of values of a function on a finite set

Given a finite set `s : Set α` (`hs : s.Finite`) and a function `f : α → β`, mapping `f` over the
underlying multiset `hs.toFinset.val` records the values of `f` on `s` with their fibre
multiplicities:

* the multiplicity of `b : β` in `hs.toFinset.val.map f` is `{x ∈ s | f x = b}.ncard`, equivalently
  `Nat.card {x // x ∈ s ∧ f x = b}` (`Set.Finite.count_map_toFinset_val`,
  `Set.Finite.count_map_toFinset_val_eq_natCard`);
* consequently `hs.toFinset.val.map f = m` holds if and only if each fibre `{x // x ∈ s ∧ f x = b}`
  has cardinality `m.count b` (`Set.Finite.map_toFinset_val_eq_iff`);
* for any commutative monoid `M` and `g : β → M`, taking the product (or sum) of `g (f x)` over
  `x ∈ s` equals `((hs.toFinset.val.map f).map g).prod`
  (`Set.Finite.finprod_mem_comp_eq_multiset_prod_map`,
  `Set.Finite.finsum_mem_comp_eq_multiset_sum_map`), and for an arbitrary (possibly infinite) set
  `s : Set α` there always exists a multiset `m : Multiset β` representing `∏ᶠ x ∈ s, g (f x)` as
  `(m.map g).prod` (`Set.exists_finprod_mem_comp_eq_multiset_prod_map`,
  `Set.exists_finsum_mem_comp_eq_multiset_sum_map`).
-/

public section

namespace Set.Finite

variable {α β M : Type*} {s : Set α}

/-- The multiplicity of `b` in the multiset of values of `f` on a finite set `s` is the cardinality
of the fibre `{x ∈ s | f x = b}`. -/
theorem count_map_toFinset_val [DecidableEq β] (hs : s.Finite) (f : α → β) (b : β) :
    (hs.toFinset.val.map f).count b = {x ∈ s | f x = b}.ncard := by
  classical
  have hsep : {x ∈ s | f x = b}.Finite := hs.sep _
  rw [Set.ncard_eq_toFinset_card _ hsep, Multiset.count_map]
  have hfin : hsep.toFinset = hs.toFinset.filter fun x ↦ b = f x := by
    ext x
    simp [eq_comm]
  rw [hfin, Finset.card_def, Finset.filter_val]

/-- The multiplicity of `b` in `hs.toFinset.val.map f` equals `Nat.card {x // x ∈ s ∧ f x = b}`. -/
theorem count_map_toFinset_val_eq_natCard [DecidableEq β] (hs : s.Finite) (f : α → β) (b : β) :
    (hs.toFinset.val.map f).count b = Nat.card {x // x ∈ s ∧ f x = b} := by
  rw [hs.count_map_toFinset_val]
  exact (Nat.card_coe_set_eq {x ∈ s | f x = b}).symm

/-- The multiset of values of `f` on a finite set `s` equals `m` if and only if every fibre over
`b : β` has cardinality `m.count b`. -/
theorem map_toFinset_val_eq_iff [DecidableEq β] (hs : s.Finite) (f : α → β) (m : Multiset β) :
    hs.toFinset.val.map f = m ↔ ∀ b, Nat.card {x // x ∈ s ∧ f x = b} = m.count b := by
  rw [Multiset.ext]
  simp_rw [hs.count_map_toFinset_val_eq_natCard]

/-- The multiset of values of `f` on a finite set `s` equals `m` if and only if every fibre
`{x ∈ s | f x = b}` has `Set.ncard` equal to `m.count b`. -/
theorem map_toFinset_val_eq_iff_ncard [DecidableEq β] (hs : s.Finite) (f : α → β)
    (m : Multiset β) :
    hs.toFinset.val.map f = m ↔ ∀ b, {x ∈ s | f x = b}.ncard = m.count b := by
  rw [Multiset.ext]
  simp_rw [hs.count_map_toFinset_val]

/-- Taking the product of `f` over a finite set `s` agrees with taking the product of
`hs.toFinset.val.map f`. -/
@[to_additive /-- Summing `f` over a finite set `s` agrees with summing `hs.toFinset.val.map f`. -/]
theorem finprod_mem_eq_multiset_prod_map [CommMonoid M] (hs : s.Finite) (f : α → M) :
    ∏ᶠ x ∈ s, f x = (hs.toFinset.val.map f).prod := by
  rw [finprod_mem_eq_finite_toFinset_prod _ hs, Finset.prod_eq_multiset_prod]

/-- Taking the product of `g (f x)` over `x ∈ s` factors through the multiset
`hs.toFinset.val.map f` of values of `f` on `s`. -/
@[to_additive /-- Summing `g (f x)` over `x ∈ s` factors through the multiset
`hs.toFinset.val.map f` of values of `f` on `s`. -/]
theorem finprod_mem_comp_eq_multiset_prod_map [CommMonoid M] (hs : s.Finite) (f : α → β)
    (g : β → M) :
    ∏ᶠ x ∈ s, g (f x) = ((hs.toFinset.val.map f).map g).prod := by
  rw [hs.finprod_mem_eq_multiset_prod_map, Multiset.map_map]
  rfl

end Set.Finite

namespace Set

variable {α β M : Type*}

/-- For any set `s : Set α`, `f : α → β`, and `g : β → M`, there exists a multiset `m : Multiset β`
such that `∏ᶠ x ∈ s, g (f x) = (m.map g).prod` (namely `ht.toFinset.val.map f` when
`s ∩ Function.mulSupport (g ∘ f)` is finite, and `0` otherwise). -/
@[to_additive /-- For any set `s : Set α`, `f : α → β`, and `g : β → M`, there exists a multiset
`m : Multiset β` such that `∑ᶠ x ∈ s, g (f x) = (m.map g).sum` (namely `ht.toFinset.val.map f` when
`s ∩ Function.support (g ∘ f)` is finite, and `0` otherwise). -/]
theorem exists_finprod_mem_comp_eq_multiset_prod_map [CommMonoid M] (s : Set α) (f : α → β)
    (g : β → M) :
    ∃ m : Multiset β, ∏ᶠ x ∈ s, g (f x) = (m.map g).prod := by
  by_cases ht : (s ∩ Function.mulSupport fun x ↦ g (f x)).Finite
  · exact ⟨ht.toFinset.val.map f, by
      rw [← finprod_mem_inter_mulSupport, ht.finprod_mem_comp_eq_multiset_prod_map]⟩
  · exact ⟨0, by rw [finprod_mem_eq_one_of_infinite ht, Multiset.map_zero, Multiset.prod_zero]⟩

end Set
