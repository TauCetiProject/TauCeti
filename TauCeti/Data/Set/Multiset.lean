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
* for any additive commutative monoid `M` and `g : β → M`, summing `g (f x)` over `x ∈ s` equals the
  multiset sum `((hs.toFinset.val.map f).map g).sum`
  (`Set.Finite.finsum_mem_comp_eq_multiset_sum_map`).
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

/-- Summing `f` over a finite set `s` agrees with summing `hs.toFinset.val.map f`. -/
theorem finsum_mem_eq_multiset_sum_map [AddCommMonoid M] (hs : s.Finite) (f : α → M) :
    ∑ᶠ x ∈ s, f x = (hs.toFinset.val.map f).sum := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.sum_eq_multiset_sum]

/-- Summing `g (f x)` over `x ∈ s` factors through the multiset `hs.toFinset.val.map f` of values
of `f` on `s`. -/
theorem finsum_mem_comp_eq_multiset_sum_map [AddCommMonoid M] (hs : s.Finite) (f : α → β)
    (g : β → M) :
    ∑ᶠ x ∈ s, g (f x) = ((hs.toFinset.val.map f).map g).sum := by
  rw [hs.finsum_mem_eq_multiset_sum_map, Multiset.map_map]
  rfl

end Set.Finite
