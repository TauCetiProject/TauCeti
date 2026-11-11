/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.GroupTheory.Index

/-!
# Finiteness of the double-coset quotient

A double coset `HgK` is a union of left cosets of `K`, so the double cosets `H \ G / K` are a
quotient of `G ⧸ K`: the map `gK ↦ HgK` is well defined and surjective
(`TauCeti.doubleCosetMk_out_mk` is the well-definedness, in the form the surjection uses).
Consequently `H \ G / K` is finite as soon as `K` has finite index, with no finiteness assumption
on `G` itself.

This is the instance that lets a sum be taken over `H \ G / K`; the Mackey decomposition
(`TauCeti.RepresentationTheory.Induction.Mackey.Basic`) uses it, where the index of the subgroup
being induced from is the only finiteness available.

The double cosets partition `G`, so for finite `G` their sizes add up to the order of `G`
(`Subgroup.sum_card_quotToDoubleCoset`).

## Main statements

* `TauCeti.finite_doubleCosetQuotient`: `H \ G / K` is finite when `K` has finite index in `G`.
* `Subgroup.sum_card_quotToDoubleCoset`: the sizes of the double cosets add up to `|G|`.
* `Subgroup.sum_card_quotToDoubleCoset_div_card_eq_index`: the numbers `|HgK| / |H|` add up
  to the index of `H`.
-/

public section

open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G]

/-- Replacing an element by the chosen representative of its left `K`-coset does not change its
double coset. -/
theorem doubleCosetMk_out_mk (H K : Subgroup G) (g : G) :
    DoubleCoset.mk H K (QuotientGroup.mk g : G ⧸ K).out = DoubleCoset.mk H K g := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
  rw [hk, DoubleCoset.mk_mul_mem]

/-- **The double cosets `H \ G / K` are finite when `K` has finite index**: they are the image of
the finite set `G ⧸ K` under `gK ↦ HgK`. -/
instance finite_doubleCosetQuotient (H K : Subgroup G) [K.FiniteIndex] :
    Finite (DoubleCoset.Quotient (H : Set G) (K : Set G)) :=
  Finite.of_surjective (fun t : G ⧸ K => DoubleCoset.mk H K t.out) fun d =>
    ⟨QuotientGroup.mk d.out, (doubleCosetMk_out_mk H K d.out).trans (DoubleCoset.out_eq' d)⟩

end TauCeti

namespace Subgroup

variable {G : Type*} [Group G]

/-- **The double cosets partition the group**: for finite `G`, the sizes of the double cosets
`HgK` add up to the order of `G`. -/
theorem sum_card_quotToDoubleCoset [Finite G] (H K : Subgroup G)
    [Fintype (DoubleCoset.Quotient (H : Set G) (K : Set G))] :
    ∑ q, Nat.card (DoubleCoset.quotToDoubleCoset H K q) = Nat.card G := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (DoubleCoset.mk H K)), Nat.card_sigma]
  exact Fintype.sum_congr _ _ fun q =>
    Nat.card_congr (Equiv.subtypeEquivRight fun a => DoubleCoset.mem_quotToDoubleCoset_iff q a)

/-- **The double cosets count the right cosets**: each double coset `HsK` of a finite group is a
union of `|HsK| / |H|` right cosets of `H`, and these numbers add up, over `H \ G / K`, to the
index of `H`. -/
theorem sum_card_quotToDoubleCoset_div_card_eq_index [Finite G] (H K : Subgroup G)
    [Fintype (DoubleCoset.Quotient (H : Set G) (K : Set G))] :
    ∑ q, Nat.card (DoubleCoset.quotToDoubleCoset H K q) / Nat.card H = H.index := by
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H)) ?_
  rw [Finset.sum_mul, Subgroup.index_mul_card, ← sum_card_quotToDoubleCoset H K]
  refine Finset.sum_congr rfl fun q _ => Nat.div_mul_cancel ?_
  -- Inversion turns right cosets of `H` into left cosets, counted by Mathlib's formula.
  rw [DoubleCoset.quotToDoubleCoset, DoubleCoset.doubleCoset,
    ← Nat.card_image_of_injective inv_injective, Set.image_inv_eq_inv]
  simp only [mul_inv_rev, inv_coe_set, ← mul_assoc]
  rw [Subgroup.card_mul_eq_card_subgroup_mul_card_quotient]
  exact dvd_mul_right _ _

end Subgroup
