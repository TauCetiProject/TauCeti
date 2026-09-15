/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Cyclic.OrderCount

/-!
# Elements with a prescribed divisibility condition on their order

In the cyclic auxiliary group used by the Chebotarev crossing, the useful tags are the elements
whose order is divisible by the order of the chosen Frobenius element. This file gives that finite
carrier and records the order-fibre decomposition of its cardinality. The latter is the exact
finite sum from which the Euler-product form of the crossing constant is obtained.

## Main definitions

* `NumberField.Chebotarev.taggedElements`: elements whose order is divisible by a given natural
  number.

## Main results

* `NumberField.Chebotarev.mem_taggedElements_iff`: the defining membership condition.
* `NumberField.Chebotarev.taggedElements_mono`: divisibility makes the tag carrier shrink.
* `NumberField.Chebotarev.card_taggedElements_eq_sum_totient`: the Chebotarev carrier is bridged to
  the generic cyclic order-counting theorem.
-/

public section

open scoped BigOperators

namespace NumberField.Chebotarev

open Finset Nat

/-- The elements of a finite group whose order is divisible by `f`.

The carrier is deliberately a `Finset`: Layer 9 sums the densities of these tags, and the
disjointness argument indexes those summands by an actual finite set. -/
noncomputable def taggedElements {H : Type*} [Group H] [Fintype H] (f : ℕ) : Finset H :=
  Finset.univ.filter fun τ ↦ f ∣ orderOf τ

/-- Membership in `taggedElements`, unfolded to the order divisibility condition. -/
@[simp]
theorem mem_taggedElements_iff {H : Type*} [Group H] [Fintype H] {f : ℕ} {τ : H} :
    τ ∈ taggedElements f ↔ f ∣ orderOf τ := by
  simp [taggedElements]

/-- A stronger divisibility requirement gives a smaller tagged carrier. -/
theorem taggedElements_mono {H : Type*} [Group H] [Fintype H] {f g : ℕ} (hfg : f ∣ g) :
    taggedElements (H := H) g ⊆ taggedElements (H := H) f := by
  intro τ hτ
  exact mem_taggedElements_iff.mpr (hfg.trans (mem_taggedElements_iff.mp hτ))

/-- Every element is tagged for the vacuous order condition `f = 1`. -/
@[simp]
theorem taggedElements_one {H : Type*} [Group H] [Fintype H] :
    taggedElements (H := H) 1 = Finset.univ := by
  ext τ
  simp [taggedElements]

/-- In a finite cyclic group, split the tags according to the exact order of their elements.

The arithmetic content is supplied by the generic cyclic order-counting API; this theorem keeps the
Chebotarev carrier opaque to its consumers. -/
theorem card_taggedElements_eq_sum_totient {H : Type*} [Group H] [Fintype H] [IsCyclic H]
    (f : ℕ) :
    (taggedElements (H := H) f).card =
      ∑ d ∈ {d ∈ (Fintype.card H).divisors | f ∣ d}, Nat.totient d := by
  -- The named carrier is this filtered subtype; expose that bridge before using the generic API.
  change #{τ : H | f ∣ orderOf τ} = _
  exact IsCyclic.card_filter_dvd_orderOf_eq_sum_totient f

end NumberField.Chebotarev
