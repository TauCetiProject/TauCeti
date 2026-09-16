/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement

/-!
# Elements with a prescribed divisibility condition on their order

In the cyclic auxiliary group used by the Chebotarev crossing, the useful tags are the elements
whose order is divisible by the order of the chosen Frobenius element. This file gives that finite
carrier together with its membership and divisibility API.

## Main definitions

* `NumberField.Chebotarev.taggedElements`: elements whose order is divisible by a given natural
  number.

## Main results

* `NumberField.Chebotarev.mem_taggedElements_iff`: the defining membership condition.
* `NumberField.Chebotarev.taggedElements_mono`: divisibility makes the tag carrier shrink.

## References

The crossing construction follows R. Sharifi, *Algebraic Number Theory*, Theorem 7.2.2.
-/

public section

open scoped BigOperators

namespace NumberField.Chebotarev

open Finset Nat

/-- The elements of a finite group whose order is divisible by `f`.

The carrier is deliberately a `Finset`, so the tags can be indexed by their order. -/
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
  unfold taggedElements
  exact Finset.monotone_filter_right Finset.univ fun _ _ h => hfg.trans h

/-- Every element is tagged for the vacuous order condition `f = 1`. -/
@[simp]
theorem taggedElements_one {H : Type*} [Group H] [Fintype H] :
    taggedElements (H := H) 1 = Finset.univ := by
  ext τ
  simp [taggedElements]

end NumberField.Chebotarev
