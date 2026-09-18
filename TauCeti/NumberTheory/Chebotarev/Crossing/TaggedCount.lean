/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Cyclic.OrderCount
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Elements with a prescribed divisibility condition on their order

In the cyclic auxiliary group used by the Chebotarev crossing, the useful tags are the elements
whose order is divisible by the order of the chosen Frobenius element. This file gives that finite
carrier together with its membership and divisibility API.

## Main definitions

* `TauCeti.NumberField.Chebotarev.taggedElements`: elements whose order is divisible by a given
  natural number.

## Main results

* `TauCeti.NumberField.Chebotarev.mem_taggedElements_iff`: the defining membership condition.
* `TauCeti.NumberField.Chebotarev.taggedElements_subset_of_dvd`: divisibility makes the tag carrier
  shrink.
* `TauCeti.NumberField.Chebotarev.card_taggedElements_eq_sum_totient`: the exact cyclic count,
  expressed as a sum of Euler totients over the allowed orders.
* `TauCeti.NumberField.Chebotarev.crossingConstant`: the density contribution of the tagged fibres.
* `TauCeti.NumberField.Chebotarev.le_crossingConstant`: the lower bound obtained by raising the
  auxiliary cyclotomic level.

## References

The crossing construction follows R. Sharifi, *Algebraic Number Theory*, Theorem 7.2.2.
-/

public section

open scoped BigOperators

namespace TauCeti.NumberField.Chebotarev

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
theorem taggedElements_subset_of_dvd {H : Type*} [Group H] [Fintype H] {f g : ℕ} (hfg : f ∣ g) :
    taggedElements (H := H) g ⊆ taggedElements (H := H) f := by
  unfold taggedElements
  exact Finset.monotone_filter_right Finset.univ fun _ _ h => hfg.trans h

/-- Every element is tagged for the vacuous order condition `f = 1`. -/
@[simp]
theorem taggedElements_one {H : Type*} [Group H] [Fintype H] :
    taggedElements (H := H) 1 = Finset.univ := by
  ext τ
  simp [taggedElements]

/-- In a finite cyclic group, count the tagged elements by their exact orders. -/
theorem card_taggedElements_eq_sum_totient {H : Type*} [Group H] [Fintype H] [IsCyclic H]
    (f : ℕ) :
    (taggedElements (H := H) f).card =
      ∑ d ∈ (Fintype.card H).divisors.filter (f ∣ ·), Nat.totient d := by
  unfold taggedElements
  exact IsCyclic.card_filter_dvd_orderOf_eq_sum_totient f

/-- The contribution of the tags whose orders are divisible by `f` to a cyclotomic crossing.

For finite groups `G` and `H`, a tagged fibre has weight
`1 / (#G * #H)`.  Thus the disjoint union over `taggedElements f` has the normalized weight
recorded here.  The definition is independent of a choice of cyclic generator of `H`; cyclicity
is needed only for the lower bound below. -/
noncomputable def crossingConstant {G H : Type*} [Fintype G] [Group H] [Fintype H]
    (f : ℕ) : ℝ :=
  (taggedElements (H := H) f).card /
    ((Fintype.card G : ℝ) * (Fintype.card H : ℝ))

/-- The tagged part of a cyclic crossing approaches the full `1 / #G` contribution as the
auxiliary level grows.  More precisely, if `f ^ r` divides `#H`, the crossing constant is at least
`(1 - 2⁻ʳ) ^ #f.primeFactors / #G`.

The cardinality estimate is the generic `IsCyclic.le_card_filter_dvd_orderOf` theorem.  This
lemma only supplies the Chebotarev normalization and deliberately keeps the two group orders
separate, as they play different roles in the crossing. -/
theorem le_crossingConstant {G H : Type*} [Nonempty G] [Fintype G] [Group H] [Fintype H]
    [IsCyclic H] (f r : ℕ) (hr : 1 ≤ r) (hfr : f ^ r ∣ Nat.card H) :
    (1 - (2 : ℝ)⁻¹ ^ r) ^ f.primeFactors.card / (Fintype.card G : ℝ) ≤
      crossingConstant (G := G) (H := H) f := by
  have hfr' : f ^ r ∣ Fintype.card H := by simpa only [Nat.card_eq_fintype_card] using hfr
  have hbound := IsCyclic.le_card_filter_dvd_orderOf (α := H) (f := f) hr hfr'
  have hbound' :
      ((1 - (2 : ℚ)⁻¹ ^ r) ^ f.primeFactors.card * Fintype.card H : ℚ) ≤
        (taggedElements (H := H) f).card := by
    simpa [taggedElements, Nat.card_eq_fintype_card] using hbound
  have hbound'' :
      ((((1 - (2 : ℚ)⁻¹ ^ r) ^ f.primeFactors.card * Fintype.card H : ℚ) : ℝ)) ≤
        ((taggedElements (H := H) f).card : ℝ) := by
    exact_mod_cast hbound'
  have hcast_factor :
      (((1 - (2 : ℚ)⁻¹ ^ r) ^ f.primeFactors.card : ℚ) : ℝ) =
        (1 - (2 : ℝ)⁻¹ ^ r) ^ f.primeFactors.card := by
    rw [Rat.cast_pow, Rat.cast_sub, Rat.cast_pow, Rat.cast_inv]
    norm_num
  have hbound''' :
      ((1 - (2 : ℝ)⁻¹ ^ r) ^ f.primeFactors.card * (Fintype.card H : ℝ)) ≤
        ((taggedElements (H := H) f).card : ℝ) := by
    simpa only [Rat.cast_mul, Rat.cast_natCast, hcast_factor] using hbound''
  have hG : (0 : ℝ) < Fintype.card G := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hH : (0 : ℝ) < Fintype.card H := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card H)
  rw [crossingConstant]
  apply (div_le_div_iff₀ hG (mul_pos hG hH)).2
  calc
    (1 - (2 : ℝ)⁻¹ ^ r) ^ f.primeFactors.card *
        (Fintype.card G * Fintype.card H : ℝ) =
      Fintype.card G *
        ((1 - (2 : ℝ)⁻¹ ^ r) ^ f.primeFactors.card * Fintype.card H) := by ring
    _ ≤ Fintype.card G * (taggedElements (H := H) f).card :=
        mul_le_mul_of_nonneg_left hbound''' hG.le
    _ = (taggedElements (H := H) f).card * Fintype.card G := by ring

end TauCeti.NumberField.Chebotarev
