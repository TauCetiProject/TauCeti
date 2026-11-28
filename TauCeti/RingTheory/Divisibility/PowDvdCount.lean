/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nakayama

/-!
# Power-divisibility counting and local-ring Nakayama elimination

This file collects elementary divisibility and Nakayama-type bounds used to estimate colengths
from elementary divisors over a local ring.

## Main results

* `TauCeti.prod_dvd_pow_sum_card`: if every `t i` divides `w ^ x`, then `∏ i, t i` divides
  `w ^ ∑ δ ∈ Finset.range x, #{i | ¬ t i ∣ w ^ δ}`.
* `TauCeti.pow_sub_dvd_of_pow_dvd_pow_mul`: over a domain, if `w ≠ 0` and `w ^ m ∣ w ^ d * x`,
  then `w ^ (m - d) ∣ x`.
* `TauCeti.smul_top_le_of_le_sup_smul_top`: over a local ring `O`, if `w ∈ maximalIdeal O`,
  `a * w ∣ u`, and `a • ⊤ ≤ G ⊔ u • ⊤` inside `E → O`, then `a • ⊤ ≤ G`.

## References

* Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`),
  `src/New/UpperBound/ElementaryDivisors/Edges.lean`
  (`New.prod_dvd_pow_sum_card`, `New.pow_sub_dvd_of_pow_dvd_pow_mul`) and
  `src/New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean`
  (`New.smul_top_le_of_le_sup_smul_top`).
-/

public section

namespace TauCeti

open Finset IsLocalRing Submodule
open scoped Pointwise

/-- If every `t i` divides `w ^ x`, then `∏ i, t i` divides `w ^ l`, where `l` counts the pairs
`(i, δ)` with `δ < x` such that `¬ t i ∣ w ^ δ`. -/
theorem prod_dvd_pow_sum_card {O I : Type*} [CommRing O] [DecidableRel fun y z : O ↦ y ∣ z]
    [Fintype I] {t : I → O} {w : O} {x : ℕ} (ht : ∀ i : I, t i ∣ w ^ x) :
    ∏ i : I, t i ∣ w ^ ∑ δ ∈ range x, (univ.filter fun i : I ↦ ¬t i ∣ w ^ δ).card := by
  have h_one (i : I) : t i ∣ w ^ ((range x).filter fun δ ↦ ¬t i ∣ w ^ δ).card := by
    have h_ex : ∃ l : ℕ, t i ∣ w ^ l := ⟨x, ht i⟩
    have h_range : range (Nat.find h_ex) ⊆ (range x).filter fun δ ↦ ¬t i ∣ w ^ δ := by
      simp only [subset_iff, mem_filter, Finset.mem_range]
      exact fun δ hδ ↦ ⟨hδ.trans_le (Nat.find_min' h_ex (ht i)), Nat.find_min h_ex hδ⟩
    refine (Nat.find_spec h_ex).trans (pow_dvd_pow w ?_)
    simpa only [Finset.card_range] using card_le_card h_range
  have h_count : ∑ i : I, ((range x).filter fun δ ↦ ¬t i ∣ w ^ δ).card =
      ∑ δ ∈ range x, (univ.filter fun i : I ↦ ¬t i ∣ w ^ δ).card := by
    simp only [card_filter, sum_comm (s := range x)]
  rw [← h_count, ← prod_pow_eq_pow_sum]
  exact prod_dvd_prod_of_dvd _ _ fun i _ ↦ h_one i

/-- Cancelling a power of a nonzero element `w` in a domain: if `w ^ m ∣ w ^ d * x`, then
`w ^ (m - d) ∣ x`. -/
theorem pow_sub_dvd_of_pow_dvd_pow_mul {O : Type*} [CommRing O] [IsDomain O] {w x : O}
    (hw : w ≠ 0) {m d : ℕ} (h_dvd : w ^ m ∣ w ^ d * x) : w ^ (m - d) ∣ x := by
  obtain hmd | hdm := le_total m d
  · simp [Nat.sub_eq_zero_of_le hmd]
  · rwa [← Nat.add_sub_cancel' hdm, pow_add, mul_dvd_mul_iff_left (pow_ne_zero d hw)] at h_dvd

/-- Nakayama elimination for scalar multiples on `E → O` over a local ring `O`: if
`w ∈ maximalIdeal O`, `a * w ∣ u`, and `a • ⊤ ≤ G ⊔ u • ⊤`, then `a • ⊤ ≤ G`. -/
theorem smul_top_le_of_le_sup_smul_top {O E : Type*} [CommRing O] [IsLocalRing O] [Finite E]
    {a u w : O} {G : Submodule O (E → O)} (hw : w ∈ maximalIdeal O) (hu : a * w ∣ u)
    (h_le : a • (⊤ : Submodule O (E → O)) ≤ G ⊔ u • ⊤) :
    a • (⊤ : Submodule O (E → O)) ≤ G := by
  have h_small : u • ⊤ ≤ maximalIdeal O • a • (⊤ : Submodule O (E → O)) := by
    obtain ⟨v, rfl : u = a * w * v⟩ := hu
    rintro _ ⟨η, -, rfl⟩
    have h_assoc : (a * w * v) • η = w • a • v • η := by rw [mul_comm a w, mul_smul, mul_smul]
    exact Set.mem_of_eq_of_mem h_assoc (smul_mem_smul hw (smul_mem_pointwise_smul _ a ⊤ mem_top))
  exact le_of_le_smul_of_le_jacobson (Module.Finite.fg_top.map _)
    (IsLocalRing.ringJacobson_eq_maximalIdeal _).ge (h_le.trans (sup_le_sup_left h_small G))

end TauCeti
