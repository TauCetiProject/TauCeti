/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.Algebra.Group.Pow

/-!
# Idempotent powers and short products in a finite monoid

Let `N` be a finite monoid with `|N|` elements. Every element `t` of `N` has an idempotent power:
there is an exponent `p` with `0 < p ≤ |N|` and `t ^ (2 * p) = t ^ p`. Every product of a list of
elements of `N` is already the product of a sublist of length less than `|N|`.

Both facts bound the data needed to evaluate a morphism into a finite monoid on long words. If
`t ^ p` is idempotent, the powers `t ^ k` with `k ≥ p` depend only on `k` modulo `p`
(`TauCeti.pow_eq_pow_of_modEq_of_pow_add_eq`, in `TauCeti.Algebra.Group.Pow`); and every value of
a word is the value of a word of length less than `|N|`. This is how they are used in
recompression for equations in free groups and in free monoids with involution.

Since the exponent `p` is at most `|N|`, it divides `m !` for every `m ≥ |N|`. Hence the factorial
powers `t ^ m !` are all equal from `m = |N|` on, and this common value is the idempotent power of
`t`. The threshold `|N|` depends only on the monoid, not on `t`, which is what makes factorial
powers converge in an inverse limit of finite monoids, as in Hida's ordinary projector.

## Main results

* `TauCeti.exists_pow_two_mul_eq_pow`: every element `t` of a finite monoid `N` has a power
  `t ^ p` with `0 < p ≤ |N|` and `t ^ (2 * p) = t ^ p`.
* `List.exists_sublist_length_lt_card_prod_eq`: the product of a list of elements of a finite
  monoid `N` is the product of a sublist of length less than `|N|`.
* `TauCeti.pow_factorial_eq_pow_factorial_of_card_le`: `t ^ n ! = t ^ m !` whenever
  `|N| ≤ m ≤ n`.
* `TauCeti.isIdempotentElem_pow_factorial_of_card_le`: `t ^ m !` is idempotent whenever
  `|N| ≤ m`.

## References

* V. Diekert, A. Jez, W. Plandowski, *Finding all solutions of equations in free groups and
  monoids with involution*, arXiv:1405.5133, §3.2 (idempotent power) and the proof of Lemma 11.
* C. B. Khare, J. A. Thorne, *Potential automorphy and the Leopoldt conjecture*, Amer. J. Math.
  139 (2017), §2.4, Lemma 2.10 and its proof (factorial powers in a finite set).
-/

public section

variable {N : Type*} [Monoid N]

namespace List

/-- The product of a list of elements of a finite monoid is the product of a sublist of length
less than the cardinality of the monoid. -/
theorem exists_sublist_length_lt_card_prod_eq [Finite N] (l : List N) :
    ∃ u : List N, u.Sublist l ∧ u.length < Nat.card N ∧ u.prod = l.prod := by
  classical
  have := Fintype.ofFinite N
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  by_cases hl : l.length < Nat.card N
  · exact ⟨l, .refl l, hl, rfl⟩
  -- Two of the products of the prefixes of `l` of lengths `0, …, |l|` coincide; cutting out the
  -- segment between them leaves a shorter sublist with the same product.
  obtain ⟨j, hj, k, hk, hne, hjk⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (l.length + 1)) (t := Finset.univ) (f := fun k ↦ (l.take k).prod)
    (by simp only [Finset.card_range, Finset.card_univ, ← Nat.card_eq_fintype_card]; lia)
    (fun _ _ ↦ Finset.mem_univ _)
  rw [Finset.mem_range] at hj hk
  wlog hlt : j < k generalizing j k
  · exact this k hk j hj hne.symm hjk.symm (hne.lt_or_gt.resolve_left hlt)
  have hshort : (l.take j ++ l.drop k).length < n := by grind
  obtain ⟨u, hu, hlen, hprod⟩ := ih _ hshort (l.take j ++ l.drop k) rfl
  refine ⟨u, hu.trans ?_, hlen, ?_⟩
  · simpa using (drop_sublist_drop_left l hlt.le).append_left (l.take j)
  · rw [hprod, prod_append, hjk, ← prod_append, take_append_drop]

end List

namespace TauCeti

/-- In a finite monoid every element `t` has an idempotent power `t ^ p`, that is
`t ^ (2 * p) = t ^ p`, whose exponent `p` is positive and at most the cardinality of the monoid. -/
theorem exists_pow_two_mul_eq_pow [Finite N] (t : N) :
    ∃ p, 0 < p ∧ p ≤ Nat.card N ∧ t ^ (2 * p) = t ^ p := by
  -- The product `t ^ |N|` of `|N|` copies of `t` is the product `t ^ x` of a sublist, `x < |N|`.
  obtain ⟨u, hu, hlen, hprod⟩ :=
    (List.replicate (Nat.card N) t).exists_sublist_length_lt_card_prod_eq
  obtain ⟨x, -, rfl⟩ := List.sublist_replicate_iff.1 hu
  rw [List.length_replicate] at hlen
  obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le hlen.le
  rw [List.prod_replicate, List.prod_replicate, hq] at hprod
  -- So `t ^ (x + q) = t ^ x` with `0 < q` and `x + q = |N|`: the least multiple of `q` above `x`
  -- will do.
  have hq0 : 0 < q := by lia
  have hx := Nat.lt_mul_div_succ x hq0
  have hle := Nat.mul_div_le x q
  refine ⟨q * (x / q + 1), by lia, by lia, ?_⟩
  refine pow_eq_pow_of_modEq_of_pow_add_eq hprod.symm (by lia) hx.le ?_
  simp [Nat.ModEq, mul_left_comm]

open Nat in
/-- In a finite monoid the factorial powers of an element are constant from the cardinality of
the monoid on: `t ^ n ! = t ^ m !` whenever `|N| ≤ m ≤ n`. -/
theorem pow_factorial_eq_pow_factorial_of_card_le [Finite N] (t : N) {m n : ℕ}
    (hm : Nat.card N ≤ m) (hmn : m ≤ n) : t ^ n ! = t ^ m ! := by
  obtain ⟨p, hp, hpN, h⟩ := exists_pow_two_mul_eq_pow t
  rw [two_mul] at h
  have hpm : p ∣ m ! := Nat.dvd_factorial hp (hpN.trans hm)
  have hpn : p ∣ n ! := Nat.dvd_factorial hp (hpN.trans (hm.trans hmn))
  exact pow_eq_pow_of_modEq_of_pow_add_eq h (Nat.le_of_dvd (Nat.factorial_pos n) hpn)
    (Nat.le_of_dvd (Nat.factorial_pos m) hpm)
    ((Nat.modEq_zero_iff_dvd.2 hpn).trans (Nat.modEq_zero_iff_dvd.2 hpm).symm)

open Nat in
/-- In a finite monoid the factorial power `t ^ m !` is idempotent as soon as `|N| ≤ m`. -/
theorem isIdempotentElem_pow_factorial_of_card_le [Finite N] (t : N) {m : ℕ}
    (hm : Nat.card N ≤ m) : IsIdempotentElem (t ^ m !) := by
  obtain ⟨p, hp, hpN, h⟩ := exists_pow_two_mul_eq_pow t
  rw [two_mul] at h
  have hpm : p ∣ m ! := Nat.dvd_factorial hp (hpN.trans hm)
  have hle : p ≤ m ! := Nat.le_of_dvd (Nat.factorial_pos m) hpm
  rw [isIdempotentElem_iff, ← pow_add]
  refine pow_eq_pow_of_modEq_of_pow_add_eq h (by lia) hle ?_
  exact (Nat.modEq_zero_iff_dvd.2 (Nat.dvd_add hpm hpm)).trans (Nat.modEq_zero_iff_dvd.2 hpm).symm

end TauCeti
