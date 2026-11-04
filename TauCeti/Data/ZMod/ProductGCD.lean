/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.List.Prime
public import Mathlib.Data.ZMod.Basic

/-!
# Gcds of products of residues

Taking a product in `ZMod n` before taking its representative does not change the gcd with `n`.
A prime therefore divides this gcd exactly when it divides a leaf gcd. This
includes the empty product and modulus zero.

For positive modulus, a prime detected at some leaf and a prime absent from every leaf certify
that the product gcd is a proper factor. Without the second condition a product gcd can equal
`n` even though some leaf gcds are proper factors. These facts are useful for batching
cross-differences in elliptic-curve factorization; see P. Zimmermann, *20 years of ECM* (2006),
§1, for the stage-2 product test.
-/

public section

namespace List

/-- Computing a product modulo `n` does not change its gcd with `n`, compared with multiplying
its natural representatives first. At modulus zero, representatives are absolute values. -/
theorem gcd_val_prod {n : ℕ} (L : List (ZMod n)) :
    Nat.gcd L.prod.val n = Nat.gcd (L.map ZMod.val).prod n := by
  rcases eq_or_ne n 0 with rfl | hn
  · induction L with
    | nil => simp
    | cons a L ih => simpa using congrArg (a.val * ·) ih
  · let : NeZero n := ⟨hn⟩
    have h : (((L.map ZMod.val).prod : ℕ) : ZMod n) = L.prod := by
      simp [Nat.cast_list_prod, List.map_map, Function.comp_def]
    rw [← h, ZMod.val_natCast, ← Nat.gcd_rec, Nat.gcd_comm]

/-- A prime divides the product gcd exactly when it divides some leaf gcd, without requiring
that it divide the modulus. In particular, the empty product has no prime divisor. -/
theorem prime_dvd_gcd_val_prod_iff {n : ℕ} (L : List (ZMod n)) {p : ℕ}
    (hp : p.Prime) :
    p ∣ Nat.gcd L.prod.val n ↔ ∃ t ∈ L, p ∣ Nat.gcd t.val n := by
  rw [gcd_val_prod]
  by_cases hpn : p ∣ n
  · simp only [Nat.dvd_gcd_iff, hpn, and_true]
    rw [hp.prime.dvd_prod_iff]
    simp
  · simp [Nat.dvd_gcd_iff, hpn]

/-- A product gcd is proper if one prime divisor of the modulus occurs in some leaf gcd and
another prime divisor occurs in none. No conclusion of primality for the gcd is asserted. -/
theorem one_lt_gcd_val_prod_and_lt {n : ℕ} [NeZero n] (L : List (ZMod n))
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqn : q ∣ n)
    (hpL : ∃ t ∈ L, p ∣ Nat.gcd t.val n)
    (hqL : ∀ t ∈ L, ¬q ∣ Nat.gcd t.val n) :
    1 < Nat.gcd L.prod.val n ∧ Nat.gcd L.prod.val n < n := by
  have hpG := (prime_dvd_gcd_val_prod_iff L hp).mpr hpL
  have hqG : ¬q ∣ Nat.gcd L.prod.val n := by
    rw [prime_dvd_gcd_val_prod_iff L hq]
    exact not_exists.mpr fun t => not_and.mpr (hqL t)
  have hpos : 0 < Nat.gcd L.prod.val n := Nat.gcd_pos_of_pos_right _ (NeZero.pos n)
  refine ⟨hp.one_lt.trans_le (Nat.le_of_dvd hpos hpG), ?_⟩
  exact lt_of_le_of_ne (Nat.gcd_le_right _ (NeZero.pos n)) fun h => hqG (by rwa [h])

end List
