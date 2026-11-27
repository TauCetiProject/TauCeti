/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.Nat.Dist
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Int.Order.Units
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import TauCeti.Data.ZMod.Units

/-!
# Terms of arithmetic progressions in `ℤ`

A progression with positive step contains a positive odd term if either its initial
term or its step is odd. The index can be chosen nonnegative. This is useful when a translation
must fix a congruence class while also arranging the sign and parity of a matrix entry.

When the initial term and the step are coprime, the progression also contains a term coprime to
any prescribed nonzero integer `m`.

For every non-unit `d`, the progression `1 + max |d| 2 * ℤ` avoids the multiples of `d`, so
integers of arbitrarily large absolute value avoid them.

## Main results

* `Int.exists_nat_add_mul_pos_odd`: a positive odd term at a nonnegative index.
* `Int.not_dvd_one_add_max_abs_mul`: `d ∤ 1 + max |d| 2 * k` for a non-unit `d`.
* `IsCoprime.exists_isCoprime_add_mul`: a progression `a + ℤ * b` with `a` and `b` coprime
  contains a term coprime to any nonzero `m : ℤ`.
* `Int.gcd_term_dvd_dist`: the gcd of two terms of a primitive progression divides the distance
  between their indices.
* `Int.eq_of_dvd_term_of_length_le`: a modulus at least the progression length divides at most
  one term of a primitive progression.
-/

public section

namespace Int

/-- A progression with positive step contains a positive odd term at a nonnegative index if its
initial term or its step is odd. -/
theorem exists_nat_add_mul_pos_odd (a : ℤ) {c : ℤ} (hc : 0 < c)
    (hodd : Odd a ∨ Odd c) : ∃ j : ℕ, 0 < a + j * c ∧ Odd (a + j * c) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-a)
  have hpos : 0 < a + (2 * (n + 1) : ℕ) * c := by
    push_cast
    have : (0 : ℤ) ≤ n := Nat.cast_nonneg n
    nlinarith
  by_cases ha : Odd a
  · refine ⟨2 * (n + 1), hpos, ?_⟩
    have hj : Even (((2 * (n + 1) : ℕ) : ℤ)) := by exact_mod_cast even_two_mul (n + 1)
    exact ha.add_even (hj.mul_right c)
  · have hcodd := hodd.resolve_left ha
    refine ⟨2 * (n + 1) + 1, ?_, ?_⟩
    · push_cast at hpos ⊢
      nlinarith
    · have hj : Odd (((2 * (n + 1) + 1 : ℕ) : ℤ)) := by
        exact_mod_cast odd_two_mul_add_one (n + 1)
      exact (Int.not_odd_iff_even.mp ha).add_odd (hj.mul hcodd)

/-- Every member of the progression `1 + max |d| 2 * ℤ` avoids the multiples of a non-unit `d`.

The modulus is `|d|` in the intended case, `2` being needed only for `d = 0`: there the multiples
of `d` are `{0}` alone, and what has to be said is that `1 + 2 * k` is odd, hence nonzero. -/
theorem not_dvd_one_add_max_abs_mul {d : ℤ} (hd : ¬ IsUnit d) (k : ℤ) :
    ¬ d ∣ 1 + max |d| 2 * k := by
  intro hdvd
  rcases eq_or_ne d 0 with rfl | hd0
  · simp at hdvd
    omega
  · have hd2 : 2 ≤ |d| := by
      have := abs_pos.mpr hd0
      have := isUnit_iff_abs_eq.not.mp hd
      omega
    rw [max_eq_left hd2, add_comm] at hdvd
    exact hd <| isUnit_of_dvd_one <|
      (dvd_add_right (((dvd_abs d d).mpr dvd_rfl).mul_right k)).mp hdvd

/-- The gcd of two terms of a primitive progression divides the distance between their indices.
See Bennett and Siksek, *A conjecture of Erdős, supersingular primes and short character sums*,
Lemma 3.1(i). -/
theorem gcd_term_dvd_dist {n d : ℤ} (h : n.gcd d = 1) (i j : ℕ) :
    (n + i * d).gcd (n + j * d) ∣ Nat.dist i j := by
  let g := (n + i * d).gcd (n + j * d)
  have hcop : IsCoprime (g : ℤ) d :=
    ((Int.isCoprime_iff_gcd_eq_one.mpr h).add_mul_right_left (i : ℤ)).of_isCoprime_of_dvd_left
      (Int.gcd_dvd_left ..)
  have hsub : (g : ℤ) ∣ ((j : ℤ) - i) * d := by
    simpa only [g, sub_mul, add_sub_add_left_eq_sub] using
      dvd_sub (Int.gcd_dvd_right (n + i * d) (n + j * d)) (Int.gcd_dvd_left ..)
  have hdist : ((j : ℤ) - i).natAbs = Nat.dist i j := by
    unfold Nat.dist
    omega
  exact hdist ▸ Int.ofNat_dvd_left.mp (hcop.dvd_of_dvd_mul_right hsub)

/-- A modulus at least the length divides at most one term of a primitive progression. -/
theorem eq_of_dvd_term_of_length_le {n d : ℤ} {k q i j : ℕ} (h : n.gcd d = 1) (hq : k ≤ q)
    (hi : i < k) (hj : j < k) (hqi : (q : ℤ) ∣ n + i * d) (hqj : (q : ℤ) ∣ n + j * d) :
    i = j := by
  by_contra hne
  have := Nat.le_of_dvd (Nat.dist_pos_of_ne hne)
    ((Int.dvd_gcd hqi hqj).trans (gcd_term_dvd_dist h i j))
  unfold Nat.dist at this
  omega

end Int

/-- An arithmetic progression `a + ℤ * b` with coprime initial term `a` and step `b` contains a
term coprime to any nonzero integer `m`. The hypothesis `m ≠ 0` is needed because at `m = 0`
coprimality to `m` means `±1`, which `3 + 5 * ℤ` never attains. -/
theorem IsCoprime.exists_isCoprime_add_mul {a b m : ℤ} (hab : IsCoprime a b) (hm : m ≠ 0) :
    ∃ k : ℤ, IsCoprime (a + k * b) m := by
  have : NeZero m.natAbs := ⟨Int.natAbs_ne_zero.mpr hm⟩
  let u : (ZMod b.natAbs)ˣ :=
    ZMod.unitOfIsCoprime a (hab.of_isCoprime_of_dvd_right Int.natAbs_dvd_self)
  obtain ⟨t, ht_cop, ht_eq⟩ := ZMod.exists_isCoprime_mul_intCast_eq m.natAbs u
  rw [ZMod.coe_unitOfIsCoprime] at ht_eq
  obtain ⟨k, hk⟩ : b ∣ t - a := Int.natAbs_dvd.mp
    ((ZMod.intCast_eq_intCast_iff_dvd_sub a t b.natAbs).mp ht_eq.symm)
  have ht : a + k * b = t := by linarith
  have hcop' : IsCoprime t ((m.natAbs : ℤ) * b.natAbs) := by simpa only [Nat.cast_mul] using ht_cop
  exact ⟨k, ht ▸ hcop'.of_mul_right_left.of_isCoprime_of_dvd_right Int.dvd_natAbs_self⟩
