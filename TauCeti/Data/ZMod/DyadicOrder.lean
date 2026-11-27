/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Multiplicity
import TauCeti.Data.ZMod.OrderOf

/-!
# Orders modulo powers of two

For `k ≥ 1`, an odd residue modulo `2^(t+k)` raised to `2^k` equals `1` precisely when its
reduction modulo `2^t` is `1` or `-1`. Avoiding these two classes thus gives a divisibility
bound for the multiplicative order at higher levels.
-/

public section

namespace ZMod

/-- An odd residue modulo `2^(t+k)` is killed by `2^k`, for `k ≥ 1`, exactly when it reduces
modulo `2^t` to one of the two signs of `1`. This uses the dyadic lifting-the-exponent
formula `Nat.multiplicity_pow_two_sub_one`. -/
theorem natCast_pow_two_pow_eq_one_iff {a t k : ℕ} (ha : Odd a) (hk : 0 < k) :
    (a : ZMod (2 ^ (t + k))) ^ (2 ^ k) = 1 ↔ 2 ^ t ∣ a - 1 ∨ 2 ^ t ∣ a + 1 := by
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt ha.pos) with h | h
  · subst a
    simp
  have hpow : 1 < a ^ (2 ^ k) := Nat.one_lt_pow (by positivity) h
  have hval := Nat.multiplicity_pow_two_sub_one h ha.not_two_dvd_nat
    (show 2 ^ k ≠ 0 by positivity) (even_two.pow_of_ne_zero hk.ne')
  have hvpow : multiplicity 2 (2 ^ k) = k := multiplicity_pow_self_of_prime
    (Nat.prime_iff.mp Nat.prime_two) k
  have hodd := Nat.odd_iff.mp ha
  have hminus : 2 ∣ a - 1 := by omega
  have hplus : 2 ∣ a + 1 := by omega
  -- Of the two consecutive even numbers `a ± 1`, exactly one has multiplicity one.
  have hone : multiplicity 2 (a - 1) = 1 ∨ multiplicity 2 (a + 1) = 1 := by
    by_cases hfour : 4 ∣ a - 1
    · right
      exact multiplicity_eq_of_dvd_of_not_dvd (by simpa using hplus) (by
        norm_num
        omega)
    · left
      exact multiplicity_eq_of_dvd_of_not_dvd (by simpa using hminus) (by simpa using hfour)
  have hval₀ : 1 ≤ multiplicity 2 (a - 1) :=
    (Nat.pow_dvd_iff_le_multiplicity (by decide) (by omega)).mp (by simpa using hminus)
  have hval₁ : 1 ≤ multiplicity 2 (a + 1) :=
    (Nat.pow_dvd_iff_le_multiplicity (by decide) (by omega)).mp (by simpa using hplus)
  rw [← orderOf_dvd_iff_pow_eq_one, ← dvd_pow_sub_one_iff_orderOf_natCast_dvd ha.pos,
    Nat.pow_dvd_iff_le_multiplicity (by decide) (Nat.sub_ne_zero_of_lt hpow),
    Nat.pow_dvd_iff_le_multiplicity (by decide) (by omega : a - 1 ≠ 0),
    Nat.pow_dvd_iff_le_multiplicity (by decide) (by omega : a + 1 ≠ 0)]
  rw [hvpow] at hval
  omega

/-- At a modulus divisible by `2^(t+k)`, the order of the negative of a residue is divisible
by `2^(k+1)` if the residue is neither `1` nor `-1` modulo `2^t`. For an even input the
order is zero, since the residue is not a unit. -/
theorem two_pow_succ_dvd_orderOf_neg_natCast {a n t k : ℕ}
    (hn : 2 ^ (t + k) ∣ n) (hminus : ¬ 2 ^ t ∣ a - 1) (hplus : ¬ 2 ^ t ∣ a + 1) :
    2 ^ (k + 1) ∣ orderOf (-(a : ZMod n)) := by
  have ht : 0 < t := Nat.pos_of_ne_zero (by rintro rfl; simp at hminus)
  let m := 2 ^ (t + k)
  let f : ZMod n →+* ZMod m := castHom hn (ZMod m)
  have hmap : orderOf (f (-(a : ZMod n))) ∣ orderOf (-(a : ZMod n)) :=
    orderOf_map_dvd f.toMonoidHom _
  rw [map_neg, map_natCast] at hmap
  refine dvd_trans ?_ hmap
  by_cases ha : Odd a
  swap
  · have hnot : ¬ IsUnit (-(a : ZMod m)) := by
      rw [IsUnit.neg_iff, isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega : 0 < t + k),
        Nat.coprime_two_right]
      exact ha
    have hz : orderOf (-(a : ZMod m)) = 0 :=
      Nat.eq_zero_of_not_pos (hnot ∘ IsOfFinOrder.isUnit ∘ orderOf_pos_iff.mp)
    simp [hz]
  let u : (ZMod m)ˣ := unitOfCoprime a ((Nat.coprime_two_right.mpr ha).pow_right (t + k))
  have hm₀ : NeZero m := ⟨by dsimp [m]; positivity⟩
  have htot : m.totient = 2 ^ (t + k - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (by omega : 0 < t + k)]
    simp
  have horder : orderOf (-u) ∣ 2 ^ (t + k - 1) := by
    rw [← htot, ← card_units_eq_totient]
    exact orderOf_dvd_card
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp horder
  have hne : (-u) ^ (2 ^ k) ≠ 1 := by
    intro he
    have hcast : (-(a : ZMod m)) ^ (2 ^ k) = 1 := by
      simpa only [u, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, coe_unitOfCoprime]
        using congrArg (fun v : (ZMod m)ˣ ↦ (v : ZMod m)) he
    rcases eq_zero_or_pos k with rfl | hk
    · simp only [m, pow_zero, pow_one] at hcast
      apply hplus
      rw [← natCast_eq_zero_iff, Nat.cast_add, Nat.cast_one, add_eq_zero_iff_neg_eq]
      exact hcast
    · rw [(even_two.pow_of_ne_zero hk.ne').neg_pow] at hcast
      exact (natCast_pow_two_pow_eq_one_iff ha hk).mp hcast |>.elim hminus hplus
  have hjk : k < j := by
    by_contra! hjk
    exact hne (orderOf_dvd_iff_pow_eq_one.mp (hj ▸ pow_dvd_pow 2 hjk))
  have hd : 2 ^ (k + 1) ∣ orderOf (-u) := hj ▸ pow_dvd_pow 2 (by omega)
  rw [← orderOf_units] at hd
  simpa only [u, Units.val_neg, coe_unitOfCoprime] using hd

end ZMod
