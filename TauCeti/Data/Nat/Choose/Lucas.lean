/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Lucas

/-!
# Lucas' theorem for a lower index divisible by `p ^ k`

Mathlib's `Choose.choose_mul_mul_modEq_choose_nat` reduces `choose (p * a) (p * b)` modulo a prime
`p` to `choose a b`, and `Choose.choose_pow_mul_pow_mul_modEq_choose_nat` reduces
`choose (p ^ k * a) (p ^ k * b)` to `choose a b`. This file generalises the latter to an arbitrary
upper index: a lower index `p ^ k * b` has `k` vanishing last base-`p` digits, so modulo `p`,
`choose n (p ^ k * b)` depends only on the digits of `n` at positions `k` and higher, that is on
`n / p ^ k`. At `b = 1` it is congruent modulo `p` to the digit of `n` in position `k`. The proof
specialises Mathlib's iterated Lucas theorem `Choose.choose_modEq_choose_mul_prod_range_choose`.

The case `k = 1`, `n = p * a + c` with `c < p` is the case in which the upper index has a nonzero
last base-`p` digit `c` and the lower index is still divisible by `p`: the extra digit contributes
the factor `choose c 0 = 1`. At `p = 2` it computes the parity of `choose (2a + 1) (2b)`, which is
what sign bookkeeping with binomial exponents of odd upper index needs.

When `p` divides `n ≠ 0`, the last base-`p` digit of `n - 1` is `p - 1`, so Mathlib's one-digit
Lucas step `Choose.choose_modEq_choose_mod_mul_choose_div_nat` also gives
`choose (n - 1) (p - 1) ≡ 1 [MOD p]`; this is the congruence behind Frobenius descent for
symmetric 2-cocycles.

## Main results

* `Choose.choose_pow_mul_modEq_choose_div_nat`:
  `choose n (p ^ k * b) ≡ choose (n / p ^ k) b [MOD p]`.
* `Choose.choose_mul_add_mul_modEq_choose_nat`: `choose (p * a + c) (p * b) ≡ choose a b [MOD p]`
  for `c < p`.
* `Choose.choose_sub_one_sub_one_modEq_one`: `choose (n - 1) (p - 1) ≡ 1 [MOD p]` when `p ∣ n`
  and `n ≠ 0`.
* `TauCeti.Choose.choose_mul_choose_add_choose_modEq`: the parity identity
  `C(2m, 2) C(2m - 1, 2) + C(2m + 1, 4) ≡ C(m, 2) [MOD 2]`.
-/

public section

namespace Choose

variable {p a b c : ℕ} [Fact p.Prime]

/-- For a prime `p`, `choose n (p ^ k * b)` is congruent to `choose (n / p ^ k) b` modulo `p`:
the last `k` base-`p` digits of the lower index vanish, so by Lucas' theorem only the digits of `n`
at positions `k` and higher matter. At `b = 1` it says that `choose n (p ^ k)` is congruent to
`n / p ^ k`, whose residue is the base-`p` digit of `n` in position `k`; so at `p = 2`,
`choose n (2 ^ k)` is odd exactly when bit `k` of `n` is set. -/
theorem choose_pow_mul_modEq_choose_div_nat (n k b : ℕ) :
    Nat.choose n (p ^ k * b) ≡ Nat.choose (n / p ^ k) b [MOD p] := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [← Int.natCast_modEq_iff]
  refine (choose_modEq_choose_mul_prod_range_choose k).trans ?_
  -- Each of the last `k` base-`p` digits of `p ^ k * b` is `0`, contributing `choose _ 0 = 1`.
  rw [Finset.prod_eq_one fun i hi => ?_, Nat.mul_div_cancel_left _ (pow_pos hp k),
    Nat.cast_one, mul_one]
  replace hi := Finset.mem_range.mp hi
  rw [← pow_mul_pow_sub p hi.le, mul_assoc, Nat.mul_div_cancel_left _ (pow_pos hp i),
    Nat.mod_eq_zero_of_dvd ((dvd_pow_self p (Nat.sub_ne_zero_of_lt hi)).mul_right b),
    Nat.choose_zero_right]

/-- For primes `p` and `c < p`, `choose (p * a + c) (p * b)` is congruent to `choose a b` modulo
`p`. This is Lucas' theorem for a lower index divisible by `p`: the case `k = 1` of
`choose_pow_mul_modEq_choose_div_nat`. -/
theorem choose_mul_add_mul_modEq_choose_nat (hc : c < p) :
    Nat.choose (p * a + c) (p * b) ≡ Nat.choose a b [MOD p] := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  simpa [Nat.mul_add_div hp, Nat.div_eq_of_lt hc] using
    choose_pow_mul_modEq_choose_div_nat (p := p) (p * a + c) 1 b

/-- For a prime `p` dividing `n ≠ 0`, `choose (n - 1) (p - 1)` is congruent to `1` modulo `p`:
the last base-`p` digit of `n - 1` is `p - 1`, and Lucas' theorem applies. -/
theorem choose_sub_one_sub_one_modEq_one {n : ℕ} (hpn : p ∣ n) (hn : n ≠ 0) :
    Nat.choose (n - 1) (p - 1) ≡ 1 [MOD p] := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hlt : p - 1 < p := Nat.sub_lt hp one_pos
  obtain ⟨q, rfl⟩ := hpn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (right_ne_zero_of_mul hn)
  -- `p * (m + 1) - 1` has last base-`p` digit `p - 1`, above which come the digits of `m`.
  have hsplit : p * (m + 1) - 1 = p * m + (p - 1) := by
    rw [Nat.mul_succ, Nat.add_sub_assoc (Nat.succ_le_of_lt hp)]
  refine choose_modEq_choose_mod_mul_choose_div_nat.trans ?_
  simp [hsplit, Nat.mod_eq_of_lt hlt, Nat.mul_add_div hp, Nat.div_eq_of_lt hlt, Nat.ModEq.refl]

end Choose

namespace TauCeti.Choose

/-- The parity identity
`C(2m, 2) C(2m - 1, 2) + C(2m + 1, 4) ≡ C(m, 2) [MOD 2]`. -/
theorem choose_mul_choose_add_choose_modEq (m : ℕ) :
    (2 * m).choose 2 * (2 * m - 1).choose 2 + (2 * m + 1).choose 4 ≡ m.choose 2 [MOD 2] := by
  rcases m with _ | k
  · rfl
  have hN := _root_.Choose.choose_mul_mul_modEq_choose_nat (p := 2) (a := k + 1) (b := 1)
  have hC := _root_.Choose.choose_mul_add_mul_modEq_choose_nat
    (p := 2) (a := k) (b := 1) one_lt_two
  have hD := _root_.Choose.choose_mul_add_mul_modEq_choose_nat
    (p := 2) (a := k + 1) (b := 2) one_lt_two
  simp only [mul_one, Nat.reduceMul, Nat.choose_one_right] at hN hC hD
  have hk : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  rw [hk]
  refine (Nat.ModEq.add (Nat.ModEq.mul hN hC) hD).trans ?_
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self k
  rw [mul_comm, ht]
  unfold Nat.ModEq
  omega

end Choose

end TauCeti
