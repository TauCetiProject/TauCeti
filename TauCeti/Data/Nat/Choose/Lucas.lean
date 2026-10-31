/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Lucas

/-!
# Lucas' theorem with a nonzero last digit on top

Mathlib's `Choose.choose_mul_mul_modEq_choose_nat` reduces `choose (p * a) (p * b)` modulo a prime
`p` to `choose a b`. This file records the companion case in which the upper index has a nonzero
last base-`p` digit `c < p` and the lower index is still divisible by `p`: the extra digit
contributes the factor `choose c 0 = 1`. At `p = 2` it computes the parity of
`choose (2a + 1) (2b)`, which is what sign bookkeeping with binomial exponents of odd upper index
needs.

When `p` divides `n ≠ 0`, the last base-`p` digit of `n - 1` is `p - 1`, so Lucas' theorem also
gives `choose (n - 1) (p - 1) ≡ 1 [MOD p]`; this is the congruence behind Frobenius descent for
symmetric 2-cocycles.

Grouping the base-`p` digits in blocks of `h`, Lucas' theorem also holds in base `pʰ`: the last
`h` digits contribute the binomial coefficient of the residues modulo `pʰ`.

## Main results

* `Choose.choose_mul_add_mul_modEq_choose_nat`: `choose (p * a + c) (p * b) ≡ choose a b [MOD p]`
  for `c < p`.
* `Choose.choose_sub_one_sub_one_modEq_one`: `choose (n - 1) (p - 1) ≡ 1 [MOD p]` when `p ∣ n`
  and `n ≠ 0`.
* `Choose.choose_pow_mul_add_modEq_choose_mul_choose_nat`:
  `choose (p ^ h * m + a) (p ^ h * l + b) ≡ choose m l * choose a b [MOD p]` for `a, b < p ^ h`.
* `TauCeti.Choose.choose_mul_choose_add_choose_modEq`: the parity identity
  `C(2m, 2) C(2m - 1, 2) + C(2m + 1, 4) ≡ C(m, 2) [MOD 2]`.
-/

public section

namespace Choose

variable {p a b c : ℕ} [Fact p.Prime]

/-- For primes `p` and `c < p`, `choose (p * a + c) (p * b)` is congruent to `choose a b` modulo
`p`. This is Lucas' theorem for a lower index divisible by `p`. -/
theorem choose_mul_add_mul_modEq_choose_nat (hc : c < p) :
    Nat.choose (p * a + c) (p * b) ≡ Nat.choose a b [MOD p] := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  refine choose_modEq_choose_mod_mul_choose_div_nat.trans ?_
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hc, Nat.mul_add_div hp, Nat.div_eq_of_lt hc, add_zero,
    Nat.mul_mod_right, Nat.mul_div_cancel_left _ hp, Nat.choose_zero_right, one_mul]

/-- For a prime `p` dividing `n ≠ 0`, `choose (n - 1) (p - 1)` is congruent to `1` modulo `p`:
the last base-`p` digit of `n - 1` is `p - 1`, and Lucas' theorem applies. -/
theorem choose_sub_one_sub_one_modEq_one {n : ℕ} (hpn : p ∣ n) (hn : n ≠ 0) :
    Nat.choose (n - 1) (p - 1) ≡ 1 [MOD p] := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
  have h₁ : (p - 1) % p = p - 1 := Nat.mod_eq_of_lt (by omega)
  have h₂ : (p - 1) / p = 0 := Nat.div_eq_of_lt (by omega)
  have hmod : (n - 1) % p = p - 1 := by
    obtain ⟨q, rfl⟩ := hpn
    have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.2 (right_ne_zero_of_mul hn)
    have hpq : p ≤ p * q := Nat.le_mul_of_pos_right p hq
    have hsplit : p * q - 1 = p - 1 + p * (q - 1) := by rw [Nat.mul_sub_one]; omega
    rw [hsplit, Nat.add_mul_mod_self_left, h₁]
  refine choose_modEq_choose_mod_mul_choose_div_nat.trans ?_
  rw [hmod, h₁, h₂, Nat.choose_self, Nat.choose_zero_right]

/-- **Lucas' theorem in base `p ^ h`.** For a prime `p` and `a, b < p ^ h`, the binomial
coefficient `choose (p ^ h * m + a) (p ^ h * l + b)` is congruent to `choose m l * choose a b`
modulo `p`: the last `h` base-`p` digits of the two indices contribute `choose a b`. -/
theorem choose_pow_mul_add_modEq_choose_mul_choose_nat {h m l : ℕ} (ha : a < p ^ h)
    (hb : b < p ^ h) :
    Nat.choose (p ^ h * m + a) (p ^ h * l + b) ≡ Nat.choose m l * Nat.choose a b [MOD p] := by
  induction h generalizing a b with
  | zero =>
    obtain rfl : a = 0 := by simpa using ha
    obtain rfl : b = 0 := by simpa using hb
    simp [Nat.ModEq.refl]
  | succ h ih =>
    have hp : 0 < p := (Fact.out : p.Prime).pos
    have hdiv {c : ℕ} (hc : c < p ^ (h + 1)) : c / p < p ^ h :=
      (Nat.div_lt_iff_lt_mul hp).mpr (by rwa [← pow_succ])
    have hdigit (c n : ℕ) :
        (p ^ (h + 1) * n + c) % p = c % p ∧ (p ^ (h + 1) * n + c) / p = p ^ h * n + c / p := by
      rw [pow_succ', mul_assoc, Nat.mul_add_mod, Nat.mul_add_div hp]
      exact ⟨rfl, rfl⟩
    refine choose_modEq_choose_mod_mul_choose_div_nat.trans ?_
    rw [(hdigit a m).1, (hdigit a m).2, (hdigit b l).1, (hdigit b l).2]
    refine ((ih (hdiv ha) (hdiv hb)).mul_left _).trans ?_
    rw [mul_left_comm]
    exact (choose_modEq_choose_mod_mul_choose_div_nat.symm).mul_left _

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
