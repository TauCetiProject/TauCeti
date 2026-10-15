/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Lucas

import Lean.Elab.Tactic.Omega

/-!
# Lucas' theorem with a nonzero last digit on top

Mathlib's `Choose.choose_mul_mul_modEq_choose_nat` reduces `choose (p * a) (p * b)` modulo a prime
`p` to `choose a b`. This file records the companion case in which the upper index has a nonzero
last base-`p` digit `c < p` and the lower index is still divisible by `p`: the extra digit
contributes the factor `choose c 0 = 1`. At `p = 2` it computes the parity of
`choose (2a + 1) (2b)`, which is what sign bookkeeping with binomial exponents of odd upper index
needs.

## Main results

* `Choose.choose_mul_add_mul_modEq_choose_nat`: `choose (p * a + c) (p * b) ≡ choose a b [MOD p]`
  for `c < p`.
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
