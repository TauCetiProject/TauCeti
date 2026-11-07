/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Digits.Defs

/-!
# Short redundant radix words

Digits up to `2k`, rather than only `k - 1`, represent every integer in `[0, 2k^n]`
using exactly `n` digits, provided `n` is positive. Words are most significant digit first;
the endpoint `2k^n` is included. Fixed-length words let equal automaton prefix states control
whole doubled radix blocks, including noncanonical representations.

## References

* Thijmen J. P. Krebs, *A more reasonable proof of Cobham's theorem* (2018), §3,
  the interval-cover assertion after the choice of the redundant digit alphabet.
-/

public section

namespace Nat

/-- Every value up to `2k^n` has a most-significant-first word of exactly `n` digits from
`0, …, 2k`. The positive-length hypothesis is essential at the upper endpoint. -/
theorem exists_redundant_word_of_le_two_mul_pow {k n z : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hz : z ≤ 2 * k ^ n) :
    ∃ w : List (Fin (2 * k + 1)), w.length = n ∧ ofDigits k (w.map Fin.val).reverse = z := by
  induction n generalizing z with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      refine ⟨[⟨z, by simpa using Nat.lt_succ_of_le hz⟩], by simp, ?_⟩
      simp
    · have hq : z / k ≤ 2 * k ^ n := by
        apply (Nat.div_le_div_right hz).trans
        rw [pow_succ, ← Nat.mul_assoc, Nat.mul_div_cancel _ hk]
      obtain ⟨w, hw, hval⟩ := ih (by omega) hq
      refine ⟨w ++ [⟨z % k, lt_of_lt_of_le (Nat.mod_lt z hk) (by omega)⟩], by simp [hw], ?_⟩
      simp only [List.map_append, List.map_singleton, List.reverse_append,
        List.reverse_singleton, List.singleton_append, ofDigits_cons, hval]
      exact Nat.mod_add_div z k

-- The upper endpoint is represented by a legal, noncanonical digit.
example : ofDigits 2 (([4, 0] : List (Fin 5)).map Fin.val).reverse = 8 := by decide

-- Zero has an all-zero word of every length, including length zero.
example (k n : ℕ) :
    ofDigits k (((List.replicate n 0 : List (Fin (2 * k + 1))).map Fin.val).reverse) = 0 := by
  simp

-- No positive value has a word of length zero.
example : ¬ ∃ w : List (Fin 5), w.length = 0 ∧ ofDigits 2 (w.map Fin.val).reverse = 2 := by
  simp

end Nat
