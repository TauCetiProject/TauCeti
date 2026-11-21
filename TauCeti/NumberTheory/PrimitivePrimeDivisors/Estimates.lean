/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import TauCeti.Data.Nat.Pow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Arithmetic lower bounds for homogeneous cyclotomic estimates

For positive natural bases `b < a` and `n ≥ 3`, the ratio
`(a ^ n - b ^ n) / (a + b)` exceeds `n` except at `(a, b, n) = (2, 1, 3)`.
Every positive integral power of this ratio still exceeds `n` outside that exception.
Equivalently, `a ^ n - b ^ n > n * (a + b)` fails exactly at that triple.

These estimates apply to the lower bound for the homogeneous cyclotomic value at index
`p * m` whose right-hand side is `((a ^ p - b ^ p) / (a + b)) ^ m.totient`.
In particular, they isolate the small-base, exponent-three obstruction that leads to the
exceptional index six in the primitive-prime-divisor theorem. Neither primality of the exponent
nor coprimality or consecutiveness of the bases is needed for the arithmetic estimate.

The estimate follows the power comparison in M. Roitman, *On Zsigmondy primes*, Proc. Amer.
Math. Soc. 125 (1997), pp. 1913–1915, in the proof of Theorem 3; here both bases may vary.

## Main results

* `Nat.mul_add_lt_pow_sub_pow_iff`: the natural-number comparison with its exact exception.
* `TauCeti.lt_pow_sub_pow_div_add_pow`: the ordered-field quotient-power bound.
-/

public section

namespace Nat

/-- For positive bases `b < a` and `n ≥ 3`, the difference of powers exceeds `n * (a + b)`
except exactly at `(a, b, n) = (2, 1, 3)`. -/
theorem mul_add_lt_pow_sub_pow_iff {a b n : ℕ} (hb : 0 < b) (hba : b < a) (hn : 3 ≤ n) :
    n * (a + b) < a ^ n - b ^ n ↔ ¬ (a = 2 ∧ b = 1 ∧ n = 3) := by
  constructor
  · rintro h ⟨rfl, rfl, rfl⟩
    norm_num at h
  · intro hex
    have ha2 : 2 ≤ a := by omega
    have hle : n ≤ a ^ (n - 2) := by
      by_cases hn4 : 4 ≤ n
      · have h := Nat.mul_le_pow (by decide : 2 ≠ 1) (n - 2)
        have hp := Nat.pow_le_pow_left ha2 (n - 2)
        omega
      · have hn3 : n = 3 := by omega
        have ha3 : 3 ≤ a := by omega
        simp [hn3, ha3]
    exact lt_of_le_of_lt (Nat.mul_le_mul_right (a + b) hle)
      (by simpa [Nat.mul_comm] using add_mul_pow_sub_two_lt_pow_sub_pow hb hba hn)

end Nat

namespace TauCeti

/-- Outside `(a, b, n) = (2, 1, 3)`, every positive integral power of
`(a ^ n - b ^ n) / (a + b)` exceeds `n`, for positive natural bases `b < a` and `n ≥ 3`. -/
theorem lt_pow_sub_pow_div_add_pow {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {a b n k : ℕ} (hb : 0 < b) (hba : b < a)
    (hn : 3 ≤ n) (hex : ¬ (a = 2 ∧ b = 1 ∧ n = 3)) (hk : 0 < k) :
    (n : K) < (((a : K) ^ n - (b : K) ^ n) / ((a : K) + b)) ^ k := by
  have hnat := (Nat.mul_add_lt_pow_sub_pow_iff hb hba hn).mpr hex
  have hpow : b ^ n ≤ a ^ n := Nat.pow_le_pow_left hba.le n
  have hcast : (n : K) * ((a : K) + b) < (a : K) ^ n - (b : K) ^ n := by
    exact_mod_cast hnat
  have hratio : (n : K) < ((a : K) ^ n - (b : K) ^ n) / ((a : K) + b) :=
    (lt_div_iff₀ (by positivity)).mpr hcast
  have hone : (1 : K) ≤ ((a : K) ^ n - (b : K) ^ n) / ((a : K) + b) :=
    le_trans (by exact_mod_cast (show 1 ≤ n by omega)) hratio.le
  exact hratio.trans_le (le_self_pow₀ hone hk.ne')

end TauCeti
