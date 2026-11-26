/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
import TauCeti.Algebra.Order.BigOperators.ProdSubOne
import TauCeti.NumberTheory.ArithmeticFunction.Zeta

/-!
# An elementary lower bound for the totient

For `0 < n`, Euler's product formula gives `n / φ(n) = ∏_{p ∣ n} p / (p - 1)`. The `k`-th smallest
prime factor of `n` is at least `k + 1`, so this product is at most
`∏_{k=1}^{ω(n)} (k + 1) / k = ω(n) + 1`. With `2 ^ ω(n) ≤ n` (again for `0 < n`) and
`log 2 ≥ 1 / 2` this gives `n ≤ φ(n) (2 log n + 1)`. For `n = 0` both bounds read `0 ≤ 0`; the
proofs treat that case separately or avoid division.

For `m = q ^ r - 1` this lower bound for `φ(m)` gives the numerical estimate
`1 - φ(q ^ r - 1) / (r q ^ r) ≤ exp(-1 / (2r (2r log q + 1)))`, the arithmetic input for bounding
the proportion of monic polynomials of degree `r` over `𝔽_q` that are not primitive (that bound
itself is not proved here).

## Main results

* `Nat.self_le_totient_mul_cardDistinctFactors_add_one`: `n ≤ φ(n) (ω(n) + 1)`.
* `Nat.self_le_totient_mul_two_mul_log_add_one`: `n ≤ φ(n) (2 log n + 1)`.
* `TauCeti.Nat.one_sub_totient_pow_sub_one_div_le_exp`: for `q ≥ 2`,
  `1 - φ(q ^ r - 1) / (r q ^ r) ≤ exp(-1 / (2r (2r log q + 1)))`.

## References

* The inequality `m ≤ φ(m) (2 log m + 1)` and the estimate for `q ^ r - 1` are the arithmetic
  steps of `New.card_not_primitive_mul_le` in `New/Spanning/MainTerm/BadTypes.lean` of the
  folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207.
-/

public section

open ArithmeticFunction
open scoped ArithmeticFunction.omega Nat

namespace Nat

/-- **A lower bound for the totient by the number of distinct prime factors**:
`n ≤ φ(n) * (ω(n) + 1)`. For `0 < n` this is `n / φ(n) = ∏_{p ∣ n} p / (p - 1) ≤ ω(n) + 1`,
proved without division from `TauCeti.prod_le_prod_sub_one_mul_card_add_one`; for `n = 0` it reads
`0 ≤ 0`. Equality holds for `n = 2 ^ a * 3 ^ b` with `a ≥ 1`. -/
theorem self_le_totient_mul_cardDistinctFactors_add_one (n : ℕ) : n ≤ φ n * (ω n + 1) := by
  have hpos : 0 < ∏ p ∈ n.primeFactors, (p - 1) := Finset.prod_pos fun p hp =>
    Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  rw [← Nat.totient_mul_prod_primeFactors, cardDistinctFactors_eq_card_primeFactors, mul_assoc,
    mul_comm (_ + 1)]
  exact Nat.mul_le_mul_left _ (TauCeti.prod_le_prod_sub_one_mul_card_add_one fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).two_le)

/-- **An elementary lower bound for the totient**: `n ≤ φ(n) * (2 log n + 1)`. For `0 < n` it
follows from `n ≤ φ(n) * (ω(n) + 1)`, `2 ^ ω(n) ≤ n` and `log 2 ≥ 1 / 2`; for `n = 0` it reads
`0 ≤ 0`. -/
theorem self_le_totient_mul_two_mul_log_add_one (n : ℕ) :
    (n : ℝ) ≤ φ n * (2 * Real.log n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hω : (ω n : ℝ) * Real.log 2 ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) (by exact_mod_cast two_pow_cardDistinctFactors_le hn.ne')
  have hlog2 : 1 / 2 ≤ Real.log 2 := by
    linarith [Real.one_sub_inv_le_log_of_pos (x := 2) two_pos]
  have hω' : (ω n : ℝ) ≤ 2 * Real.log n := by
    linarith [mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg (α := ℝ) (ω n))]
  calc (n : ℝ) ≤ φ n * (ω n + 1) := by
        exact_mod_cast self_le_totient_mul_cardDistinctFactors_add_one n
    _ ≤ φ n * (2 * Real.log n + 1) := by gcongr

end Nat

namespace TauCeti.Nat

/-- For `q ≥ 2` and every `r`, `1 - φ(q ^ r - 1) / (r q ^ r) ≤ exp(-1 / (2r (2r log q + 1)))`.
For `r ≥ 1` this comes from `q ^ r - 1 ≤ φ(q ^ r - 1) (2r log q + 1)`, `q ^ r ≤ 2 (q ^ r - 1)`
and `1 - x ≤ exp(-x)`; for `r = 0` both sides are `1` (division by zero is zero). -/
theorem one_sub_totient_pow_sub_one_div_le_exp {q : ℕ} (hq : 2 ≤ q) (r : ℕ) :
    1 - ((q ^ r - 1).totient : ℝ) / (r * q ^ r) ≤
      Real.exp (-(1 / (2 * r * (2 * r * Real.log q + 1)))) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have hqr : 2 ≤ q ^ r := (Nat.le_self_pow hr.ne' q).trans' hq
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hqr' : (2 : ℝ) ≤ (q : ℝ) ^ r := by exact_mod_cast hqr
  have hm : ((q ^ r - 1 : ℕ) : ℝ) = (q : ℝ) ^ r - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_pow, Nat.cast_one]
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith)
  -- `log (q ^ r - 1) ≤ r log q`.
  have hlog : Real.log ((q ^ r - 1 : ℕ) : ℝ) ≤ r * Real.log q := by
    rw [hm, ← Real.log_pow]
    exact Real.log_le_log (by linarith) (by linarith)
  have hφ0 : (0 : ℝ) ≤ (q ^ r - 1).totient := Nat.cast_nonneg _
  -- `q ^ r - 1 ≤ φ(q ^ r - 1) (2r log q + 1)`.
  have hφ : (q : ℝ) ^ r - 1 ≤ (q ^ r - 1).totient * (2 * r * Real.log q + 1) := by
    rw [← hm]
    calc _ ≤ _ := (q ^ r - 1).self_le_totient_mul_two_mul_log_add_one
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hφ0
  -- `q ^ r ≤ 2 φ(q ^ r - 1) (2r log q + 1)`.
  have hmain : (q : ℝ) ^ r ≤ 2 * (q ^ r - 1).totient * (2 * r * Real.log q + 1) := by
    linarith
  have hx : 1 / (2 * r * (2 * r * Real.log q + 1)) ≤
      ((q ^ r - 1).totient : ℝ) / (r * q ^ r) := by
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [mul_le_mul_of_nonneg_left hmain hr'.le]
  linarith [Real.add_one_le_exp (-(1 / (2 * r * (2 * r * Real.log q + 1))))]

end TauCeti.Nat
