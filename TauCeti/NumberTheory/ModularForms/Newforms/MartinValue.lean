/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Prime

/-!
# Martin's arithmetic expression for the weight-two newspace dimension

G. Martin gave an explicit formula for the dimension `g⁺(N)` of the space of weight-two newforms
on `Γ₀(N)` with trivial character. It is built from five multiplicative functions of `N`, each
determined by an explicit value at every prime power `p ^ e`:

* `s(p ^ e)`: `1 - 1/p` for `e = 1`, `1 - 1/p - 1/p²` for `e = 2`, and `(1 - 1/p)(1 - 1/p²)` for
  `e ≥ 3`;
* `v∞(p ^ e)`: `0` for odd `e`, `p - 2` for `e = 2`, and `p ^ (e/2 - 2) (p - 1)²` for even `e ≥ 4`;
* `v₂(p ^ e)`: for `e = 1, 2, 3` the values `-1, -1, 1` at `p = 2`, `0, -1, 0` at `p ≡ 1 mod 4`
  and `-2, 1, 0` at `p ≡ 3 mod 4`, and `0` for `e ≥ 4`;
* `v₃(p ^ e)`: for `e = 1, 2, 3` the values `-1, -1, 1` at `p = 3`, `0, -1, 0` at `p ≡ 1 mod 3`
  and `-2, 1, 0` at `p ≡ 2 mod 3`, and `0` for `e ≥ 4`;
* the Möbius factor: `-1` for `e = 1` and `0` for `e ≥ 2`.

With `(S, I, A, B, M)` the products of these local factors over the prime factorization of
`N > 0`, Martin's Theorem 1 at weight two reads

```text
g⁺(N) = N S / 12 - I / 2 - A / 4 - B / 3 + M.
```

This file defines the local table `TauCeti.martinLocalTerms p e : Fin 5 → ℚ`, its coordinatewise
product `TauCeti.martinTerms N` over the factorization of `N`, and the right-hand side
`TauCeti.martinValue N`. It is purely arithmetic: no space of modular forms enters, and the
identification of `martinValue N` with the actual newspace dimension is a separate comparison
theorem. The Möbius coordinate of `martinTerms N` is the Möbius function `μ N`, and at a prime
`p ≡ 11 mod 12` the expression attains Martin's bound: `12 · martinValue p = p + 1`.

## Main definitions

* `TauCeti.martinLocalTerms p e`: the five local factors `(s, v∞, v₂, v₃, μ)` at `p ^ e`; it is
  `1` at `e = 0` and `0` for a nonprime `p` and `e > 0`.
* `TauCeti.martinTerms N`: the coordinatewise product of the local factors over the
  factorization of `N`.
* `TauCeti.martinValue N`: `N S / 12 - I / 2 - A / 4 - B / 3 + M` for `N > 0`, and `0` at `N = 0`
  as a total-function convention.

## Main results

* `TauCeti.martinLocalTerms_of_prime`: the prime-power table.
* `TauCeti.martinTerms_mul`, `TauCeti.martinTerms_prime_pow`: `martinTerms` is multiplicative on
  coprime arguments and equals the local table at a prime power.
* `TauCeti.martinTerms_apply_four`: the Möbius coordinate is `μ N`.
* `TauCeti.martinValue_prime`, `TauCeti.twelve_mul_martinValue_prime_of_mod_twelve_eq_eleven`: the
  expression at a prime level, and its value `(p + 1) / 12` at primes `p ≡ 11 mod 12`.
* `TauCeti.martinValue_eleven`, `TauCeti.martinValue_thirty`, `TauCeti.martinValue_thirtyFive`:
  the values `1`, `1` and `3` at levels `11`, `30` and `35`.

## References

* G. Martin, *Dimensions of the spaces of cuspforms and newforms on `Γ₀(N)` and `Γ₁(N)`*,
  J. Number Theory 112 (2005), 298–331, Definitions 1A–1D and Theorem 1.
-/

public section

open Finset

open scoped ArithmeticFunction.Moebius

namespace TauCeti

/-! ### The local table -/

/-- Martin's five local factors `(s, v∞, v₂, v₃, μ)` at the prime power `p ^ e`, as a vector in
`ℚ⁵` (Martin, Definitions 1A–1D and the Möbius term of Theorem 1). At exponent `0` it is the
all-ones vector, and for a nonprime `p` and `e > 0` it is the zero vector. -/
def martinLocalTerms (p e : ℕ) : Fin 5 → ℚ :=
  if e = 0 then 1 else if ¬ p.Prime then 0 else
    ![if e = 1 then 1 - 1 / (p : ℚ) else if e = 2 then 1 - 1 / (p : ℚ) - 1 / (p : ℚ) ^ 2 else
        (1 - 1 / (p : ℚ)) * (1 - 1 / (p : ℚ) ^ 2),
      if e % 2 = 1 then 0 else if e = 2 then (p : ℚ) - 2 else
        (p : ℚ) ^ (e / 2 - 2) * ((p : ℚ) - 1) ^ 2,
      if p = 2 then (if e = 1 ∨ e = 2 then -1 else if e = 3 then 1 else 0)
        else if p % 4 = 1 then (if e = 2 then -1 else 0)
        else (if e = 1 then -2 else if e = 2 then 1 else 0),
      if p = 3 then (if e = 1 ∨ e = 2 then -1 else if e = 3 then 1 else 0)
        else if p % 3 = 1 then (if e = 2 then -1 else 0)
        else (if e = 1 then -2 else if e = 2 then 1 else 0),
      if e = 1 then -1 else 0]

/-- At exponent zero the local table is the all-ones vector, for every `p` including nonprime
ones such as `p = 0`. -/
@[simp]
theorem martinLocalTerms_zero_right (p : ℕ) : martinLocalTerms p 0 = 1 := by
  simp [martinLocalTerms]

theorem martinLocalTerms_of_not_prime {p e : ℕ} (hp : ¬ p.Prime) (he : e ≠ 0) :
    martinLocalTerms p e = 0 := by
  simp [martinLocalTerms, hp, he]

/-- The prime-power table of Martin's local factors. -/
theorem martinLocalTerms_of_prime {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    martinLocalTerms p e =
      ![if e = 1 then 1 - 1 / (p : ℚ) else if e = 2 then 1 - 1 / (p : ℚ) - 1 / (p : ℚ) ^ 2 else
          (1 - 1 / (p : ℚ)) * (1 - 1 / (p : ℚ) ^ 2),
        if e % 2 = 1 then 0 else if e = 2 then (p : ℚ) - 2 else
          (p : ℚ) ^ (e / 2 - 2) * ((p : ℚ) - 1) ^ 2,
        if p = 2 then (if e = 1 ∨ e = 2 then -1 else if e = 3 then 1 else 0)
          else if p % 4 = 1 then (if e = 2 then -1 else 0)
          else (if e = 1 then -2 else if e = 2 then 1 else 0),
        if p = 3 then (if e = 1 ∨ e = 2 then -1 else if e = 3 then 1 else 0)
          else if p % 3 = 1 then (if e = 2 then -1 else 0)
          else (if e = 1 then -2 else if e = 2 then 1 else 0),
        if e = 1 then -1 else 0] := by
  simp [martinLocalTerms, hp, he]

/-- At a prime `p`, the Möbius coordinate of the local table is the Möbius function of `p ^ e`. -/
theorem martinLocalTerms_apply_four {p : ℕ} (hp : p.Prime) (e : ℕ) :
    martinLocalTerms p e 4 = μ (p ^ e) := by
  rcases eq_or_ne e 0 with rfl | he
  · simp
  · rw [martinLocalTerms_of_prime hp he, ArithmeticFunction.moebius_apply_prime_pow hp he]
    split_ifs <;> simp

/-- At a prime `p` the local table at exponent one is `(1 - 1/p, 0, v₂(p), v₃(p), -1)`, where
`v₂(p)` is `-1`, `0` or `-2` according as `p = 2`, `p ≡ 1 mod 4` or `p ≡ 3 mod 4`, and `v₃(p)` is
`-1`, `0` or `-2` according as `p = 3`, `p ≡ 1 mod 3` or `p ≡ 2 mod 3`. -/
theorem martinLocalTerms_prime_one {p : ℕ} (hp : p.Prime) :
    martinLocalTerms p 1 =
      ![1 - 1 / (p : ℚ), 0, if p = 2 then -1 else if p % 4 = 1 then 0 else -2,
        if p = 3 then -1 else if p % 3 = 1 then 0 else -2, -1] := by
  ext i
  fin_cases i <;> simp [martinLocalTerms_of_prime hp one_ne_zero]

/-- The local table at `2 ^ 2`; the order-two correction `-1` at `p = 2` differs from the value
`1` at a prime `p ≡ 3 mod 4`. -/
theorem martinLocalTerms_two_two : martinLocalTerms 2 2 = ![1 / 4, 0, -1, 1, 0] := by
  ext i
  fin_cases i <;> norm_num [martinLocalTerms_of_prime Nat.prime_two two_ne_zero]

/-- The local table at `3 ^ 2`; the order-three correction `-1` at `p = 3` differs from the value
`1` at a prime `p ≡ 2 mod 3`. -/
theorem martinLocalTerms_three_two : martinLocalTerms 3 2 = ![5 / 9, 1, 1, -1, 0] := by
  ext i
  fin_cases i <;> norm_num [martinLocalTerms_of_prime Nat.prime_three two_ne_zero]

/-- The local table at `2 ^ 3`: the cusp term vanishes at odd exponent while the order-two
correction is positive. -/
theorem martinLocalTerms_two_three : martinLocalTerms 2 3 = ![3 / 8, 0, 1, 0, 0] := by
  ext i
  fin_cases i <;> norm_num [martinLocalTerms_of_prime Nat.prime_two three_ne_zero]

/-! ### The product over the factorization -/

/-- The coordinatewise product `(S, I, A, B, M)` of Martin's local factors over the prime
factorization of `N`. -/
def martinTerms (N : ℕ) : Fin 5 → ℚ :=
  N.factorization.prod martinLocalTerms

/-- Each coordinate of `martinTerms N` is the product of the local factors over the prime
factors of `N`. -/
theorem martinTerms_apply (N : ℕ) (j : Fin 5) :
    martinTerms N j = ∏ p ∈ N.primeFactors, martinLocalTerms p (N.factorization p) j := by
  simp [martinTerms, Finsupp.prod, Finset.prod_apply]

@[simp]
theorem martinTerms_zero : martinTerms 0 = 1 := by
  simp [martinTerms]

@[simp]
theorem martinTerms_one : martinTerms 1 = 1 := by
  simp [martinTerms]

/-- `martinTerms` is multiplicative on coprime arguments. -/
theorem martinTerms_mul {m n : ℕ} (h : m.Coprime n) :
    martinTerms (m * n) = martinTerms m * martinTerms n := by
  simp only [martinTerms]
  rw [Nat.factorization_mul_of_coprime h,
    Finsupp.prod_add_index_of_disjoint h.disjoint_primeFactors]

/-- At a prime power, `martinTerms` is the local table. -/
theorem martinTerms_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) :
    martinTerms (p ^ e) = martinLocalTerms p e := by
  rw [martinTerms, hp.factorization_pow, Finsupp.prod_single_index (martinLocalTerms_zero_right p)]

theorem martinTerms_prime {p : ℕ} (hp : p.Prime) : martinTerms p = martinLocalTerms p 1 := by
  simpa using martinTerms_prime_pow hp 1

/-- The Möbius coordinate of `martinTerms N` is the Möbius function, for `N ≠ 0`. -/
theorem martinTerms_apply_four {N : ℕ} (hN : N ≠ 0) : martinTerms N 4 = μ N := by
  rw [ArithmeticFunction.isMultiplicative_moebius.multiplicative_factorization _ hN,
    martinTerms_apply, Finsupp.prod, Int.cast_prod]
  exact prod_congr rfl fun p hp ↦ by
    rw [martinLocalTerms_apply_four (Nat.prime_of_mem_primeFactors hp)]

/-! ### Martin's expression -/

/-- Martin's arithmetic expression `N S / 12 - I / 2 - A / 4 - B / 3 + M` for the dimension of
the weight-two newspace on `Γ₀(N)` with trivial character, where `(S, I, A, B, M)` is
`martinTerms N` (Martin, Theorem 1 at weight two). The value `0` at `N = 0` is a total-function
convention. -/
def martinValue (N : ℕ) : ℚ :=
  if N = 0 then 0 else
    N * martinTerms N 0 / 12 - martinTerms N 1 / 2 - martinTerms N 2 / 4 - martinTerms N 3 / 3 +
      martinTerms N 4

@[simp]
theorem martinValue_zero : martinValue 0 = 0 := by
  simp [martinValue]

theorem martinValue_of_ne_zero {N : ℕ} (hN : N ≠ 0) :
    martinValue N = N * martinTerms N 0 / 12 - martinTerms N 1 / 2 - martinTerms N 2 / 4 -
      martinTerms N 3 / 3 + martinTerms N 4 := by
  simp [martinValue, hN]

/-- At level one all five products are empty, giving `1/12 - 1/2 - 1/4 - 1/3 + 1 = 0`. -/
@[simp]
theorem martinValue_one : martinValue 1 = 0 := by
  rw [martinValue_of_ne_zero one_ne_zero, martinTerms_one]
  norm_num

/-- Martin's expression at a prime level `p`: `(p - 1) / 12 - v₂(p) / 4 - v₃(p) / 3 - 1`. -/
theorem martinValue_prime {p : ℕ} (hp : p.Prime) :
    martinValue p =
      ((p : ℚ) - 1) / 12 - martinLocalTerms p 1 2 / 4 - martinLocalTerms p 1 3 / 3 - 1 := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h0 : martinLocalTerms p 1 0 = 1 - 1 / (p : ℚ) := by simp [martinLocalTerms_prime_one hp]
  have h1 : martinLocalTerms p 1 1 = 0 := by simp [martinLocalTerms_prime_one hp]
  have h4 : martinLocalTerms p 1 4 = -1 := by simp [martinLocalTerms_prime_one hp]
  rw [martinValue_of_ne_zero hp.ne_zero, martinTerms_prime hp, h0, h1, h4]
  field_simp
  ring

/-- At a prime `p ≡ 11 mod 12` Martin's expression equals `(p + 1) / 12`, the case of equality in
Martin's bound `12 g⁺(N) ≤ N + 1`. -/
theorem twelve_mul_martinValue_prime_of_mod_twelve_eq_eleven {p : ℕ} (hp : p.Prime)
    (h : p % 12 = 11) : 12 * martinValue p = p + 1 := by
  have h2 : p ≠ 2 := by omega
  have h3 : p ≠ 3 := by omega
  have h4 : p % 4 ≠ 1 := by omega
  have h3' : p % 3 ≠ 1 := by omega
  rw [martinValue_prime hp, martinLocalTerms_prime_one hp]
  simp only [Matrix.cons_val, h2, h3, h4, h3', ↓reduceIte]
  ring

/-- Martin's expression takes the value `1` at level `11`. -/
theorem martinValue_eleven : martinValue 11 = 1 := by
  have h := twelve_mul_martinValue_prime_of_mod_twelve_eq_eleven (p := 11) (by norm_num) rfl
  push_cast at h
  linarith

/-- Martin's expression takes the value `3` at level `35`, so that `12 · 3 = 35 + 1`. -/
theorem martinValue_thirtyFive : martinValue 35 = 3 := by
  have h : martinTerms 35 = martinLocalTerms 5 1 * martinLocalTerms 7 1 := by
    rw [show 35 = 5 * 7 by rfl, martinTerms_mul (by norm_num),
      martinTerms_prime (by norm_num), martinTerms_prime (by norm_num)]
  rw [martinValue_of_ne_zero (by norm_num), h]
  norm_num [martinLocalTerms_of_prime (p := 5) (by norm_num) one_ne_zero,
    martinLocalTerms_of_prime (p := 7) (by norm_num) one_ne_zero]

/-- Martin's expression takes the value `1` at level `30`, which has three distinct prime
factors. -/
theorem martinValue_thirty : martinValue 30 = 1 := by
  have h : martinTerms 30 =
      martinLocalTerms 2 1 * martinLocalTerms 3 1 * martinLocalTerms 5 1 := by
    rw [show 30 = 2 * 3 * 5 by rfl, martinTerms_mul (by norm_num), martinTerms_mul (by norm_num),
      martinTerms_prime Nat.prime_two, martinTerms_prime Nat.prime_three,
      martinTerms_prime (by norm_num)]
  rw [martinValue_of_ne_zero (by norm_num), h]
  norm_num [martinLocalTerms_of_prime Nat.prime_two one_ne_zero,
    martinLocalTerms_of_prime Nat.prime_three one_ne_zero,
    martinLocalTerms_of_prime (p := 5) (by norm_num) one_ne_zero]

end TauCeti
