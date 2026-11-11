/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The Chu–Vandermonde identity

For `n : ℕ`, the terminating Gauss hypergeometric series at `z = 1` is

`₂F₁(−n, b; c; 1) = (c − b)ₙ / (c)ₙ`  (DLMF 15.4.24),

whenever `(c)ₙ ≠ 0`. This is the case `a = −n` of Gauss's summation theorem; here it is proved
directly, from the Pochhammer form `∑ₖ (−1)ᵏ C(n, k) (b)ₖ (c + k)ₙ₋ₖ = (c − b)ₙ`.

## Main results

* `TauCeti.ordinaryHypergeometric_neg_nat_eq_sum`: `₂F₁(−n, b; c; z)` is the finite sum of its
  first `n + 1` terms;
* `TauCeti.sum_neg_one_pow_mul_choose_ascPochhammer`: the Pochhammer form of Chu–Vandermonde;
* `TauCeti.ordinaryHypergeometric_neg_nat_one`: DLMF 15.4.24.

## Implementation notes

The hypothesis is `(c)ₙ ≠ 0`, which allows `c = −m` with `m ≥ n`; then `(c)ₖ ≠ 0` for `k ≤ n`
and the series stops before Mathlib's junk inverse `0⁻¹` is reached.

## References

* NIST Digital Library of Mathematical Functions, 15.4.24, <https://dlmf.nist.gov/15.4.E24>.
-/

public section

noncomputable section

open Finset Polynomial
open scoped Nat

namespace TauCeti

/-- `(x)ₖ₊₁ = x (x + 1)ₖ`. -/
private theorem ascPochhammer_succ_eval_left (k : ℕ) (x : ℂ) :
    (ascPochhammer ℂ (k + 1)).eval x = x * (ascPochhammer ℂ k).eval (x + 1) := by
  rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add, eval_X, eval_one]

/-- `(x)ₖ₊ₘ = (x)ₖ (x + k)ₘ`. -/
private theorem ascPochhammer_eval_add (x : ℂ) (k m : ℕ) :
    (ascPochhammer ℂ (k + m)).eval x =
      (ascPochhammer ℂ k).eval x * (ascPochhammer ℂ m).eval (x + k) := by
  rw [← ascPochhammer_mul, eval_mul, eval_comp, eval_add, eval_X, eval_natCast]

/-- `(−n)ₖ = (−1)ᵏ k! C(n, k)`. -/
private theorem ascPochhammer_eval_neg_natCast (n k : ℕ) :
    (ascPochhammer ℂ k).eval (-(n : ℂ)) = (-1) ^ k * k ! * n.choose k := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  ring

/-- **The Pochhammer form of Chu–Vandermonde**:
`∑ₖ (−1)ᵏ C(n, k) (b)ₖ (c + k)ₙ₋ₖ = (c − b)ₙ`. -/
theorem sum_neg_one_pow_mul_choose_ascPochhammer (n : ℕ) (b c : ℂ) :
    ∑ k ∈ range (n + 1), (-1 : ℂ) ^ k * n.choose k * (ascPochhammer ℂ k).eval b *
      (ascPochhammer ℂ (n - k)).eval (c + k) = (ascPochhammer ℂ n).eval (c - b) := by
  induction n generalizing b c with
  | zero => simp
  | succ n ih =>
    set f : ℕ → ℂ := fun k =>
      (-1 : ℂ) ^ k * (ascPochhammer ℂ k).eval b * (ascPochhammer ℂ (n + 1 - k)).eval (c + k)
    have hgoal : ∀ k ∈ range (n + 2),
        (-1 : ℂ) ^ k * (n + 1).choose k * (ascPochhammer ℂ k).eval b *
          (ascPochhammer ℂ (n + 1 - k)).eval (c + k) = (n + 1).choose k * f k := by
      intro k _
      simp only [f]
      ring
    -- Pascal's rule splits the sum.
    have hsplit : ∑ k ∈ range (n + 2), ((n + 1).choose k : ℂ) * f k =
        ∑ k ∈ range (n + 1), (n.choose k : ℂ) * f k +
          ∑ k ∈ range (n + 1), (n.choose k : ℂ) * f (k + 1) := by
      have h1 := sum_range_succ (fun x => (n.choose (x + 1) : ℂ) * f (x + 1)) n
      have h2 := sum_range_succ' (fun x => (n.choose x : ℂ) * f x) n
      rw [Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero] at h1
      rw [Nat.choose_zero_right, Nat.cast_one, one_mul] at h2
      rw [sum_range_succ']
      simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, sum_add_distrib,
        Nat.choose_zero_right, Nat.cast_one, one_mul]
      linear_combination h1 - h2
    -- The first part: `(c + n) (c − b)ₙ`.
    have hfirst : ∑ k ∈ range (n + 1), (n.choose k : ℂ) * f k =
        (c + n) * (ascPochhammer ℂ n).eval (c - b) := by
      rw [← ih b c, mul_sum]
      refine sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
      simp only [f]
      rw [show n + 1 - k = n - k + 1 by omega, ascPochhammer_succ_eval,
        show c + k + ((n - k : ℕ) : ℂ) = c + n by rw [Nat.cast_sub hk']; ring]
      ring
    -- The second part: `−b (c − b)ₙ`, by the induction hypothesis at `b + 1`, `c + 1`.
    have hsecond : ∑ k ∈ range (n + 1), (n.choose k : ℂ) * f (k + 1) =
        -b * (ascPochhammer ℂ n).eval (c - b) := by
      rw [show c - b = c + 1 - (b + 1) by ring, ← ih (b + 1) (c + 1), mul_sum]
      refine sum_congr rfl fun k _ => ?_
      simp only [f]
      rw [show n + 1 - (k + 1) = n - k by omega, ascPochhammer_succ_eval_left, pow_succ]
      push_cast
      rw [show c + (k + 1) = c + 1 + k by ring]
      ring
    rw [sum_congr rfl hgoal, hsplit, hfirst, hsecond, ascPochhammer_succ_eval]
    ring

/-- A terminating `₂F₁(−n, b; c; z)` is the sum of its first `n + 1` terms. -/
theorem ordinaryHypergeometric_neg_nat_eq_sum (n : ℕ) (b c z : ℂ) :
    ordinaryHypergeometric (-n : ℂ) b c z =
      ∑ k ∈ range (n + 1), ((k ! : ℂ)⁻¹ * (ascPochhammer ℂ k).eval (-n : ℂ) *
        (ascPochhammer ℂ k).eval b * ((ascPochhammer ℂ k).eval c)⁻¹) * z ^ k := by
  rw [ordinaryHypergeometric_eq_tsum]
  simp only [smul_eq_mul]
  refine tsum_eq_sum fun k hk => ?_
  rw [ascPochhammer_eval_neg_natCast_of_lt (by simpa using hk)]
  simp

/-- **Chu–Vandermonde** (DLMF 15.4.24): `₂F₁(−n, b; c; 1) = (c − b)ₙ / (c)ₙ` when `(c)ₙ ≠ 0`. -/
theorem ordinaryHypergeometric_neg_nat_one (n : ℕ) (b : ℂ) {c : ℂ}
    (hc : (ascPochhammer ℂ n).eval c ≠ 0) :
    ordinaryHypergeometric (-n : ℂ) b c (1 : ℂ) =
      (ascPochhammer ℂ n).eval (c - b) / (ascPochhammer ℂ n).eval c := by
  rw [ordinaryHypergeometric_neg_nat_eq_sum, eq_div_iff hc, sum_mul,
    ← sum_neg_one_pow_mul_choose_ascPochhammer]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hadd := ascPochhammer_eval_add c k (n - k)
  rw [Nat.add_sub_of_le hk'] at hadd
  have hck : (ascPochhammer ℂ k).eval c ≠ 0 := by
    intro h
    rw [hadd, h, zero_mul] at hc
    exact hc rfl
  have hkf : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [hadd, ascPochhammer_eval_neg_natCast, one_pow, mul_one]
  field_simp

end TauCeti
