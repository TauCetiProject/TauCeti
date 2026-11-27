/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-!
# Archimedean size of the theta-jet loss factor

A theta-jet coefficient can lose divisibility at the primes. One can pay for the losses by
multiplying by the squares of short products of consecutive integers, one per infinite place.
We bound the archimedean cost of these products together with the level and vacuum factors.
The level and consecutive-integer factors are rational, so all field conjugates have the same
size for these factors, even though the field automorphism need not preserve the complex norm.

The normalization is that of `New.Data.norm_map_mul_intVacuum_le` in lsernau/grh-lean
(`72fead1`, `grh/src/New/Derivatives/Sharpness/BoundAttained.lean`).
-/

public section

namespace TauCeti.OneSidedBound

open Real

private theorem prod_sq_ascFactorial_le {ι : Type*} (s : Finset ι) (l : ι → ℕ)
    {b k : ℕ} (hb : 2 ≤ b) (hkb : k ≤ b) (hl : ∀ i ∈ s, l i ≤ 2 * b) :
    let n := ⌈6 * (b : ℝ) / k⌉₊
    ∏ i ∈ s, (((l i - n + 1).ascFactorial n : ℝ) ^ 2) ≤
      exp (56 * s.card * ((b : ℝ) / k) * log b) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  intro n
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hratio : 1 ≤ (b : ℝ) / k := (one_le_div (by positivity)).2 (by exact_mod_cast hkb)
  have hn : (n : ℝ) ≤ 7 * (b : ℝ) / k := calc
    _ ≤ 6 * (b : ℝ) / k + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    _ ≤ 7 * (b : ℝ) / k := by rw [mul_div_assoc, mul_div_assoc]; linarith
  have hn' : n ≤ 7 * b := by exact_mod_cast hn.trans (div_le_self (by positivity) hk')
  have hpow : 7 * b ≤ b ^ 4 := by
    have h8 := Nat.pow_le_pow_left hb 3
    rw [pow_succ]
    exact Nat.mul_le_mul_right b (by omega)
  have hbound (i : ι) (hi : i ∈ s) :
      (l i - n + 1).ascFactorial n ≤ (b ^ 4) ^ n := by
    refine (Nat.ascFactorial_le_pow_add _ _).trans (Nat.pow_le_pow_left ?_ _)
    rw [tsub_add_eq_max]
    exact max_le ((hl i hi).trans (by omega : 2 * b ≤ 7 * b)) hn' |>.trans hpow
  have hb' : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  calc
    _ ≤ ∏ _i ∈ s, (((b : ℝ) ^ 4) ^ n) ^ 2 := by
      gcongr with i hi
      exact_mod_cast hbound i hi
    _ = exp (8 * s.card * n * log b) := by
      rw [Finset.prod_const, ← pow_mul, ← pow_mul, ← pow_mul]
      rw [← exp_log hb', ← exp_natCast_mul, log_exp]
      push_cast
      congr 1
      ring
    _ ≤ _ := by
      apply exp_le_exp.mpr
      calc
        _ ≤ 8 * s.card * (7 * (b : ℝ) / k) * log b := by gcongr
        _ = _ := by ring

/-- The squared consecutive-integer loss products, the level contribution `M^(12·#s)`, and a
vacuum value with conjugate norm bounded by `exp(12 C q²)` have combined conjugate norm at most
`exp(#s · m · b/k)`. The product at a place starts at `(l i - n)₊ + 1` and has `n = ⌈6b/k⌉`
factors, so the estimate covers both `l i < n` and `n ≤ l i`. -/
private theorem norm_map_mul_intVacuum_le_of_budget {ι : Type*} (s : Finset ι) (l : ι → ℕ)
    {b k m M q : ℕ} {C : ℝ} {v : ℂ} (σ : ℂ ≃+* ℂ) (hs : s.Nonempty)
    (hb : 2 ≤ b) (hk : 0 < k) (hkb : k ≤ b) (hm : 332 * log (b : ℝ) ≤ m)
    (hM : M ≤ b ^ 22) (hC : C ≤ log b) (hq : k * q ^ 2 ≤ b) (hl : ∀ i ∈ s, l i ≤ 2 * b)
    (hv : ‖σ v‖ ≤ exp (12 * C * (q : ℝ) ^ 2)) :
    let n := ⌈6 * (b : ℝ) / k⌉₊
    ‖σ ((M : ℂ) ^ (12 * s.card) * ((∏ i ∈ s, ((l i - n + 1).ascFactorial n) ^ 2 : ℕ) : ℂ) * v)‖ ≤
      exp (s.card * m * ((b : ℝ) / k)) := by
  intro n
  have hb' : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hratio : (1 : ℝ) ≤ (b : ℝ) / k := (one_le_div hk').2 (by exact_mod_cast hkb)
  have hq' : (q : ℝ) ^ 2 ≤ (b : ℝ) / k := by
    rw [le_div_iff₀ hk', mul_comm]
    exact_mod_cast hq
  have hlevel : (M : ℝ) ^ (12 * s.card) ≤ exp (264 * s.card * log b) := calc
    _ ≤ ((b : ℝ) ^ 22) ^ (12 * s.card) := by gcongr; exact_mod_cast hM
    _ = _ := by
      rw [← pow_mul, ← exp_log hb', ← exp_natCast_mul, log_exp]
      push_cast
      congr 1
      ring
  have hprod := prod_sq_ascFactorial_le s l hb hkb hl
  simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast]
  push_cast
  calc
    _ ≤ exp (264 * s.card * log b) * exp (56 * s.card * ((b : ℝ) / k) * log b) *
        exp (12 * C * (q : ℝ) ^ 2) := by gcongr
    _ ≤ _ := by
      rw [← exp_add, ← exp_add]
      apply exp_le_exp.mpr
      have hs' : (1 : ℝ) ≤ s.card := by exact_mod_cast hs.card_pos
      have h₁ : 264 * (s.card : ℝ) * log b ≤ 264 * s.card * ((b : ℝ) / k) * log b := calc
        _ = 264 * s.card * 1 * log b := by rw [mul_one]
        _ ≤ _ := by gcongr
      have h₂ : 12 * C * (q : ℝ) ^ 2 ≤ 12 * s.card * ((b : ℝ) / k) * log b := calc
        _ ≤ 12 * log b * (q : ℝ) ^ 2 := by gcongr
        _ ≤ 12 * log b * ((b : ℝ) / k) := by gcongr
        _ ≤ _ := by
          calc
            _ = 12 * 1 * ((b : ℝ) / k) * log b := by ring
            _ ≤ _ := by gcongr
      linarith [mul_le_mul_of_nonneg_right hm
        (mul_nonneg (Nat.cast_nonneg s.card) (div_nonneg hb'.le hk'.le))]

/-- At the separated prime-sum scales, the level factor, squared loss products and vacuum value
fit into the conjugate bound `exp(#s · m · b/k)`. Here `s` is the set of infinite places,
`q` is the cyclotomic order and `l` the family of jet degrees. -/
theorem norm_map_mul_intVacuum_le {ι : Type*} (s : Finset ι) (l : ι → ℕ)
    {x b k m M q : ℕ} {C : ℝ} {v : ℂ} (σ : ℂ ≃+* ℂ) (hs : s.Nonempty)
    (hb : 2 ≤ log (b : ℝ)) (hx : log (b : ℝ) ^ 100 ≤ x) (hm : x ≤ m ^ 2)
    (hk : 0 < k) (hkx : k ≤ 3 * x ^ 5) (hq : q ≤ x ^ 12) (hxb : x ^ 30 ≤ b)
    (hM : M ≤ b ^ 22) (hC : C ≤ log b) (hl : ∀ i ∈ s, l i ≤ 2 * b)
    (hv : ‖σ v‖ ≤ exp (12 * C * (q : ℝ) ^ 2)) :
    let n := ⌈6 * (b : ℝ) / k⌉₊
    ‖σ ((M : ℂ) ^ (12 * s.card) * ((∏ i ∈ s, ((l i - n + 1).ascFactorial n) ^ 2 : ℕ) : ℂ) * v)‖ ≤
      exp (s.card * m * ((b : ℝ) / k)) := by
  have hx3 : 3 ≤ x := by
    have h : (2 : ℝ) ^ 100 ≤ (x : ℝ) := (pow_le_pow_left₀ (by norm_num) hb _).trans hx
    exact_mod_cast (by norm_num : (3 : ℝ) ≤ 2 ^ 100).trans h
  have hxb' : 3 * x ^ 29 ≤ b := calc
    _ ≤ x ^ 30 := (Nat.mul_le_mul_right (x ^ 29) hx3).trans_eq (pow_succ' x 29).symm
    _ ≤ _ := hxb
  have hk' : k ≤ b := by
    refine hkx.trans ?_
    calc
      _ ≤ 3 * x ^ 29 := by gcongr; omega
      _ ≤ _ := hxb'
  have hq' : k * q ^ 2 ≤ b := calc
    _ ≤ (3 * x ^ 5) * (x ^ 12) ^ 2 := by gcongr
    _ = 3 * x ^ 29 := by ring
    _ ≤ _ := hxb'
  have hb' : 2 ≤ b := (by omega : 2 ≤ x).trans
    ((Nat.le_self_pow (by decide : 30 ≠ 0) x).trans hxb)
  have hm' : log (b : ℝ) ^ 50 ≤ m := by
    apply (pow_le_pow_iff_left₀ (by positivity) (Nat.cast_nonneg m) (by norm_num : 2 ≠ 0)).mp
    rw [← pow_mul]
    exact hx.trans (by exact_mod_cast hm)
  have hm'' : 332 * log (b : ℝ) ≤ m := by
    refine le_trans ?_ hm'
    rw [pow_succ]
    gcongr
    exact (by norm_num : (332 : ℝ) ≤ 2 ^ 49).trans (pow_le_pow_left₀ (by norm_num) hb _)
  exact norm_map_mul_intVacuum_le_of_budget s l σ hs hb' hk hk' hm'' hM hC hq' hl hv

end TauCeti.OneSidedBound
