/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Group.Indicator

/-!
# Summability of multiplicative functions supported on squarefree integers

Let `g : ℕ → ℝ` be nonnegative and multiplicative on coprime arguments, with `g 1 = 1` and
`g (p ^ k) = 0` for every prime `p` and `k ≥ 2`. Then every partial sum of `g` over the
`M`-smooth numbers is the finite Euler product `∏_{p < M} (1 + g p) ≤ exp (∑_{p < M} g p)`, so
`g` is summable as soon as its values at the primes are.

This is the convergence criterion behind singular series such as
`∑_q μ(q) c_q(N) / φ(q)³`, whose terms are bounded by such a function.

## Main results

* `TauCeti.summable_of_summable_primes_of_squarefree`: `g` is summable if `g` restricted to the
  primes is.
-/

public section

open Finset

namespace TauCeti

/-- A nonnegative function on `ℕ`, multiplicative on coprime arguments, with `g 1 = 1` and
vanishing at the prime powers `p ^ k` with `k ≥ 2`, is summable as soon as its values at the
primes are summable. -/
theorem summable_of_summable_primes_of_squarefree {g : ℕ → ℝ} (hg₀ : ∀ n, 0 ≤ g n)
    (hg₁ : g 1 = 1) (hmul : ∀ {m n}, m.Coprime n → g (m * n) = g m * g n)
    (hpow : ∀ {p k : ℕ}, p.Prime → 2 ≤ k → g (p ^ k) = 0)
    (hprime : Summable fun p : Nat.Primes ↦ g p) : Summable g := by
  -- Each local factor `∑' e, g (p ^ e)` is `1 + g p`.
  have hloc : ∀ {p : ℕ}, p.Prime → ∑' e, g (p ^ e) = 1 + g p := fun {p} hp ↦ by
    rw [tsum_eq_sum (s := range 2) fun e he ↦ hpow hp (by simp at he; omega)]
    simp [sum_range_succ, hg₁]
  have hsum : ∀ {p : ℕ}, p.Prime → Summable fun e : ℕ ↦ ‖g (p ^ e)‖ := fun {p} hp ↦
    summable_of_ne_finset_zero (s := range 2) fun e he ↦ by
      rw [hpow hp (by simp at he; omega), norm_zero]
  have hind : Summable ({p : ℕ | p.Prime}.indicator g) :=
    (summable_subtype_iff_indicator (s := {p : ℕ | p.Prime})).1 hprime
  refine summable_of_sum_le hg₀ (c := g 0 + Real.exp (∑' n, {p : ℕ | p.Prime}.indicator g n))
    fun u ↦ ?_
  set M := u.sup id + 1
  -- The finite Euler product over the primes below `M` dominates the sum over `u \ {0}`.
  have hsmooth : HasSum (M.smoothNumbers.indicator g) (∏ p ∈ M.primesBelow, ∑' e, g (p ^ e)) :=
    hasSum_subtype_iff_indicator.1
      (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hg₁ hmul hsum M).2
  have h₁ : ∑ n ∈ u.erase 0, g n ≤ ∏ p ∈ M.primesBelow, ∑' e, g (p ^ e) := by
    refine (sum_congr rfl fun n hn ↦ ?_).trans_le
      (sum_le_hasSum _ (fun n _ ↦ Set.indicator_nonneg (fun n _ ↦ hg₀ n) n) hsmooth)
    have hn0 := Nat.pos_of_ne_zero (ne_of_mem_erase hn)
    have hnM : n < M := Nat.lt_succ_of_le (le_sup (f := id) (mem_of_mem_erase hn))
    rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt hn0 hnM)]
  have h₂ : ∏ p ∈ M.primesBelow, ∑' e, g (p ^ e) ≤
      Real.exp (∑' n, {p : ℕ | p.Prime}.indicator g n) := by
    calc ∏ p ∈ M.primesBelow, ∑' e, g (p ^ e)
        = ∏ p ∈ M.primesBelow, (1 + g p) :=
          prod_congr rfl fun p hp ↦ hloc (Nat.prime_of_mem_primesBelow hp)
      _ ≤ ∏ p ∈ M.primesBelow, Real.exp (g p) :=
          prod_le_prod₀ (fun p _ ↦ by linarith [hg₀ p]) fun p _ ↦ by
            linarith [Real.add_one_le_exp (g p)]
      _ = Real.exp (∑ n ∈ range M, {p : ℕ | p.Prime}.indicator g n) := by
          simp only [← Real.exp_sum, Nat.primesBelow, sum_filter, Set.indicator_apply,
            Set.mem_ofPred_eq]
      _ ≤ _ := Real.exp_le_exp.2 <| hind.sum_le_tsum _ fun n _ ↦
          Set.indicator_nonneg (fun n _ ↦ hg₀ n) n
  rcases em (0 ∈ u) with h0 | h0
  · rw [← add_sum_erase _ _ h0]
    linarith
  · rw [← erase_eq_of_notMem h0]
    linarith [hg₀ 0]

end TauCeti
