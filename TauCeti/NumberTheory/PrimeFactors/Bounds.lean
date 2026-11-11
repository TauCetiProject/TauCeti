/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Subpower bounds for products over prime divisors

For every fixed `C ≥ 1` and `ε > 0`, the product `C ^ ω(n)` is at most `A n ^ ε`, with
`A` independent of the positive integer `n`. Here `ω(n)` counts distinct prime divisors.
This controls finite Euler corrections whose local factors are uniformly bounded.

The elementary argument separates the finitely many primes for which `p ^ ε < C`.
See Davenport, *Multiplicative Number Theory*, the discussion of elementary divisor bounds.
-/

public section

open Finset Filter

namespace TauCeti

/-- A fixed exponential of the number of distinct prime factors grows more slowly than any
positive power, uniformly over all positive integers. -/
theorem exists_pow_card_primeFactors_le_mul_rpow {C ε : ℝ} (hC : 1 ≤ C) (hε : 0 < ε) :
    ∃ A > 0, ∀ n : ℕ, n ≠ 0 → C ^ n.primeFactors.card ≤ A * (n : ℝ) ^ ε := by
  obtain ⟨P, hP⟩ := eventually_atTop.1 <|
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop C)
  refine ⟨C ^ P, pow_pos (lt_of_lt_of_le zero_lt_one hC) _, fun n hn ↦ ?_⟩
  have hsmall : (n.primeFactors.filter (· < P)).card ≤ P := by
    have hsub : n.primeFactors.filter (· < P) ⊆ range P :=
      fun _ hp ↦ mem_range.2 (mem_filter.1 hp).2
    simpa using card_le_card hsub
  have hprod : (∏ p ∈ n.primeFactors, (p : ℝ)) ≤ n := by
    simpa only [Nat.cast_prod] using (Nat.cast_le (α := ℝ)).mpr
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n))
  calc
    C ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, C := (prod_const C).symm
    _ ≤ ∏ p ∈ n.primeFactors, (if p < P then C else 1) * (p : ℝ) ^ ε := by
      apply Finset.prod_le_prod₀ (fun _ _ ↦ le_trans zero_le_one hC)
      intro p hp
      have hp1 : (1 : ℝ) ≤ p := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
      split_ifs with h
      · exact le_mul_of_one_le_right (le_trans zero_le_one hC)
          (Real.one_le_rpow hp1 hε.le)
      · simpa using hP p (by omega)
    _ = C ^ (n.primeFactors.filter (· < P)).card * (∏ p ∈ n.primeFactors, (p : ℝ)) ^ ε := by
      rw [prod_mul_distrib, ← prod_filter, prod_const, Real.finsetProd_rpow]
      exact fun _ _ ↦ Nat.cast_nonneg _
    _ ≤ C ^ P * (n : ℝ) ^ ε := by gcongr

end TauCeti
