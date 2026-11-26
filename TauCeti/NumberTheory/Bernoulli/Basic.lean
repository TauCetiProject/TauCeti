/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Primorial

/-!
# Evaluation of `bernoulli 12` and denominators of Bernoulli numbers

Mathlib records `bernoulli 0` through `bernoulli 6` in `Mathlib.NumberTheory.Bernoulli`. This file
evaluates `B₁₂ = -691 / 2730`, which is used to compute the positive-degree `q`-expansion
coefficients of the normalised weight-`12` Eisenstein series `E₁₂`.

It also clears the denominators of `B₀, …, Bₖ` with the primorial `Pₖ₊₁ = primorial (k + 1)`,
the product of the primes `≤ k + 1`, through Mathlib's theorem of von Staudt and Clausen
(`Bernoulli.vonStaudt_clausen`).

## Main results

* `TauCeti.bernoulli_twelve`: `bernoulli 12 = -691 / 2730`.
* `TauCeti.exists_intCast_eq_primorial_mul_bernoulli`: for `i ≤ k`, `Pₖ₊₁ Bᵢ` is an integer.

## Provenance

`TauCeti.exists_intCast_eq_primorial_mul_bernoulli` is adapted from grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/Cyclotomic/Voronoi.lean`, declaration
`New.OddPart.exists_intCast_eq_factorial_mul_bernoulli`. There the denominators are cleared with
`(k + 1)!`; here they are cleared with the primorial, through von Staudt–Clausen.
-/

public section

namespace TauCeti

/- `bernoulli` is computed through `bernoulli'`, which is defined by well-founded recursion, so
neither `norm_num` nor elaborator-side `decide` can evaluate it; the kernel can. -/

/-- The twelfth Bernoulli number `B₁₂ = -691 / 2730`. -/
@[simp]
theorem bernoulli_twelve : bernoulli 12 = -691 / 2730 := by decide +kernel

open Finset Nat in
/-- **Denominators of Bernoulli numbers.** For `i ≤ k`, the product `primorial (k + 1)` of the
primes `≤ k + 1` times the Bernoulli number `Bᵢ` is an integer. This is the theorem of von Staudt
and Clausen, together with `B₁ = -1 / 2` and `Bᵢ = 0` for odd `i ≥ 3`. -/
theorem exists_intCast_eq_primorial_mul_bernoulli {i k : ℕ} (hi : i ≤ k) :
    ∃ z : ℤ, (z : ℚ) = primorial (k + 1) * bernoulli i := by
  obtain _ | _ | i := i
  · exact ⟨primorial (k + 1), by simp⟩
  · obtain ⟨c, hc⟩ : 2 ∣ primorial (k + 1) := Nat.prime_two.dvd_primorial_iff.2 (by omega)
    exact ⟨-c, by rw [hc, bernoulli_one]; push_cast; ring⟩
  rcases Nat.even_or_odd (i + 2) with ⟨m, hm⟩ | ho
  swap
  · exact ⟨0, by rw [bernoulli_eq_zero_of_odd ho (by omega)]; simp⟩
  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen m
  set S := (range (2 * m + 2)).filter fun p ↦ p.Prime ∧ (p - 1) ∣ 2 * m
  -- every prime of the von Staudt–Clausen sum is at most `2 m + 1 = i + 3 ≤ k + 1`
  have hS (p : ℕ) (hp : p ∈ S) : p ∣ primorial (k + 1) := by
    simp only [S, mem_filter, mem_range] at hp
    exact hp.2.1.dvd_primorial_iff.2 (by omega)
  refine ⟨primorial (k + 1) * z - ∑ p ∈ S, (primorial (k + 1) / p : ℕ), ?_⟩
  have hp (p : ℕ) (hp : p ∈ S) :
      ((primorial (k + 1) / p : ℕ) : ℚ) = primorial (k + 1) * (1 / p) := by
    rw [Nat.cast_div (hS p hp)]
    · ring
    · simp only [S, mem_filter] at hp
      exact_mod_cast hp.2.1.ne_zero
  have hb : bernoulli (i + 1 + 1) = bernoulli (2 * m) := by rw [two_mul, ← hm]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]
  rw [Nat.cast_sum, sum_congr rfl hp, ← mul_sum]
  linear_combination (primorial (k + 1) : ℚ) * (hz - hb)

end TauCeti
