/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.BigOperators.Field
public import TauCeti.Algebra.BigOperators.ModEq
import TauCeti.Data.Nat.Cast.Basic
import TauCeti.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Floor sums for coprime natural numbers

For coprime `h` and `c`, multiplication by `h` permutes residues modulo `c`. Summing the
remainders and their squares yields identities for the first two moments of `⌊h r / c⌋`.
A weighted count of lattice points on either side of `c s = h r` relates the floor sums
with `h` and `c` exchanged. These identities supply the elementary proof of Dedekind reciprocity.

## References

* H. Rademacher and E. Grosswald, *Dedekind Sums*, Chapter 2 (the lattice-point proof).
-/

public section

open Finset

/-- For coprime `h` and `c`, the sum of `⌊h r / c⌋` over `r < c`, doubled,
is `(h - 1) * (c - 1)` in `ℕ`. -/
theorem Nat.Coprime.sum_range_div_mul_two {h c : ℕ} (hhc : h.Coprime c) :
    (∑ r ∈ range c, h * r / c) * 2 = (h - 1) * (c - 1) := by
  rcases h.eq_zero_or_pos with rfl | hh
  · simp
  rcases c.eq_zero_or_pos with rfl | hc
  · simp
  have hperm := hhc.sum_range_mul_mod (fun r ↦ (r : ℚ))
  simp only [Nat.cast_mod_eq_sub_mul_div, Nat.cast_mul, sum_sub_distrib, ← mul_sum,
    sum_range_natCast] at hperm
  have heq : (∑ r ∈ range c, ((h * r / c : ℕ) : ℚ)) * 2 =
      ((h : ℚ) - 1) * (c - 1) := by
    apply mul_left_cancel₀ (show (c : ℚ) ≠ 0 by positivity)
    linear_combination -2 * hperm
  have heq' : (((∑ r ∈ range c, h * r / c) * 2 : ℕ) : ℚ) =
      (((h - 1) * (c - 1) : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub hh, Nat.cast_sub hc]
    exact heq
  exact_mod_cast heq'

/-- For coprime naturals `h` and `c`, `∑_{r < c} ⌊h r / c⌋ = (h - 1)(c - 1) / 2`. -/
theorem Nat.Coprime.sum_range_div {h c : ℕ} (hhc : h.Coprime c) :
    ∑ r ∈ range c, h * r / c = (h - 1) * (c - 1) / 2 := by
  rw [← hhc.sum_range_div_mul_two, Nat.mul_div_cancel _ (by decide)]

/-- For coprime `h` and `c`, the floor sum is `(h - 1)(c - 1) / 2` in any
characteristic-zero field. -/
theorem Nat.Coprime.sum_range_cast_div {K : Type*} [Field K] [CharZero K]
    {h c : ℕ} (hhc : h.Coprime c) :
    ∑ r ∈ range c, ((h * r / c : ℕ) : K) = (h - 1) * (c - 1) / 2 := by
  rcases h.eq_zero_or_pos with rfl | hh
  · have : c = 1 := by simpa using hhc
    subst c
    simp
  rcases c.eq_zero_or_pos with rfl | hc
  · have : h = 1 := by simpa using hhc
    subst h
    simp
  have heq := congrArg (Nat.cast : ℕ → K) hhc.sum_range_div_mul_two
  push_cast [Nat.cast_sub hh, Nat.cast_sub hc] at heq
  exact (eq_div_iff (by norm_num)).2 heq

/-- For coprime `h` and `c` in a characteristic-zero field,
`c² ∑_{r < c} ⌊h r / c⌋² = 2hc ∑_{r < c} r⌊h r / c⌋ +
(1 - h²)c(c - 1)(2c - 1)/6`. -/
theorem Nat.Coprime.sq_mul_sum_div_sq {K : Type*} [Field K] [CharZero K]
    {h c : ℕ} (hhc : h.Coprime c) :
    (c : K) ^ 2 * ∑ r ∈ range c, ((h * r / c : ℕ) : K) ^ 2 =
      2 * h * c * (∑ r ∈ range c, r * (h * r / c) : ℕ) +
        (1 - h ^ 2) * (c * (c - 1) * (2 * c - 1) / 6) := by
  have hperm := Nat.Coprime.sum_range_mul_mod hhc (fun r ↦ (r : K) ^ 2)
  have hterm (r : ℕ) : (((h * r % c : ℕ) : K)) ^ 2 = h ^ 2 * (r : K) ^ 2 -
      2 * h * c * ((r * (h * r / c) : ℕ) : K) + c ^ 2 * ((h * r / c : ℕ) : K) ^ 2 := by
    rw [Nat.cast_mod_eq_sub_mul_div]
    push_cast
    ring
  simp only [hterm, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_range_natCast_sq] at hperm
  push_cast at hperm ⊢
  linear_combination hperm

/-- For coprime naturals `h` and `c`,
`∑_{r < c} r (⌊h r / c⌋ + 1) + ∑_{s < h} ∑_{r ≤ ⌊c s / h⌋} r = h ∑_{r < c} r`.
This counts the rectangle on either side of `c s = h r`, weighted by `r`. -/
theorem TauCeti.sum_mul_div_add_sum_sum {h c : ℕ} (hhc : h.Coprime c) :
    ∑ r ∈ range c, r * (h * r / c + 1) + ∑ s ∈ range h, ∑ r ∈ range (c * s / h + 1), r =
      h * ∑ r ∈ range c, r := by
  rcases h.eq_zero_or_pos with rfl | hh
  · have : c = 1 := by simpa using hhc
    subst c
    simp
  rcases c.eq_zero_or_pos with rfl | hc
  · simp
  have hsplit : ∀ r ∈ range c, ∀ s ∈ range h,
      (if c * s ≤ h * r then r else 0) + (if h * r ≤ c * s then r else 0) = r := by
    intro r hr s hs
    rw [mem_range] at hr hs
    by_cases h₁ : c * s ≤ h * r <;> by_cases h₂ : h * r ≤ c * s <;> simp only [h₁, h₂,
      ↓reduceIte, add_zero, zero_add]
    · have hdvd : c ∣ r := hhc.symm.dvd_of_dvd_mul_left ⟨s, (le_antisymm h₁ h₂).symm⟩
      obtain rfl : r = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hr
      rfl
    · omega
  have h₁ : ∑ r ∈ range c, ∑ s ∈ range h, (if c * s ≤ h * r then r else 0) =
      ∑ r ∈ range c, r * (h * r / c + 1) := by
    refine sum_congr rfl fun r hr ↦ ?_
    rw [← sum_filter,
      filter_range_mul_le_of_div_lt hc (Nat.div_lt_of_lt_mul (by nlinarith [mem_range.1 hr])),
      sum_const, card_range,
      smul_eq_mul, mul_comm]
  have h₂ : ∑ r ∈ range c, ∑ s ∈ range h, (if h * r ≤ c * s then r else 0) =
      ∑ s ∈ range h, ∑ r ∈ range (c * s / h + 1), r := by
    rw [sum_comm]
    refine sum_congr rfl fun s hs ↦ ?_
    rw [← sum_filter,
      filter_range_mul_le_of_div_lt hh (Nat.div_lt_of_lt_mul (by nlinarith [mem_range.1 hs]))]
  rw [← h₁, ← h₂, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun r hr ↦ ?_
  rw [← sum_add_distrib, sum_congr rfl (hsplit r hr), sum_const, card_range, smul_eq_mul]

