/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Basic
public import TauCeti.Algebra.BigOperators.ModEq
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Data.Nat.Cast.Basic
import TauCeti.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
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
  have hperm := hhc.sum_range_mul_mod (fun r ↦ (r : ℤ))
  simp only [Nat.cast_mod_eq_sub_mul_div, Nat.cast_mul, sum_sub_distrib, ← mul_sum] at hperm
  have heq : (∑ r ∈ range c, ((h * r / c : ℕ) : ℤ)) * 2 =
      ((h : ℤ) - 1) * (c - 1) := by
    apply mul_left_cancel₀ (show (c : ℤ) ≠ 0 by positivity)
    linear_combination -2 * hperm + ((h : ℤ) - 1) * sum_range_natCast_mul_two (R := ℤ) c
  have heq' : (((∑ r ∈ range c, h * r / c) * 2 : ℕ) : ℤ) =
      (((h - 1) * (c - 1) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hh, Nat.cast_sub hc]
    exact heq
  exact_mod_cast heq'

/-- For coprime naturals `h` and `c`, `∑_{r < c} ⌊h r / c⌋ = (h - 1)(c - 1) / 2`. -/
theorem Nat.Coprime.sum_range_div {h c : ℕ} (hhc : h.Coprime c) :
    ∑ r ∈ range c, h * r / c = (h - 1) * (c - 1) / 2 := by
  rw [← hhc.sum_range_div_mul_two, Nat.mul_div_cancel _ (by decide)]

/-- For coprime `h` and `c`, the floor sum is `(h - 1)(c - 1) / 2` in any
division ring where `2 ≠ 0`. -/
theorem Nat.Coprime.sum_range_natCast_div {K : Type*} [DivisionRing K] [NeZero (2 : K)]
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
  exact (eq_div_iff two_ne_zero).2 heq

/-- For coprime `h` and `c`, the second moment of `⌊h r / c⌋` in `ℕ`:
`6 c ∑_{r < c} ⌊h r / c⌋² + (h² - 1)(c - 1)(2c - 1) = 12 h ∑_{r < c} r ⌊h r / c⌋`. -/
theorem Nat.Coprime.mul_sum_range_div_sq_mul_six_add {h c : ℕ} (hhc : h.Coprime c) :
    c * (∑ r ∈ range c, (h * r / c) ^ 2) * 6 + (h ^ 2 - 1) * (c - 1) * (2 * c - 1) =
      12 * h * ∑ r ∈ range c, r * (h * r / c) := by
  rcases h.eq_zero_or_pos with rfl | hh
  · obtain rfl : c = 1 := by simpa using hhc
    simp
  rcases c.eq_zero_or_pos with rfl | hc
  · simp
  have hperm := hhc.sum_range_mul_mod (fun r ↦ (r : ℤ) ^ 2)
  have hterm (r : ℕ) : (((h * r % c : ℕ) : ℤ)) ^ 2 = h ^ 2 * (r : ℤ) ^ 2 -
      2 * h * c * ((r * (h * r / c) : ℕ) : ℤ) + c ^ 2 * ((h * r / c : ℕ) : ℤ) ^ 2 := by
    rw [Nat.cast_mod_eq_sub_mul_div]
    push_cast
    ring
  simp only [hterm, sum_add_distrib, sum_sub_distrib, ← mul_sum] at hperm
  push_cast at hperm
  have heq : (((c * (∑ r ∈ range c, (h * r / c) ^ 2) * 6 +
      (h ^ 2 - 1) * (c - 1) * (2 * c - 1) : ℕ)) : ℤ) =
      ((12 * h * ∑ r ∈ range c, r * (h * r / c) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hh), Nat.cast_sub hc,
      Nat.cast_sub (by omega : 1 ≤ 2 * c)]
    apply mul_left_cancel₀ (show (c : ℤ) ≠ 0 by positivity)
    linear_combination 6 * hperm - ((h : ℤ) ^ 2 - 1) * sum_range_natCast_sq_mul_six (R := ℤ) c
  exact_mod_cast heq

/-- For coprime `h` and `c` in a division ring where `2 ≠ 0` and `3 ≠ 0`,
`c ∑_{r < c} ⌊h r / c⌋² = 2h ∑_{r < c} r⌊h r / c⌋ + (1 - h²)(c - 1)(2c - 1)/6`. -/
theorem Nat.Coprime.mul_sum_range_natCast_div_sq {K : Type*} [DivisionRing K] [NeZero (2 : K)]
    [NeZero (3 : K)] {h c : ℕ} (hhc : h.Coprime c) :
    (c : K) * ∑ r ∈ range c, ((h * r / c : ℕ) : K) ^ 2 =
      2 * h * ∑ r ∈ range c, (r : K) * ((h * r / c : ℕ) : K) +
        (1 - h ^ 2) * ((c - 1) * (2 * c - 1) / 6) := by
  rcases h.eq_zero_or_pos with rfl | hh
  · obtain rfl : c = 1 := by simpa using hhc
    simp
  rcases c.eq_zero_or_pos with rfl | hc
  · obtain rfl : h = 1 := by simpa using hhc
    simp
  have h6 : (6 : K) ≠ 0 := by
    rw [show (6 : K) = 2 * 3 by norm_num]
    exact mul_ne_zero two_ne_zero three_ne_zero
  have heq := congrArg (Nat.cast : ℕ → K) hhc.mul_sum_range_div_sq_mul_six_add
  push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hh), Nat.cast_sub hc,
    Nat.cast_sub (by omega : 1 ≤ 2 * c)] at heq
  rw [← mul_div_assoc, ← sub_eq_iff_eq_add', eq_div_iff h6]
  rw [sub_mul, eq_sub_of_add_eq heq]
  noncomm_ring

/-- For coprime naturals `h` and `c`,
`∑_{r < c} r (⌊h r / c⌋ + 1) + ∑_{s < h} ∑_{r ≤ ⌊c s / h⌋} r = h ∑_{r < c} r`.
This counts the rectangle on either side of `c s = h r`, weighted by `r`. -/
theorem Nat.Coprime.sum_mul_div_add_sum_sum {h c : ℕ} (hhc : h.Coprime c) :
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

