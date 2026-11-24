/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.ContinuedFractions.Basic
public import TauCeti.NumberTheory.Real.GoldenRatio

/-!
# The continued fraction of the golden ratio

The golden ratio `φ` satisfies `φ = 1 + 1 / φ`, so its continued fraction is `[1; 1, 1, …]`: every
partial quotient is `1`. The continuants therefore satisfy the Fibonacci recurrence, and the
convergents of `φ`, written in lowest terms, are the ratios of consecutive Fibonacci numbers:

`φ.convergent n = fib (n + 2) / fib (n + 1)`.

Combined with Binet's formula this gives the exact approximation error
`fib (n + 1) * φ - fib (n + 2) = -ψ ^ (n + 1)`, where `ψ` is the conjugate of `φ`. Since `1` is the
smallest possible partial quotient, the denominators of the convergents of `φ` grow as slowly as
those of an irrational number can: the bound `Real.fib_succ_le_den_convergent` is an equality
for `φ`.

## Main results

* `TauCeti.partDens_of_goldenRatio`: every partial denominator of `GenContFract.of φ` is `1`.
* `TauCeti.dens_of_goldenRatio`, `TauCeti.nums_of_goldenRatio`: the continuants of `φ` are
  `fib (n + 1)` and `fib (n + 2)`.
* `TauCeti.den_convergent_goldenRatio`, `TauCeti.num_convergent_goldenRatio`,
  `TauCeti.convergent_goldenRatio`: the convergents of `φ` are `fib (n + 2) / fib (n + 1)`, in
  lowest terms.
* `TauCeti.den_convergent_goldenRatio_mul_sub_num`, `TauCeti.goldenRatio_sub_convergent`: the
  exact error of the `n`-th convergent.

## References

* A. Ya. Khinchin, *Continued Fractions*, ch. I, §4.
-/

public section

open GenContFract (of IntFractPair)
open scoped goldenRatio
open Real

namespace TauCeti

/-- Every step of the continued fraction algorithm for the golden ratio returns the integer part
`1` and the fractional part `φ - 1`. -/
private theorem stream_goldenRatio (n : ℕ) : IntFractPair.stream φ n = some ⟨1, φ - 1⟩ := by
  induction n with
  | zero => simp [IntFractPair.stream, IntFractPair.of, fract_goldenRatio]
  | succ n ih =>
    have h : φ - 1 ≠ 0 := by linarith [one_lt_goldenRatio]
    rw [IntFractPair.stream_succ_of_some ih h, ← fract_goldenRatio, inv_fract_goldenRatio]
    simp [IntFractPair.of]

/-- Every entry of the continued fraction of the golden ratio is the pair `⟨1, 1⟩`. -/
private theorem s_of_goldenRatio (n : ℕ) : (of φ).s.get? n = some ⟨1, 1⟩ := by
  simpa using GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream
    (stream_goldenRatio (n + 1))

/-- Every partial denominator of the continued fraction of the golden ratio is `1`: the
continued fraction is `[1; 1, 1, …]`. -/
@[simp]
theorem partDens_of_goldenRatio (n : ℕ) : (of φ).partDens.get? n = some 1 :=
  GenContFract.partDen_eq_s_b (s_of_goldenRatio n)

/-- The denominator continuants of the golden ratio are the Fibonacci numbers. -/
@[simp]
theorem dens_of_goldenRatio (n : ℕ) : (of φ).dens n = Nat.fib (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [GenContFract.zeroth_den_eq_one]
  | one => simp [GenContFract.first_den_eq (s_of_goldenRatio 0)]
  | more n ih₀ ih₁ =>
    rw [GenContFract.dens_recurrence (s_of_goldenRatio (n + 1)) ih₀ ih₁,
      Nat.fib_add_two (n := n + 1)]
    push_cast
    ring

/-- The numerator continuants of the golden ratio are the Fibonacci numbers, shifted by one. -/
@[simp]
theorem nums_of_goldenRatio (n : ℕ) : (of φ).nums n = Nat.fib (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [GenContFract.zeroth_num_eq_h, GenContFract.of_h_eq_floor]
  | one =>
    rw [GenContFract.first_num_eq (s_of_goldenRatio 0), GenContFract.of_h_eq_floor,
      floor_goldenRatio]
    norm_num [Nat.fib_add_two]
  | more n ih₀ ih₁ =>
    rw [GenContFract.nums_recurrence (s_of_goldenRatio (n + 1)) ih₀ ih₁,
      Nat.fib_add_two (n := n + 2)]
    push_cast
    ring

/-- The denominator of the `n`-th convergent of the golden ratio is `fib (n + 1)`. In particular
the lower bound `Real.fib_succ_le_den_convergent` is attained by the golden ratio. -/
@[simp]
theorem den_convergent_goldenRatio (n : ℕ) : (convergent φ n).den = Nat.fib (n + 1) := by
  have h := den_convergent φ n
  rw [dens_of_goldenRatio] at h
  exact_mod_cast h

/-- The numerator of the `n`-th convergent of the golden ratio is `fib (n + 2)`. -/
@[simp]
theorem num_convergent_goldenRatio (n : ℕ) : (convergent φ n).num = Nat.fib (n + 2) := by
  have h := num_convergent φ n
  rw [nums_of_goldenRatio] at h
  exact_mod_cast h

/-- The convergents of the golden ratio are the ratios of consecutive Fibonacci numbers. -/
theorem convergent_goldenRatio (n : ℕ) :
    convergent φ n = (Nat.fib (n + 2) : ℚ) / Nat.fib (n + 1) := by
  rw [← Rat.num_div_den (convergent φ n), num_convergent_goldenRatio, den_convergent_goldenRatio]
  simp

/-- The exact error of the `n`-th convergent `p / q` of the golden ratio, in the form
`q * φ - p = -ψ ^ (n + 1)`. -/
theorem den_convergent_goldenRatio_mul_sub_num (n : ℕ) :
    (convergent φ n).den * φ - (convergent φ n).num = -ψ ^ (n + 1) := by
  rw [den_convergent_goldenRatio, num_convergent_goldenRatio]
  push_cast
  linear_combination -fib_succ_sub_goldenRatio_mul_fib (n + 1)

/-- The exact error of the `n`-th convergent of the golden ratio. -/
theorem goldenRatio_sub_convergent (n : ℕ) :
    φ - convergent φ n = -ψ ^ (n + 1) / Nat.fib (n + 1) := by
  have hpos : (0 : ℝ) < Nat.fib (n + 1) := by exact_mod_cast Nat.fib_pos.mpr n.succ_pos
  rw [convergent_goldenRatio, eq_div_iff hpos.ne']
  push_cast
  rw [sub_mul, div_mul_cancel₀ _ hpos.ne']
  linear_combination -fib_succ_sub_goldenRatio_mul_fib (n + 1)

/-- The convergents of the golden ratio alternate around it: the `n`-th convergent lies below the
golden ratio exactly when `n` is even. -/
theorem convergent_goldenRatio_lt_iff (n : ℕ) : (convergent φ n : ℝ) < φ ↔ Even n := by
  have hpos : (0 : ℝ) < Nat.fib (n + 1) := by exact_mod_cast Nat.fib_pos.mpr n.succ_pos
  rw [← sub_pos, goldenRatio_sub_convergent, div_pos_iff_of_pos_right hpos, neg_pos]
  rcases Nat.even_or_odd n with h | h
  · exact iff_of_true (h.add_one.pow_neg goldenConj_neg) h
  · exact iff_of_false (not_lt.mpr (h.add_one.pow_nonneg ψ)) (Nat.not_even_iff_odd.mpr h)

end TauCeti
