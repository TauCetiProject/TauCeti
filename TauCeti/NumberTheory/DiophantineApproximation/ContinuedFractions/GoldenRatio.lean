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

The golden ratio is also the extremal case of Hurwitz's theorem
(`Real.infinite_rat_abs_sub_lt_one_div_sqrt_five_mul_den_sq_of_irrational`): along the convergents
`p / q` of `φ`, the quantity `q * |q * φ - p|` tends to `1 / √5`. That the constant `√5` cannot be
improved for `φ` is `TauCeti.finite_setOf_abs_goldenRatio_sub_lt_of_sqrt_five_lt`, in
`TauCeti.NumberTheory.DiophantineApproximation.Hurwitz`; its proof does not use continued
fractions.

## Main results

* `TauCeti.partDens_of_goldenRatio`: every partial denominator of `GenContFract.of φ` is `1`.
* `TauCeti.dens_of_goldenRatio`, `TauCeti.nums_of_goldenRatio`: the continuants of `φ` are
  `fib (n + 1)` and `fib (n + 2)`.
* `TauCeti.den_convergent_goldenRatio`, `TauCeti.num_convergent_goldenRatio`,
  `TauCeti.convergent_goldenRatio`: the convergents of `φ` are `fib (n + 2) / fib (n + 1)`, in
  lowest terms.
* `TauCeti.den_convergent_goldenRatio_mul_sub_num`, `TauCeti.goldenRatio_sub_convergent`: the
  exact error of the `n`-th convergent.
* `TauCeti.den_convergent_goldenRatio_mul_abs`,
  `TauCeti.tendsto_den_convergent_goldenRatio_mul_abs`: at the `n`-th convergent `p / q`,
  `q * |q * φ - p| = (1 - (-ψ ^ 2) ^ (n + 1)) / √5`, which tends to `1 / √5`.

## References

* A. Ya. Khinchin, *Continued Fractions*, ch. I, §4.
* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, ch. XI.
-/

public section

open GenContFract (of IntFractPair)
open scoped goldenRatio
open Real Filter Topology

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

/-- The exact value of `q * |q * φ - p|` at the `n`-th convergent `p / q` of the golden ratio. -/
theorem den_convergent_goldenRatio_mul_abs (n : ℕ) :
    (convergent φ n).den * |(convergent φ n).den * φ - (convergent φ n).num| =
      (1 - (-ψ ^ 2) ^ (n + 1)) / √5 := by
  have h1 : φ * -ψ = 1 := by linarith [goldenRatio_mul_goldenConj]
  have h2 : ψ * -ψ = -ψ ^ 2 := by ring
  have habs : |(-ψ ^ (n + 1))| = (-ψ) ^ (n + 1) := by simp [abs_pow, abs_of_neg goldenConj_neg]
  rw [den_convergent_goldenRatio_mul_sub_num, den_convergent_goldenRatio, coe_fib_eq, habs]
  calc (φ ^ (n + 1) - ψ ^ (n + 1)) / √5 * (-ψ) ^ (n + 1)
      = ((φ * -ψ) ^ (n + 1) - (ψ * -ψ) ^ (n + 1)) / √5 := by
        simp only [mul_pow]; ring
    _ = (1 - (-ψ ^ 2) ^ (n + 1)) / √5 := by rw [h1, h2, one_pow]

/-- Along the convergents `p / q` of the golden ratio, `q * |q * φ - p|` tends to `1 / √5`: the
constant `√5` in Hurwitz's theorem is attained in the limit by the convergents of `φ`. -/
theorem tendsto_den_convergent_goldenRatio_mul_abs :
    Tendsto (fun n : ℕ ↦
      (convergent φ n).den * |(convergent φ n).den * φ - (convergent φ n).num|)
      atTop (𝓝 (1 / √5)) := by
  simp_rw [den_convergent_goldenRatio_mul_abs]
  have hψ : |ψ| < 1 := abs_lt.mpr ⟨neg_one_lt_goldenConj, goldenConj_neg.trans one_pos⟩
  have h : |(-ψ ^ 2)| < 1 := by
    simpa only [abs_neg, abs_pow] using pow_lt_one₀ (abs_nonneg ψ) hψ two_ne_zero
  have h0 := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h).comp (tendsto_add_atTop_nat 1)
  simpa using (h0.const_sub 1).div_const √5

end TauCeti
