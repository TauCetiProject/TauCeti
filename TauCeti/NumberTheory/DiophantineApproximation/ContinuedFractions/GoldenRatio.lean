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
(`Real.infinite_rat_abs_sub_lt_one_div_sqrt_five_mul_den_sq_of_irrational`): the constant `√5`
cannot be improved for `φ`. Indeed `(q * φ - p) * (q * ψ - p) = p ^ 2 - p * q - q ^ 2` is a
nonzero integer for integers `p` and `q ≠ 0`, and `q * ψ - p = q * φ - p - q * √5`, so that
`x = |q * φ - p|` satisfies `1 ≤ x * (x + q * √5)`; for `c > √5` this bounds the denominators of the
rationals `p / q` with `|φ - p / q| < 1 / (c * q ^ 2)`. Along the convergents, `q * |q * φ - p|`
tends to `1 / √5`.

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
* `TauCeti.one_le_abs_mul_goldenRatio_sub_mul_abs_mul_goldenConj_sub`,
  `TauCeti.one_le_abs_mul_goldenRatio_sub_mul_add`: the lower bounds
  `1 ≤ |q * φ - p| * |q * ψ - p|` and `1 ≤ |q * φ - p| * (|q * φ - p| + q * √5)`.
* `TauCeti.sq_mul_lt_one_of_abs_mul_goldenRatio_sub_mul_lt`: for `c ≥ 0`, the bound
  `|q * φ - p| * (c * q) < 1` forces `q ^ 2 * (c * (c - √5)) < 1`.
* `TauCeti.finite_setOf_abs_goldenRatio_sub_lt_of_sqrt_five_lt`: sharpness of Hurwitz's theorem
  at `φ`: for `c > √5`, only finitely many rationals `r` satisfy
  `|φ - r| < 1 / (c * r.den ^ 2)`.

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
  rw [den_convergent_goldenRatio_mul_sub_num, den_convergent_goldenRatio, abs_neg, abs_pow,
    coe_fib_eq, abs_of_neg goldenConj_neg, div_mul_eq_mul_div, sub_mul, ← mul_pow, ← mul_pow, h1,
    h2, one_pow]

/-- Along the convergents `p / q` of the golden ratio, `q * |q * φ - p|` tends to `1 / √5`: the
constant `√5` in Hurwitz's theorem is attained in the limit by the convergents of `φ`. -/
theorem tendsto_den_convergent_goldenRatio_mul_abs :
    Tendsto (fun n : ℕ ↦
      (convergent φ n).den * |(convergent φ n).den * φ - (convergent φ n).num|)
      atTop (𝓝 (1 / √5)) := by
  simp_rw [den_convergent_goldenRatio_mul_abs]
  have h : |(-ψ ^ 2)| < 1 := by
    rw [abs_neg, abs_pow, sq_lt_one_iff_abs_lt_one, abs_abs]
    exact abs_lt.mpr ⟨neg_one_lt_goldenConj, goldenConj_neg.trans one_pos⟩
  have h0 := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h).comp (tendsto_add_atTop_nat 1)
  simpa using (h0.const_sub 1).div_const √5

/-! ### Sharpness of Hurwitz's theorem at the golden ratio -/

/-- The norm form `p ^ 2 - p * q - q ^ 2` of `ℤ[φ]` does not vanish at integers `p` and `q ≠ 0`,
so the product of `q * φ - p` and its conjugate `q * ψ - p` has absolute value at least `1`. -/
theorem one_le_abs_mul_goldenRatio_sub_mul_abs_mul_goldenConj_sub (p : ℤ) {q : ℤ} (hq : q ≠ 0) :
    1 ≤ |q * φ - p| * |q * ψ - p| := by
  have hφ : (q : ℝ) * φ - p ≠ 0 :=
    sub_ne_zero.mpr ((goldenRatio_irrational.intCast_mul hq).ne_int p)
  have hψ : (q : ℝ) * ψ - p ≠ 0 :=
    sub_ne_zero.mpr ((goldenConj_irrational.intCast_mul hq).ne_int p)
  have h : ((q : ℝ) * φ - p) * (q * ψ - p) = ((p ^ 2 - p * q - q ^ 2 : ℤ) : ℝ) := by
    push_cast
    linear_combination (q : ℝ) ^ 2 * goldenRatio_mul_goldenConj -
      (p : ℝ) * q * goldenRatio_add_goldenConj
  have h0 : p ^ 2 - p * q - q ^ 2 ≠ 0 := fun h0 ↦
    mul_ne_zero hφ hψ (by rw [h, h0, Int.cast_zero])
  rw [← abs_mul, h, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs h0

/-- A rational approximation `p / q` of the golden ratio is never much better than `1 / (√5 q ^ 2)`:
with `x = |q * φ - p|`, one has `1 ≤ x * (x + q * √5)`. -/
theorem one_le_abs_mul_goldenRatio_sub_mul_add (p : ℤ) {q : ℕ} (hq : q ≠ 0) :
    1 ≤ |q * φ - p| * (|q * φ - p| + q * √5) := by
  have h := one_le_abs_mul_goldenRatio_sub_mul_abs_mul_goldenConj_sub p (q := q) (mod_cast hq)
  have hy : ((q : ℤ) : ℝ) * ψ - p = (q : ℝ) * φ - p - q * √5 := by
    rw [← goldenRatio_sub_goldenConj]
    push_cast
    ring
  rw [hy, Int.cast_natCast] at h
  have h5 : (0 : ℝ) ≤ q * √5 := by positivity
  refine h.trans (mul_le_mul_of_nonneg_left (abs_le.mpr ⟨?_, ?_⟩) (abs_nonneg _))
  · linarith [neg_abs_le ((q : ℝ) * φ - p)]
  · linarith [le_abs_self ((q : ℝ) * φ - p)]

/-- A rational approximation `p / q` of the golden ratio with `|q * φ - p| * (c * q) < 1` satisfies
`q ^ 2 * (c * (c - √5)) < 1`. For `c > √5` this bounds the denominator `q`. -/
theorem sq_mul_lt_one_of_abs_mul_goldenRatio_sub_mul_lt {c : ℝ} (hc : 0 ≤ c) (p : ℤ) (q : ℕ)
    (h : |q * φ - p| * (c * q) < 1) : (q : ℝ) ^ 2 * (c * (c - √5)) < 1 := by
  rcases le_or_gt c √5 with hc5 | hc5
  · linarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (q : ℝ))
      (mul_nonpos_of_nonneg_of_nonpos hc (sub_nonpos.mpr hc5))]
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hc0 : 0 < c := (Real.sqrt_nonneg 5).trans_lt hc5
  have hnorm := one_le_abs_mul_goldenRatio_sub_mul_add p hq
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = q * φ - p := ⟨_, rfl⟩
  rw [← hx] at h hnorm
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = |x| * (c * q) := ⟨_, rfl⟩
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  have hw1 : w < 1 := hw ▸ h
  have key : c ^ 2 * (q : ℝ) ^ 2 ≤ w * w + w * (c * (q : ℝ) ^ 2 * √5) :=
    calc c ^ 2 * (q : ℝ) ^ 2 = c ^ 2 * (q : ℝ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ c ^ 2 * (q : ℝ) ^ 2 * (|x| * (|x| + q * √5)) := by gcongr
      _ = w * w + w * (c * (q : ℝ) ^ 2 * √5) := by rw [hw]; ring
  have h1 : w * w < 1 := by nlinarith
  have h2 : w * (c * (q : ℝ) ^ 2 * √5) ≤ c * (q : ℝ) ^ 2 * √5 :=
    mul_le_of_le_one_left (by positivity) hw1.le
  linarith [show (q : ℝ) ^ 2 * (c * (c - √5)) =
    c ^ 2 * (q : ℝ) ^ 2 - c * (q : ℝ) ^ 2 * √5 by ring]

/-- **Sharpness of Hurwitz's theorem at the golden ratio.** For every `c > √5`, only finitely many
rational numbers `r` satisfy `|φ - r| < 1 / (c * r.den ^ 2)`. -/
theorem finite_setOf_abs_goldenRatio_sub_lt_of_sqrt_five_lt {c : ℝ} (hc : √5 < c) :
    {r : ℚ | |φ - r| < 1 / (c * (r.den : ℝ) ^ 2)}.Finite := by
  have h5 : (1 : ℝ) < √5 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hc0 : 0 < c := by linarith
  have hcc : 0 < c * (c - √5) := mul_pos hc0 (sub_pos.mpr hc)
  let N : ℕ := ⌊1 / (c * (c - √5))⌋₊
  refine ((Finset.Icc (-(3 * N : ℤ)) (3 * N) ×ˢ Finset.Icc 1 N).image
    fun x : ℤ × ℕ ↦ (x.1 : ℚ) / x.2).finite_toSet.subset fun r hr ↦ ?_
  have hd : (1 : ℝ) ≤ r.den := mod_cast r.den_pos
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = r.den * φ - r.num := ⟨_, rfl⟩
  -- the hypothesis bounds `x = q * φ - p`
  have hxlt : |x| * (c * r.den) < 1 := by
    have hrx : φ - r = x / r.den := by
      rw [hx, Rat.cast_def]
      field_simp
    have hr' : |x| / r.den < 1 / (c * (r.den : ℝ) ^ 2) := by
      rwa [Set.mem_ofPred_eq, hrx, abs_div, abs_of_pos (by linarith : (0 : ℝ) < r.den)] at hr
    rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hr'
    nlinarith
  -- hence the denominator is bounded
  have hden : (r.den : ℝ) ^ 2 * (c * (c - √5)) < 1 :=
    sq_mul_lt_one_of_abs_mul_goldenRatio_sub_mul_lt hc0.le r.num r.den (by rwa [← hx])
  have hdN : r.den ≤ N := by
    refine Nat.le_floor ?_
    rw [le_div_iff₀ hcc]
    nlinarith
  -- and so is the numerator
  have hnum : |(r.num : ℝ)| ≤ 3 * r.den := by
    have hcd : 1 ≤ c * r.den := by nlinarith
    have hx1 : |x| ≤ 1 := by
      linarith [mul_le_mul_of_nonneg_left hcd (abs_nonneg x)]
    have hp : (r.num : ℝ) = r.den * φ - x := by rw [hx]; ring
    rw [hp, abs_le]
    constructor <;> nlinarith [abs_le.mp hx1, goldenRatio_lt_two, goldenRatio_pos]
  have hnum' : |r.num| ≤ 3 * (N : ℤ) := by
    have : |r.num| ≤ 3 * (r.den : ℤ) := by exact_mod_cast hnum
    omega
  rw [Finset.coe_image, Set.mem_image]
  refine ⟨(r.num, r.den), ?_, Rat.num_div_den r⟩
  simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
  exact ⟨abs_le.mp hnum', r.den_pos, hdN⟩

end TauCeti
