/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Perron.Formula

/-!
# The Perron formula for sums over ideals

Let `f` be an arithmetic function on the nonzero ideals of the ring of integers of a number field
`K`, and let the `L`-series of its norm coefficients `TauCeti.normCoeff K f` converge absolutely on
the line `Re s = c > 0`.  This file reads the arithmetic Perron formula of
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Perron/Formula.lean` as a statement about the
ideal sums `∑_{N(I) ≤ x} f(I)` themselves.

The sharp step `TauCeti.perronStep` gives an ideal `I` with `N(I) ≤ x` the weight `1` when
`N(I) < x` and the weight `1 / 2` when `N(I) = x`, so the limit of the truncated Perron integral
is the finite ideal sum `∑_{N(I) ≤ x} f(I) perronStep (x / N(I))`
(`TauCeti.tsum_normCoeff_mul_perronStep`).  It is the inclusive summatory function
`TauCeti.idealSummatory K f x` exactly when `x` is not the norm of a nonzero ideal, and at an
integer endpoint `x = N` every ideal of norm `N` enters with half weight, so that the limit is
`∑_{N(I) ≤ N} f(I) - normCoeff K f N / 2`.

Only norm endpoints matter.  An integer `x` that is not the norm of any nonzero ideal behaves like
a non-integer, because the norm coefficient of `f` vanishes there; this is why the off-norm
statements exclude exactly the norms of nonzero ideals rather than all natural numbers.

## Main results

* `TauCeti.perronFormula`: the truncated Perron integral of the `L`-series of the norm
  coefficients tends to the step-weighted ideal sum `∑_{N(I) ≤ x} f(I) perronStep (x / N(I))`.
* `TauCeti.perronFormula_of_forall_absNorm_ne`: off the norms the limit is
  `TauCeti.idealSummatory K f x`.
* `TauCeti.perronFormula_natCast`: at an integer endpoint `N` the limit is
  `TauCeti.idealSummatory K f N - normCoeff K f N / 2`, the ideals of norm `N` entering with half
  weight.
* `TauCeti.norm_truncatedPerron_LSeries_normCoeff_sub_idealSummatory_le`: off the norms, the
  truncated integral at finite height differs from `TauCeti.idealSummatory K f x` by at most the
  series of the smoothed-step kernel errors.

## References

* H. Davenport, *Multiplicative Number Theory*, chapter 17.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

public section

namespace TauCeti

open Filter Topology
open scoped Real nonZeroDivisors NumberField

variable {K : Type*} [Field K] [NumberField K] {f : IdealArithmeticFunction K} {x c T : ℝ}

/-- **The Perron step series of the norm coefficients is a finite ideal sum.**  Every index above
`x` has step weight `0`, and the norm fibre at each index below it redistributes the weight over
the ideals of that norm. -/
theorem tsum_normCoeff_mul_perronStep (f : IdealArithmeticFunction K) (x : ℝ) :
    ∑' n : ℕ, normCoeff K f n * perronStep (x / n) =
      ∑ I ∈ idealsLE K x, f I * perronStep (x / Ideal.absNorm (I : Ideal (𝓞 K))) := by
  have hzero : ∀ n ∉ Finset.range (⌊x⌋₊ + 1), normCoeff K f n * perronStep (x / n) = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    have hlt : ⌊x⌋₊ < n := hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.zero_lt_of_lt hlt)
    rw [perronStep_of_lt_one ((div_lt_one hn0).2 (Nat.lt_of_floor_lt hlt)), mul_zero]
  rw [tsum_eq_sum hzero,
    ← idealSummatory_apply K (fun I ↦ f I * perronStep (x / Ideal.absNorm (I : Ideal (𝓞 K)))),
    idealSummatory_eq_sum_range_normFiber]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  rw [normCoeff_eq_sum_normFiber, Finset.sum_mul]
  refine Finset.sum_congr rfl fun I hI ↦ ?_
  rw [(mem_normFiber K).mp hI]

/-- **Off the norms the step weights are sharp.**  If `x` is not the absolute norm of any nonzero
ideal, every ideal counted up to `x` has norm strictly below `x`, and so step weight `1`. -/
theorem sum_idealsLE_mul_perronStep_of_forall_absNorm_ne
    (hoff : ∀ I : (Ideal (𝓞 K))⁰, (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≠ x)
    (f : IdealArithmeticFunction K) :
    ∑ I ∈ idealsLE K x, f I * perronStep (x / Ideal.absNorm (I : Ideal (𝓞 K))) =
      idealSummatory K f x := by
  rw [idealSummatory_apply]
  refine Finset.sum_congr rfl fun I hI ↦ ?_
  have hpos : (0 : ℝ) < Ideal.absNorm (I : Ideal (𝓞 K)) :=
    zero_lt_one.trans_le (one_le_absNorm_real_of_nonZeroDivisors I)
  have hlt : (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) < x :=
    lt_of_le_of_ne
      ((mem_normLE fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))).mp hI) (hoff I)
  rw [perronStep_of_one_lt ((one_lt_div hpos).2 hlt), mul_one]

/-- **The half weight at an integer endpoint.**  At `x = N` the ideals of norm `N` receive step
weight `1 / 2` and all others counted up to `N` receive `1`, so the step-weighted sum is the
inclusive ideal sum less half of the norm coefficient at `N`. -/
theorem sum_idealsLE_mul_perronStep_natCast (f : IdealArithmeticFunction K) (N : ℕ) :
    ∑ I ∈ idealsLE K N, f I * perronStep ((N : ℝ) / Ideal.absNorm (I : Ideal (𝓞 K))) =
      idealSummatory K f N - normCoeff K f N / 2 := by
  classical
  have hstep : ∀ I ∈ idealsLE K N,
      f I * perronStep ((N : ℝ) / Ideal.absNorm (I : Ideal (𝓞 K))) =
        f I - (if Ideal.absNorm (I : Ideal (𝓞 K)) = N then f I else 0) / 2 := by
    intro I hI
    have hle : Ideal.absNorm (I : Ideal (𝓞 K)) ≤ N :=
      (mem_normLE_natCast fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))).mp hI
    have hpos : (0 : ℝ) < Ideal.absNorm (I : Ideal (𝓞 K)) :=
      zero_lt_one.trans_le (one_le_absNorm_real_of_nonZeroDivisors I)
    split_ifs with hN
    · rw [hN, div_self (hN ▸ hpos.ne'), perronStep_one]
      ring
    · have hlt : (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) < N := by
        exact_mod_cast lt_of_le_of_ne hle hN
      rw [perronStep_of_one_lt ((one_lt_div hpos).2 hlt), mul_one, zero_div, sub_zero]
  have hfib : (idealsLE K N).filter (fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K)) = N) =
      normFiber K N := by
    ext I
    simp only [Finset.mem_filter, mem_normFiber, and_iff_right_iff_imp]
    exact fun hI ↦
      (mem_normLE_natCast fun I : (Ideal (𝓞 K))⁰ ↦ Ideal.absNorm (I : Ideal (𝓞 K))).mpr hI.le
  rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_filter,
    hfib, ← normCoeff_eq_sum_normFiber, ← idealSummatory_apply]

/-- **The arithmetic Perron formula for ideal sums.**  Where the `L`-series of the norm
coefficients of `f` converges absolutely on the line `Re s = c`, the truncated Perron integral
tends, as the height grows, to the ideal sum `∑_{N(I) ≤ x} f(I)` in which each ideal of norm
exactly `x` carries half weight.  The two readings of this limit are
`TauCeti.perronFormula_of_forall_absNorm_ne` and `TauCeti.perronFormula_natCast`. -/
theorem perronFormula (hx : 0 < x) (hc : 0 < c) (h : LSeriesSummable (normCoeff K f) c) :
    Tendsto (fun T : ℝ ↦ ((2 * π : ℝ) : ℂ)⁻¹ *
        ∫ t in -T..T, LSeries (normCoeff K f) ((c : ℂ) + t * Complex.I) * perronIntegrand x c t)
      atTop (𝓝 (∑ I ∈ idealsLE K x, f I * perronStep (x / Ideal.absNorm (I : Ideal (𝓞 K))))) := by
  rw [← tsum_normCoeff_mul_perronStep]
  exact tendsto_truncatedPerron_LSeries hx hc h

/-- **The Perron formula off the norms.**  If `x > 0` is not the absolute norm of a nonzero ideal,
the truncated Perron integral tends to the inclusive ideal sum `∑_{N(I) ≤ x} f(I)`. -/
theorem perronFormula_of_forall_absNorm_ne (hx : 0 < x) (hc : 0 < c)
    (hoff : ∀ I : (Ideal (𝓞 K))⁰, (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≠ x)
    (h : LSeriesSummable (normCoeff K f) c) :
    Tendsto (fun T : ℝ ↦ ((2 * π : ℝ) : ℂ)⁻¹ *
        ∫ t in -T..T, LSeries (normCoeff K f) ((c : ℂ) + t * Complex.I) * perronIntegrand x c t)
      atTop (𝓝 (idealSummatory K f x)) := by
  rw [← sum_idealsLE_mul_perronStep_of_forall_absNorm_ne hoff f]
  exact perronFormula hx hc h

/-- **The Perron formula at an integer endpoint.**  At `x = N` the truncated Perron integral tends
to the inclusive ideal sum `∑_{N(I) ≤ N} f(I)` less half of the norm coefficient at `N`: every
ideal of norm exactly `N` enters with half weight. -/
theorem perronFormula_natCast {N : ℕ} (hN : 0 < N) (hc : 0 < c)
    (h : LSeriesSummable (normCoeff K f) c) :
    Tendsto (fun T : ℝ ↦ ((2 * π : ℝ) : ℂ)⁻¹ *
        ∫ t in -T..T, LSeries (normCoeff K f) ((c : ℂ) + t * Complex.I) * perronIntegrand N c t)
      atTop (𝓝 (idealSummatory K f N - normCoeff K f N / 2)) := by
  rw [← sum_idealsLE_mul_perronStep_natCast]
  exact perronFormula (Nat.cast_pos.2 hN) hc h

/-- **The truncated Perron formula off the norms.**  If `x > 0` is not the absolute norm of a
nonzero ideal, then at every positive height `T` the truncated Perron integral differs from the
inclusive ideal sum `∑_{N(I) ≤ x} f(I)` by at most the series of the smoothed-step kernel errors at
the ratios `x / n`. -/
theorem norm_truncatedPerron_LSeries_normCoeff_sub_idealSummatory_le (hx : 0 < x) (hc : 0 < c)
    (hT : 0 < T)
    (hoff : ∀ I : (Ideal (𝓞 K))⁰, (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≠ x)
    (h : LSeriesSummable (normCoeff K f) c) :
    ‖(((2 * π : ℝ) : ℂ)⁻¹ *
        ∫ t in -T..T, LSeries (normCoeff K f) ((c : ℂ) + t * Complex.I) * perronIntegrand x c t)
        - idealSummatory K f x‖
      ≤ ∑' n : ℕ, ‖normCoeff K f n‖ * ((x / n) ^ c / (π * T * |Real.log (x / n)|)) := by
  -- A nonzero norm coefficient at `n` comes from an ideal of norm `n`, so `x ≠ n` there.
  have hoff' : ∀ n : ℕ, normCoeff K f n ≠ 0 → x ≠ n := by
    rintro n hn rfl
    obtain ⟨I, hI⟩ : (normFiber K n).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro h0
      rw [normCoeff_eq_sum_normFiber, h0, Finset.sum_empty] at hn
      exact hn rfl
    exact hoff I (by rw [(mem_normFiber K).mp hI])
  have hsum : ∑ n ∈ Finset.Ico 1 ⌈x⌉₊, normCoeff K f n = idealSummatory K f x := by
    rw [← tsum_mul_perronStep_div _ hoff', tsum_normCoeff_mul_perronStep,
      sum_idealsLE_mul_perronStep_of_forall_absNorm_ne hoff]
  rw [← hsum]
  exact norm_truncatedPerron_LSeries_sub_sum_le hx hc hT hoff' h

end TauCeti
