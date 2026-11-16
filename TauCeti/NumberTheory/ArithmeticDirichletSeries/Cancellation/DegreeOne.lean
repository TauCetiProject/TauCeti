/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation
import TauCeti.Algebra.BigOperators.Periodic
import TauCeti.NumberTheory.LSeries.Twist
import TauCeti.NumberTheory.NumberField.Ideal.DegreeOne

/-!
# Norm-twist cancellation for periodic weights in degree one

`TauCeti.HasCancellation.normTwist` proves that cancellation survives an imaginary norm twist
`N(I) ^ (-z)` (`Re z = 0`) whenever `1 < Module.finrank ℚ K`, where the cancellation exponent
`1 - 1 / [K : ℚ]` is strictly positive. In degree `[K : ℚ] = 1` that exponent is `0`: arbitrary
`O(1)` partial sums only yield `O(log x)` after twisting by `n ^ (-i t)`, so an imaginary norm
twist does not preserve `O(1)` partial sums without additional structure.

When the weight `χ` is periodic of period `N ≠ 0` on the principal ideals `(k : 𝓞 K)` for `k ≥ 1`
— as holds for every ray class character weight with `N = Ideal.absNorm 𝔪.finitePart` — degree one
identifies `normCoeff K χ.toIdealArithmeticFunction k` with `χ((k : 𝓞 K))`. Boundedness of the
untwisted partial sums (`HasCancellation χ`) then forces the period sum `∑ k ∈ Icc 1 N, a k` to
vanish, and second-order summation by parts
(`TauCeti.LSeries.exists_norm_sum_Icc_mul_natCast_cpow_neg_le`) bounds the twisted partial sums
uniformly by `O(1)`. Combining the degree-one argument with `HasCancellation.normTwist` in degree
greater than one removes the degree restriction altogether for periodic weights
(`TauCeti.HasCancellation.normTwist_of_periodic_span_natCast`).

## Main results

* `TauCeti.normFiber_of_finrank_eq_one` and `TauCeti.normCoeff_apply_of_finrank_eq_one`: in degree
  one over `ℚ`, the norm fibre at `n ≠ 0` is the singleton `{(n : 𝓞 K)}` and the `n`-th norm
  coefficient of `f` is `f.zeroExtend (Ideal.span {(n : 𝓞 K)})` for every `n : ℕ`.
* `TauCeti.sum_Icc_eq_zero_of_periodic_of_isBigO_one`: if `a` is `N`-periodic on `k ≥ 1` in a real
  normed space and its partial sums are `O(1)`, its period sum `∑ k ∈ Icc 1 N, a k` vanishes.
* `TauCeti.HasCancellation.normTwist_of_finrank_eq_one`: imaginary norm twists preserve
  `HasCancellation` in degree one for weights periodic on `(k : 𝓞 K)` (`k ≥ 1`, `N ≠ 0`).
* `TauCeti.HasCancellation.normTwist_of_periodic_span_natCast`: unconditional version across all
  number fields `K`.
-/

public section

namespace TauCeti

open Asymptotics Filter NumberField
open scoped nonZeroDivisors NumberField

section NormCoeffDegreeOne

variable {K : Type*} [Field K] [NumberField K]

/-- In degree one over `ℚ`, the absolute-norm fibre at `n ≠ 0` consists solely of the principal
ideal `(n : 𝓞 K)`. -/
theorem normFiber_of_finrank_eq_one (hK : Module.finrank ℚ K = 1) {n : ℕ} (hn : n ≠ 0) :
    normFiber K n =
      {⟨Ideal.span {(n : 𝓞 K)},
        mem_nonZeroDivisors_of_ne_zero
          (mt Ideal.span_singleton_eq_bot.mp (Nat.cast_ne_zero.mpr hn))⟩} := by
  ext I
  rw [mem_normFiber, Finset.mem_singleton, Subtype.ext_iff]
  dsimp only
  constructor
  · intro hI
    rw [← hI]
    exact (RingOfIntegers.ideal_span_absNorm_eq_self_of_finrank_eq_one hK _).symm
  · intro hI
    rw [hI]
    exact RingOfIntegers.absNorm_span_natCast_of_finrank_eq_one hK n

/-- **Norm coefficients in degree one.** When `Module.finrank ℚ K = 1`, the `n`-th norm coefficient
of `f` is `f.zeroExtend (Ideal.span {(n : 𝓞 K)})` for every `n : ℕ` (including `n = 0`, where both
sides are `0`). -/
theorem normCoeff_apply_of_finrank_eq_one (hK : Module.finrank ℚ K = 1)
    (f : IdealArithmeticFunction K) (n : ℕ) :
    normCoeff K f n = f.zeroExtend (Ideal.span {(n : 𝓞 K)}) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [normCoeff_eq_sum_normFiber, normFiber_of_finrank_eq_one hK hn, Finset.sum_singleton]
    exact (f.zeroExtend_coe ⟨Ideal.span {(n : 𝓞 K)}, _⟩).symm

/-- When `Module.finrank ℚ K = 1`, the `n`-th norm coefficient of a multiplicative ideal weight `χ`
is `χ (Ideal.span {(n : 𝓞 K)})` for every `n : ℕ`. -/
theorem MultiplicativeIdealWeight.normCoeff_toIdealArithmeticFunction_of_finrank_eq_one
    (hK : Module.finrank ℚ K = 1) (χ : MultiplicativeIdealWeight K) (n : ℕ) :
    normCoeff K χ.toIdealArithmeticFunction n = χ (Ideal.span {(n : 𝓞 K)}) := by
  rw [normCoeff_apply_of_finrank_eq_one hK, χ.zeroExtend_toIdealArithmeticFunction]

/-- When `Module.finrank ℚ K = 1`, the `n`-th norm coefficient of a unitary ideal weight `χ` is
`χ.1 (Ideal.span {(n : 𝓞 K)})` for every `n : ℕ`. -/
theorem UnitaryIdealWeight.normCoeff_toIdealArithmeticFunction_of_finrank_eq_one
    (hK : Module.finrank ℚ K = 1) (χ : UnitaryIdealWeight K) (n : ℕ) :
    normCoeff K χ.toIdealArithmeticFunction n = χ.1 (Ideal.span {(n : 𝓞 K)}) := by
  rw [normCoeff_apply_of_finrank_eq_one hK, χ.zeroExtend_toIdealArithmeticFunction]

end NormCoeffDegreeOne

section PeriodicZeroMean

/-- **Bounded partial sums of a periodic sequence force vanishing period sum.** If `a : ℕ → E` in a
real normed space satisfies `a (k + N) = a k` for all `k ≥ 1` and its partial sums are `O(1)`, then
`∑ k ∈ Icc 1 N, a k = 0`. -/
theorem sum_Icc_eq_zero_of_periodic_of_isBigO_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a : ℕ → E} {N : ℕ} (hper : ∀ k, 1 ≤ k → a (k + N) = a k)
    (hbdd : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, a k) =O[atTop] (1 : ℕ → ℝ)) :
    ∑ k ∈ Finset.Icc 1 N, a k = 0 := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp
  · by_contra hS
    have hSpos : 0 < ‖∑ k ∈ Finset.Icc 1 N, a k‖ := norm_pos_iff.mpr hS
    obtain ⟨c, hc⟩ := hbdd.bound
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hc
    let m : ℕ := max n₀ (⌊max c 0 / ‖∑ k ∈ Finset.Icc 1 N, a k‖⌋₊ + 1)
    have hmN : n₀ ≤ m * N :=
      (le_max_left _ _).trans (Nat.le_mul_of_pos_right m (Nat.pos_of_ne_zero hN))
    have hle := hn₀ (m * N) hmN
    rw [Finset.sum_Icc_mul_eq_nsmul_of_periodic hper m, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul,
      Real.norm_natCast, Pi.one_apply, norm_one, mul_one] at hle
    have hlt : max c 0 < (m : ℝ) * ‖∑ k ∈ Finset.Icc 1 N, a k‖ :=
      (div_lt_iff₀ hSpos).mp
        ((Nat.lt_floor_add_one _).trans_le (by exact_mod_cast le_max_right n₀ _))
    linarith [le_max_left c 0]

end PeriodicZeroMean

section DegreeOneTwist

variable {K : Type*} [Field K] [NumberField K]

/-- In degree one over `ℚ`, cancellation of a unitary weight that is `N`-periodic on `(k : 𝓞 K)`
for `k ≥ 1` forces its period sum `∑ k ∈ Icc 1 N, normCoeff K χ k` to vanish. -/
theorem HasCancellation.sum_Icc_normCoeff_eq_zero_of_finrank_eq_one {χ : UnitaryIdealWeight K}
    (hK : Module.finrank ℚ K = 1) (hχ : HasCancellation χ) {N : ℕ}
    (hper : ∀ k, 1 ≤ k →
      χ.1 (Ideal.span {((k + N : ℕ) : 𝓞 K)}) = χ.1 (Ideal.span {(k : 𝓞 K)})) :
    ∑ k ∈ Finset.Icc 1 N, normCoeff K χ.toIdealArithmeticFunction k = 0 := by
  have hbdd : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, normCoeff K χ.toIdealArithmeticFunction k)
      =O[atTop] (1 : ℕ → ℝ) := by
    refine hχ.isBigO_sum_normCoeff.trans (IsBigO.of_bound 1 ?_)
    filter_upwards with n
    simp [hK]
  refine sum_Icc_eq_zero_of_periodic_of_isBigO_one (fun k hk ↦ ?_) hbdd
  rw [UnitaryIdealWeight.normCoeff_toIdealArithmeticFunction_of_finrank_eq_one hK,
    UnitaryIdealWeight.normCoeff_toIdealArithmeticFunction_of_finrank_eq_one hK, hper k hk]

/-- **Imaginary norm twists preserve cancellation in degree one for periodic weights.** If
`Module.finrank ℚ K = 1`, `χ` has cancellation, and `χ` is periodic of period `N ≠ 0` on `(k : 𝓞 K)`
for `k ≥ 1`, then `UnitaryIdealWeight.normTwist z hz χ` has cancellation for every `z` with
`z.re = 0`. -/
theorem HasCancellation.normTwist_of_finrank_eq_one {χ : UnitaryIdealWeight K}
    (hK : Module.finrank ℚ K = 1) (hχ : HasCancellation χ) {N : ℕ} (hN : N ≠ 0)
    (hper : ∀ k, 1 ≤ k →
      χ.1 (Ideal.span {((k + N : ℕ) : 𝓞 K)}) = χ.1 (Ideal.span {(k : 𝓞 K)}))
    (z : ℂ) (hz : z.re = 0) :
    HasCancellation (UnitaryIdealWeight.normTwist z hz χ) := by
  have hsum := hχ.sum_Icc_normCoeff_eq_zero_of_finrank_eq_one hK hper
  have hper_coeff : ∀ k, 1 ≤ k →
      normCoeff K χ.toIdealArithmeticFunction (k + N) =
        normCoeff K χ.toIdealArithmeticFunction k := fun k hk ↦ by
    rw [UnitaryIdealWeight.normCoeff_toIdealArithmeticFunction_of_finrank_eq_one hK,
      UnitaryIdealWeight.normCoeff_toIdealArithmeticFunction_of_finrank_eq_one hK, hper k hk]
  obtain ⟨C, hC⟩ := LSeries.exists_norm_sum_Icc_mul_natCast_cpow_neg_le hN hper_coeff hsum
    (z := z) (by simp [hz])
  rw [hasCancellation_iff_isBigO]
  refine IsBigO.of_bound C ?_
  filter_upwards with x
  rw [hK, Nat.cast_one, div_one, sub_self, Real.rpow_zero, norm_one, mul_one,
    idealSummatory_eq_sum_Icc_normCoeff]
  simp_rw [UnitaryIdealWeight.normCoeff_normTwist z hz χ]
  exact hC ⌊x⌋₊

/-- **Imaginary norm twists preserve cancellation across all degrees for periodic weights.**
Combining `HasCancellation.normTwist_of_finrank_eq_one` when `[K : ℚ] = 1` with
`HasCancellation.normTwist` when `[K : ℚ] > 1` removes the degree restriction for any unitary
weight that is `N`-periodic (`N ≠ 0`) on `(k : 𝓞 K)` for `k ≥ 1`. -/
theorem HasCancellation.normTwist_of_periodic_span_natCast {χ : UnitaryIdealWeight K}
    (hχ : HasCancellation χ) {N : ℕ} (hN : N ≠ 0)
    (hper : ∀ k, 1 ≤ k →
      χ.1 (Ideal.span {((k + N : ℕ) : 𝓞 K)}) = χ.1 (Ideal.span {(k : 𝓞 K)}))
    (z : ℂ) (hz : z.re = 0) :
    HasCancellation (UnitaryIdealWeight.normTwist z hz χ) := by
  have hpos : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  rcases hpos.eq_or_lt with hK | hK
  · exact hχ.normTwist_of_finrank_eq_one hK.symm hN hper z hz
  · exact hχ.normTwist z hz hK

end DegreeOneTwist

end TauCeti
