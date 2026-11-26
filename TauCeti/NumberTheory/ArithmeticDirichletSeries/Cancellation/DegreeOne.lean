/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation
import TauCeti.Analysis.Asymptotics.Sum.Periodic

/-!
# Norm-twist cancellation for periodic weights in degree one

`TauCeti.HasCancellation.normTwist` proves that cancellation survives an imaginary norm twist
`N(I) ^ (-z)` (`Re z = 0`) whenever `1 < Module.finrank ℚ K`, where the cancellation exponent
`1 - 1 / [K : ℚ]` is strictly positive. In degree `[K : ℚ] = 1` that exponent is `0`: arbitrary
`O(1)` partial sums only yield `O(log x)` after twisting by `n ^ (-i t)`, so an imaginary norm
twist does not preserve `O(1)` partial sums without additional structure.

When the weight `χ` is periodic of period `N ≠ 0` on the principal ideals `(k : 𝓞 K)` for `k ≥ 1`
— as holds for every ray class character weight with `N = Ideal.absNorm 𝔪.finitePart` — degree one
identifies `normCoeff K χ.toIdealArithmeticFunction k` with `χ((k : 𝓞 K))`
(`TauCeti.UnitaryIdealWeight.normCoeff_toIdealArithmeticFunction_of_finrank_eq_one`). Boundedness of
the untwisted partial sums (`HasCancellation χ`) then forces the period sum `∑ k ∈ Icc 1 N, a k` to
vanish (`TauCeti.sum_Icc_eq_zero_of_periodic_of_isBigO_one`), and second-order summation by parts
(`TauCeti.exists_norm_sum_Icc_mul_natCast_cpow_neg_le`) bounds the twisted partial sums
uniformly by `O(1)`. Together with `HasCancellation.normTwist` in higher degree, this removes the
degree restriction altogether for periodic weights
(`TauCeti.HasCancellation.normTwist_of_periodic_span_natCast`).

## Main results

* `TauCeti.HasCancellation.sum_Icc_normCoeff_eq_zero_of_finrank_eq_one`: in degree one over `ℚ`,
  cancellation of a unitary weight that is `N`-periodic on `(k : 𝓞 K)` (`k ≥ 1`) forces its period
  sum `∑ k ∈ Icc 1 N, normCoeff K χ k` to vanish.
* `TauCeti.HasCancellation.normTwist_of_finrank_eq_one`: imaginary norm twists preserve
  `HasCancellation` in degree one for weights periodic on `(k : 𝓞 K)` (`k ≥ 1`, `N ≠ 0`).
* `TauCeti.HasCancellation.normTwist_of_periodic_span_natCast`: unconditional version across all
  number fields `K`.
-/

public section

namespace TauCeti

open Asymptotics Filter NumberField
open scoped NumberField

section DegreeOneTwist

variable {K : Type*} [Field K] [NumberField K]

/-- In degree one over `ℚ`, cancellation of a unitary weight that is `N`-periodic on `(k : 𝓞 K)`
for `k ≥ 1` forces its period sum `∑ k ∈ Icc 1 N, normCoeff K χ k` to vanish. -/
theorem HasCancellation.sum_Icc_normCoeff_eq_zero_of_finrank_eq_one {χ : UnitaryIdealWeight K}
    (hK : Module.finrank ℚ K = 1) (hχ : HasCancellation χ) {N : ℕ}
    (hper : ∀ k, 1 ≤ k →
      χ.val (Ideal.span {((k + N : ℕ) : 𝓞 K)}) = χ.val (Ideal.span {(k : 𝓞 K)})) :
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
      χ.val (Ideal.span {((k + N : ℕ) : 𝓞 K)}) = χ.val (Ideal.span {(k : 𝓞 K)}))
    (z : ℂ) (hz : z.re = 0) :
    HasCancellation (UnitaryIdealWeight.normTwist z hz χ) := by
  have hsum := hχ.sum_Icc_normCoeff_eq_zero_of_finrank_eq_one hK hper
  have hper_coeff : ∀ k, 1 ≤ k →
      normCoeff K χ.toIdealArithmeticFunction (k + N) =
        normCoeff K χ.toIdealArithmeticFunction k := fun k hk ↦ by
    rw [UnitaryIdealWeight.normCoeff_toIdealArithmeticFunction_of_finrank_eq_one hK,
      UnitaryIdealWeight.normCoeff_toIdealArithmeticFunction_of_finrank_eq_one hK, hper k hk]
  obtain ⟨C, hC⟩ := exists_norm_sum_Icc_mul_natCast_cpow_neg_le hN hper_coeff hsum
    (z := z) (by simp [hz])
  rw [hasCancellation_iff_isBigO]
  refine IsBigO.of_bound C ?_
  filter_upwards with x
  rw [hK, Nat.cast_one, div_one, sub_self, Real.rpow_zero, norm_one, mul_one,
    idealSummatory_eq_sum_Icc_normCoeff]
  simp_rw [UnitaryIdealWeight.normCoeff_normTwist z hz χ]
  exact hC ⌊x⌋₊

/-- **Imaginary norm twists preserve cancellation for periodic weights.** Over any number field `K`,
if `χ : UnitaryIdealWeight K` has cancellation and is periodic of period `N ≠ 0` on the principal
ideals `(k : 𝓞 K)` for `k ≥ 1`, then `UnitaryIdealWeight.normTwist z hz χ` has cancellation for
every `z : ℂ` with `z.re = 0`. -/
theorem HasCancellation.normTwist_of_periodic_span_natCast {χ : UnitaryIdealWeight K}
    (hχ : HasCancellation χ) {N : ℕ} (hN : N ≠ 0)
    (hper : ∀ k, 1 ≤ k →
      χ.val (Ideal.span {((k + N : ℕ) : 𝓞 K)}) = χ.val (Ideal.span {(k : 𝓞 K)}))
    (z : ℂ) (hz : z.re = 0) :
    HasCancellation (UnitaryIdealWeight.normTwist z hz χ) := by
  have hpos : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
  rcases hpos.eq_or_lt with hK | hK
  · exact hχ.normTwist_of_finrank_eq_one hK.symm hN hper z hz
  · exact hχ.normTwist z hz hK

end DegreeOneTwist

end TauCeti
