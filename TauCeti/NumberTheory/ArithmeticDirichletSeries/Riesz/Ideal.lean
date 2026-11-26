/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic

/-!
# First Riesz sums over ideals of a number field

For an ideal arithmetic function `b : IdealArithmeticFunction K` on the nonzero ideals of the ring
of integers `𝓞 K` of a number field `K`, the ideal first Riesz sum
`∑_{N(I) ≤ y} b(I) (y / N(I) - 1)` agrees with `TauCeti.rieszSum (TauCeti.normCoeff K b) y`.

## Main results

* `TauCeti.sum_idealsLE_mul_div_absNorm_sub_one_eq_rieszSum_normCoeff`: expresses the ideal
  Riesz sum as the sequence Riesz sum of the norm coefficients `TauCeti.normCoeff K b`.

## References

* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Chapter 5.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
-/

public section

open scoped nonZeroDivisors NumberField

namespace TauCeti

/-- **Ideal coefficients**: summing `b I * (y / N(I) - 1)` over nonzero integral ideals of `𝓞 K`
with `N(I) ≤ y` equals `TauCeti.rieszSum (TauCeti.normCoeff K b) y`. -/
theorem sum_idealsLE_mul_div_absNorm_sub_one_eq_rieszSum_normCoeff (K : Type*) [Field K]
    [NumberField K] (b : IdealArithmeticFunction K) (y : ℝ) :
    ∑ I ∈ idealsLE K y, b I * ((y : ℂ) / Ideal.absNorm (I : Ideal (𝓞 K)) - 1) =
      rieszSum (normCoeff K b) y := by
  rw [← idealSummatory_apply K, idealSummatory_eq_sum_Icc_normCoeff, rieszSum_def]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simpa using normCoeff_fun_mul_comp_absNorm K b (fun m : ℕ ↦ (y : ℂ) / m - 1) n

end TauCeti
