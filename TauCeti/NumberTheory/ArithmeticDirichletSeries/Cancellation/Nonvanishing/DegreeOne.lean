/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation.Nonvanishing
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Landau

/-!
# Degree-one boundary nonvanishing for norm-twisted-square weights

When a unitary ideal weight `χ` has `(χ ^ 2).val.IsNormTwistOnGood u` (its pointwise square is a
purely imaginary norm twist `I ↦ N(I) ^ (u * I)` on its good ideals), the `3-4-1` criterion
already gives `continuedLFunctionOfWeight χ s ≠ 0` on `Re s ≥ 1` away from `s = 1 + (u / 2) * I`.

When `Module.finrank ℚ K = 1` and `HasCancellation χ`, `continuedLFunctionOfWeight χ` continues
holomorphically to `Re s > 0`, and `TauCeti.exists_differentiableOn_eq_dedekindZeta` continues
`ζ_K` holomorphically to `{z | 0 < z.re} \ {1}`. Landau's theorem
(`TauCeti.MultiplicativeIdealWeight.ne_zero_of_one_le_re_of_finrank_eq_one`) therefore closes the
exceptional point `s = 1 + (u / 2) * I` without any separate analytic continuation hypothesis.
Specializing to `u = 0` covers the quadratic case `(χ ^ 2).val.IsTrivialOnGood` away from and at
`s = 1`.

Both main theorems require `HasCancellation χ` only on the boundary `s.re = 1` and
`Module.finrank ℚ K = 1` only at the exceptional point (`s = 1 + (u / 2) * I`, or `s = 1` in the
trivial-square case `u = 0`).

## Main results

* `TauCeti.continuedLFunctionOfWeight_ne_zero_of_isNormTwistOnGood_sq_of_finrank_eq_one`: full
  `Re s ≥ 1` nonvanishing when `(χ ^ 2).val.IsNormTwistOnGood u`, requiring `HasCancellation χ` on
  `s.re = 1` and `[K : ℚ] = 1` at the exceptional point `s = 1 + (u / 2) * I`.
* `TauCeti.continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq_of_finrank_eq_one`: the
  `u = 0` specialization when `(χ ^ 2).val.IsTrivialOnGood`, requiring `HasCancellation χ` on
  `s.re = 1` and `[K : ℚ] = 1` at `s = 1`.

## References

* E. Landau, *Über die zu einem algebraischen Zahlkörper gehörige Zetafunction und die Ausdehnung
  der Tschebyschefschen Primzahlentheorie auf das Problem der Vertheilung der Primideale*,
  J. Reine Angew. Math. 125 (1903), 64–188.
* H. Davenport, *Multiplicative Number Theory*, Chapter 4.
-/

public section

namespace TauCeti

open Complex NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Nonvanishing of `continuedLFunctionOfWeight` on `Re s ≥ 1` when `(χ ^ 2).val` is a purely
imaginary norm twist on its good ideals, discharging the exceptional point in degree `1`.**
Requires `HasCancellation χ` on `s.re = 1` and `Module.finrank ℚ K = 1` at
`s = 1 + (u / 2) * I`, where `HasCancellation χ` continues `continuedLFunctionOfWeight χ` to
`Re z > 0` so Landau's theorem closes the exceptional point without a separate continuation
assumption. -/
theorem continuedLFunctionOfWeight_ne_zero_of_isNormTwistOnGood_sq_of_finrank_eq_one
    {χ : UnitaryIdealWeight K} {u : ℝ} (hχ₂ : (χ ^ 2).val.IsNormTwistOnGood u) {s : ℂ}
    (hs : 1 ≤ s.re) (hχ : s.re = 1 → HasCancellation χ)
    (hK : s = 1 + (u : ℂ) / 2 * I → Module.finrank ℚ K = 1) :
    continuedLFunctionOfWeight χ s ≠ 0 := by
  rcases hs.lt_or_eq with hsgt | hseq
  · exact continuedLFunctionOfWeight_ne_zero_of_one_lt_re χ hsgt
  · have hcanc := hχ hseq.symm
    have hdiff : DifferentiableOn ℂ (continuedLFunctionOfWeight χ)
        {z | 1 - 1 / (Module.finrank ℚ K : ℝ) < z.re} :=
      differentiableOn_continuedLFunctionOfWeight hcanc
    have hopen : IsOpen {z : ℂ | (0 : ℝ) < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact MultiplicativeIdealWeight.ne_zero_of_one_le_re_of_finrank_eq_one hχ₂
      (fun z hz ↦ by
        rw [continuedLFunctionOfWeight_eq_LSeries χ hz,
          UnitaryIdealWeight.toIdealArithmeticFunction_eq_val])
      hs
      (fun _ _ ↦ differentiableAt_continuedLFunctionOfWeight hcanc hs)
      (fun hsu ↦
        have hdiff0 : DifferentiableOn ℂ (continuedLFunctionOfWeight χ) {z | (0 : ℝ) < z.re} := by
          simpa [hK hsu] using hdiff
        ⟨hdiff0.mono fun _ hz ↦ lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hz,
          (hdiff0.differentiableAt (hopen.mem_nhds (by norm_num))).continuousAt⟩)
      hK

/-- **Nonvanishing of `continuedLFunctionOfWeight` on `Re s ≥ 1` when `(χ ^ 2).val.IsTrivialOnGood`
(the `u = 0` case), discharging `s = 1` in degree `1`.** Requires `HasCancellation χ` on `s.re = 1`
and `Module.finrank ℚ K = 1` at `s = 1`. -/
theorem continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq_of_finrank_eq_one
    {χ : UnitaryIdealWeight K} (hχ₂ : (χ ^ 2).val.IsTrivialOnGood) {s : ℂ}
    (hs : 1 ≤ s.re) (hχ : s.re = 1 → HasCancellation χ)
    (hK : s = 1 → Module.finrank ℚ K = 1) :
    continuedLFunctionOfWeight χ s ≠ 0 :=
  continuedLFunctionOfWeight_ne_zero_of_isNormTwistOnGood_sq_of_finrank_eq_one
    ((MultiplicativeIdealWeight.isNormTwistOnGood_zero_iff _).mpr hχ₂) hs hχ (by simpa using hK)

end TauCeti
