/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Basic
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Upper

/-!
# The incomplete Gamma functions on the real line

The complex incomplete Gamma functions of `TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower`
and `TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Upper` restrict, at a real parameter and a
nonnegative real argument, to real-valued functions: the lower and regularized ones to Tau Ceti's
real `TauCeti.lowerIncompleteGamma` and `TauCeti.regularizedGamma`, the upper one to the real tail
integral `∫ₓ^∞ t^{a−1} e^{−t} dt`.

## Main results

* `Complex.lowerIncompleteGamma_ofReal`: `γ(s, x)` is the real `TauCeti.lowerIncompleteGamma s x`
  for `0 < s` and `0 ≤ x`;
* `Complex.regularizedGamma_ofReal`: `P(s, x)` is the real `TauCeti.regularizedGamma s x` for
  `0 < s` and `0 ≤ x`;
* `Complex.regularizedGamma_ofReal_im`: `P(a, x)` is real for every real `a` and `0 ≤ x`;
* `Complex.upperIncompleteGamma_ofReal_eq_ofReal_integral`,
  `Complex.upperIncompleteGamma_ofReal_im`: `Γ(a, x)` is the real integral
  `∫ₓ^∞ t^{a−1} e^{−t} dt` for every real `a` and `0 ≤ x`, hence real.

The reality of Tricomi's `γ*(a, x)` for real `a` and `x` is
`Complex.tricomiIncompleteGamma_ofReal_im`.

## References

* NIST Digital Library of Mathematical Functions, §8.2, <https://dlmf.nist.gov/8.2>.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), files
`DLMF/IncompleteGamma/Regularized.lean` and `DLMF/IncompleteGamma/RealIntegrals.lean`, and
restated on Tau Ceti's definitions.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Complex

/-- For `0 < s` and `0 ≤ x`, the complex lower incomplete Gamma function `γ(s, x)` is Tau Ceti's
real `TauCeti.lowerIncompleteGamma s x`. -/
theorem lowerIncompleteGamma_ofReal {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    lowerIncompleteGamma s x = (TauCeti.lowerIncompleteGamma s x : ℂ) := by
  rw [lowerIncompleteGamma_ofReal_eq_partialGamma s (by simpa using hs) hx,
    TauCeti.ofReal_lowerIncompleteGamma_eq_partialGamma hx]

/-- For `0 < s` and `0 ≤ x`, the complex regularized Gamma function `P(s, x)` is Tau Ceti's real
`TauCeti.regularizedGamma s x`. -/
theorem regularizedGamma_ofReal {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) :
    regularizedGamma s x = (TauCeti.regularizedGamma s x : ℂ) := by
  have hG : Gamma (s : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hs)
  have h := lowerIncompleteGamma_ofReal hs hx
  rw [lowerIncompleteGamma_def] at h
  rw [TauCeti.regularizedGamma_eq_div, ofReal_div, ← h, ← Gamma_ofReal, mul_div_cancel_left₀ _ hG]

/-- `P(a, x) = x^a γ*(a, x)` is real for every real `a` and `0 ≤ x`. -/
@[simp]
theorem regularizedGamma_ofReal_im (a : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (regularizedGamma a x).im = 0 := by
  rw [regularizedGamma_def, ← ofReal_cpow hx, ← ofReal_tricomiIncompleteGamma_ofReal_re,
    ← ofReal_mul, ofReal_im]

/-- For real `a` and `0 ≤ x`, `Γ(a, x)` is the real tail integral `∫ₓ^∞ t^{a−1} e^{−t} dt`. -/
theorem upperIncompleteGamma_ofReal_eq_ofReal_integral (a : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    upperIncompleteGamma a x = ((∫ t in Ioi x, t ^ (a - 1) * Real.exp (-t) : ℝ) : ℂ) := by
  rw [upperIncompleteGamma_ofReal, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [ofReal_mul, ofReal_cpow (hx.trans ht.le), ofReal_exp]
  push_cast
  rfl

/-- `Γ(a, x)` is real for every real `a` and `0 ≤ x`. -/
@[simp]
theorem upperIncompleteGamma_ofReal_im (a : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (upperIncompleteGamma a x).im = 0 := by
  rw [upperIncompleteGamma_ofReal_eq_ofReal_integral a hx, ofReal_im]

end Complex
