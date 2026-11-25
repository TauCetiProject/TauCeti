/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Basic
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower

/-!
# The lower incomplete Gamma functions on the real line

For a positive real parameter and a nonnegative real argument, the complex lower and regularized
incomplete Gamma functions of `TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower` agree with
Tau Ceti's real `TauCeti.lowerIncompleteGamma` and `TauCeti.regularizedGamma`.

## Main results

* `Complex.lowerIncompleteGamma_ofReal`: `γ(s, x)` is the real `TauCeti.lowerIncompleteGamma s x`
  for `0 < s` and `0 ≤ x`;
* `Complex.regularizedGamma_ofReal`: `P(s, x)` is the real `TauCeti.regularizedGamma s x` for
  `0 < s` and `0 ≤ x`.

For every real parameter and nonnegative argument, `P` and the upper function are real:
`Complex.regularizedGamma_ofReal_im` in `TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower`,
and `Complex.upperIncompleteGamma_ofReal_im`, with the real tail integral
`Complex.upperIncompleteGamma_ofReal_eq_ofReal_integral`, in
`TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Upper`. The reality of Tricomi's `γ*(a, x)` for
real `a` and `x` is `Complex.tricomiIncompleteGamma_ofReal_im`.

## References

* NIST Digital Library of Mathematical Functions, §8.2, <https://dlmf.nist.gov/8.2>.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), file
`DLMF/IncompleteGamma/Regularized.lean`, and restated on Tau Ceti's definitions.
-/

public section

noncomputable section

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

end Complex
