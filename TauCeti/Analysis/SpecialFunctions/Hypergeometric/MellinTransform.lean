/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.MellinTransform.Convolution

/-!
# The Mellin transform of Euler's integral on the negative real axis

On the negative real axis `z = -x`, `x > 0`, Euler's integral for the regularized Gauss function
(DLMF 15.6.1) is a Mellin convolution: with the Beta weight `w(t) = t^{b-1} (1 - t)^{c-b-1}` on
`(0, 1]`,

`E(a, b, c, -x) = (Γ(b) Γ(c - b))⁻¹ ∫₀^∞ w(t) (1 + x t)^{-a} dt`.

The Mellin transform of a convolution `∫₀^∞ f(t) h(x t) dt` is `𝓜f(1 - s) 𝓜h(s)`
(`TauCeti.hasMellin_integral_mul_comp_mul`, DLMF 2.5.3–2.5.4). Here `𝓜w(1 - s)` is the Beta
integral `B(b - s, c - b)` (`Complex.hasMellin_cpow_mul_one_sub_cpow_Ioc`) and `𝓜h(s)` is Euler's
Beta integral of the second kind `Γ(s) Γ(a - s) / Γ(a)` (`Complex.hasMellin_one_add_cpow_neg`,
DLMF 5.12.3), so for `0 < Re s < min(Re a, Re b)` and `Re b < Re c`

`∫₀^∞ x^{s-1} E(a, b, c, -x) dx = Γ(s) Γ(a - s) Γ(b - s) / (Γ(a) Γ(b) Γ(c - s))`,

with absolute convergence. Since Euler's integral represents the regularized Gauss function
`𝐅(a, b; c; z)` on the cut plane when `0 < Re b < Re c` (DLMF 15.6.1), and `-x` lies in that cut
plane for every `x > 0`, this is the Mellin transform of DLMF 15.14.1 in that parameter region.

## Main results

* `Complex.hasMellin_eulerIntegral_neg`: the Mellin transform of `x ↦ E(a, b, c, -x)` converges
  at `s` and equals `Γ(s) Γ(a - s) Γ(b - s) / (Γ(a) Γ(b) Γ(c - s))`.

## References

* NIST Digital Library of Mathematical Functions, equations 2.5.3, 5.12.3, 15.6.1 and 15.14.1.
-/

public section

open MeasureTheory Set

namespace Complex

/-- On the negative real axis Euler's integral is the Mellin convolution of the Beta weight on
`(0, 1]` with `u ↦ (1 + u)^{-a}`. -/
private lemma eulerIntegral_neg_ofReal_eq_integral (a b c : ℂ) (x : ℝ) :
    eulerIntegral a b c (-x) = (Gamma b * Gamma (c - b))⁻¹ *
      ∫ t in Ioi 0, (Ioc 0 1).indicator
        (fun t : ℝ ↦ (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) t *
          (1 + ((x * t : ℝ) : ℂ)) ^ (-a) := by
  have hmul (t : ℝ) : (Ioc 0 1).indicator
      (fun t : ℝ ↦ (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) t *
        (1 + ((x * t : ℝ) : ℂ)) ^ (-a) = (Ioc 0 1).indicator (fun t : ℝ ↦
          (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 + ((x * t : ℝ) : ℂ)) ^ (-a)) t :=
    (indicator_mul_left _ _ fun t : ℝ ↦ (1 + ((x * t : ℝ) : ℂ)) ^ (-a)).symm
  rw [eulerIntegral_def, intervalIntegral.integral_of_le zero_le_one]
  simp_rw [hmul]
  rw [setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.mpr (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0)]
  simp only [ofReal_mul, neg_mul, sub_neg_eq_add]

/-- **DLMF 15.14.1 for Euler's integral.** For `0 < Re s < min(Re a, Re b)` and `Re b < Re c`,
the Mellin transform of `x ↦ E(a, b, c, -x)` converges absolutely at `s` and

`∫₀^∞ x^{s-1} E(a, b, c, -x) dx = Γ(s) Γ(a - s) Γ(b - s) / (Γ(a) Γ(b) Γ(c - s))`. -/
theorem hasMellin_eulerIntegral_neg {a b c s : ℂ} (hs : 0 < s.re) (hsa : s.re < a.re)
    (hsb : s.re < b.re) (hbc : b.re < c.re) :
    HasMellin (fun x : ℝ ↦ eulerIntegral a b c (-x)) s
      (Gamma s * Gamma (a - s) * Gamma (b - s) / (Gamma a * Gamma b * Gamma (c - s))) := by
  have hbs : 0 < (b - s).re := by simpa using hsb
  have hcb : 0 < (c - b).re := by simpa using hbc
  have hcs : 0 < (c - s).re := by simpa using hsb.trans hbc
  have hw := hasMellin_cpow_mul_one_sub_cpow_Ioc (s := 1 - s) (a := b - 1) (b := c - b - 1)
    (by simpa using hsb) (by simpa using hbc)
  rw [show 1 - s + (b - 1) = b - s by ring, sub_add_cancel] at hw
  have hh := hasMellin_one_add_cpow_neg hs hsa
  have hconv := TauCeti.hasMellin_integral_mul_comp_mul hw.1 hh.1
  have h := hasMellin_const_smul hconv.1 (Gamma b * Gamma (c - b))⁻¹
  rw [hconv.2, hw.2, hh.2, betaIntegral_eq_Gamma_mul_div _ _ hbs hcb, sub_add_sub_cancel'] at h
  refine (TauCeti.hasMellin_congr fun x _ ↦ eulerIntegral_neg_ofReal_eq_integral a b c x).mpr ?_
  convert h using 1
  have := Gamma_ne_zero_of_re_pos (hs.trans hsa)
  have := Gamma_ne_zero_of_re_pos (hs.trans hsb)
  have := Gamma_ne_zero_of_re_pos hcb
  have := Gamma_ne_zero_of_re_pos hcs
  simp only [smul_eq_mul]
  field_simp

end Complex
