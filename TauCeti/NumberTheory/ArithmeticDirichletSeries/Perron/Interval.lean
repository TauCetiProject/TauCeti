/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The subtracted Perron kernel

The kernel for a finite interval is the difference of the two endpoint kernels. Subtracting
before dividing by the complex variable removes the pole at the origin. Its value there is the
logarithmic width of the interval, which is the weight of a zero at the origin when shifting
the Perron contour.

See Koukoulopoulos, *The Distribution of Prime Numbers*, Chapter 8, for the contour method
with a single endpoint; the difference here is taken before shifting the line of integration.
-/

public section

open Complex

namespace TauCeti

/-- The subtracted Perron kernel with lower endpoint `a` and upper endpoint `b`, filled in at
zero by differentiation. -/
noncomputable def perronIntervalKernel (a b : ℝ) : ℂ → ℂ :=
  dslope (fun s : ℂ ↦ (b : ℂ) ^ s - (a : ℂ) ^ s) 0

/-- Away from zero the kernel is the difference of the powers divided by the exponent. -/
theorem perronIntervalKernel_eq_div {a b : ℝ} {s : ℂ} (hs : s ≠ 0) :
    perronIntervalKernel a b s = ((b : ℂ) ^ s - (a : ℂ) ^ s) / s := by
  rw [perronIntervalKernel, dslope_of_ne _ hs, slope_def_field]
  simp

/-- At the origin the kernel is the difference of the logarithms of the endpoints. -/
@[simp] theorem perronIntervalKernel_zero {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    perronIntervalKernel a b 0 = Complex.log b - Complex.log a := by
  have h (x : ℝ) (hx : x ≠ 0) :
      HasDerivAt (fun s : ℂ ↦ (x : ℂ) ^ s) (Complex.log x) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_cpow (c := (x : ℂ))
      (Or.inl (ofReal_ne_zero.mpr hx))
  rw [perronIntervalKernel, dslope_same, ((h b hb).fun_sub (h a ha)).deriv]

/-- The subtracted kernel for nonzero endpoints is analytic also at the origin. -/
theorem analyticAt_perronIntervalKernel {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (s : ℂ) :
    AnalyticAt ℂ (perronIntervalKernel a b) s := by
  have h (x : ℝ) (hx : x ≠ 0) : AnalyticAt ℂ (fun z : ℂ ↦ (x : ℂ) ^ z) s :=
    (analyticAt_const.mul analyticAt_id).cexp.congr <|
      Filter.Eventually.of_forall fun z ↦ (cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx) z).symm
  exact ((h b hb).sub (h a ha)).dslope 0

/-- The kernel on a horizontal contour is bounded by the two endpoint powers divided by the
absolute height. -/
theorem norm_perronIntervalKernel_le_div_abs_im {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {s : ℂ} (hs : s.im ≠ 0) :
    ‖perronIntervalKernel a b s‖ ≤ (b ^ s.re + a ^ s.re) / |s.im| := by
  have hs₀ : s ≠ 0 := fun h ↦ hs (by simp [h])
  have hpow (x : ℝ) (hx : 0 ≤ x) : ‖(x : ℂ) ^ s‖ ≤ x ^ s.re := by
    rcases hx.eq_or_lt with h | h
    · simp [← h, zero_cpow hs₀, Real.rpow_nonneg]
    · exact (norm_cpow_eq_rpow_re_of_pos h s).le
  rw [perronIntervalKernel_eq_div hs₀, norm_div]
  have h := (norm_sub_le ((b : ℂ) ^ s) ((a : ℂ) ^ s)).trans (add_le_add (hpow b hb) (hpow a ha))
  gcongr
  exact abs_im_le_norm s

end TauCeti
