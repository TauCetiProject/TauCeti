/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.Analysis.Contour.Residue.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Perron.Interval
import TauCeti.Analysis.Contour.Argument.Rectangle.Weighted
import TauCeti.Analysis.Contour.Residue.LogDeriv
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Dirichlet.Origin

/-!
# The finite contour shift for a subtracted Dirichlet Perron integral

Subtract the two Perron kernels before moving the contour. The resulting entire weight gives
one contribution per enclosed L-function zero, with no additional pole from the kernel. For a
primitive nonprincipal character the origin contributes minus the logarithmic width if the
character is even, and zero if it is odd.

The contour setup follows Koukoulopoulos, *The Distribution of Prime Numbers*, Chapter 8,
with endpoint subtraction as in the half-interval explicit formula.
-/

public section

open Complex Set TauCeti TauCeti.Contour
open scoped Real Interval

namespace DirichletCharacter

/-- The exact finite-height shift of the Perron integral for the interval with endpoints `a,b`.
The rectangle has real coordinates `l,c` and ordinates `u,v`. In addition to the three other
edges, the integral on the right picks up minus `2π` times the kernel-weighted zero sum. There
is no pole term for a nonprincipal character and no singularity of the kernel at zero. -/
theorem intervalIntegral_perronIntervalKernel_eq {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {a b l c u v : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hlc : l ≤ c) (huv : u ≤ v)
    (hzeros : ∀ z ∈ Icc l c ×ℂ Icc u v, χ.LFunction z = 0 → z ∈ Ioo l c ×ℂ Ioo u v) :
    (∫ y : ℝ in u..v, -logDeriv χ.LFunction (c + y * I) * perronIntervalKernel a b (c + y * I)) =
      (∫ y : ℝ in u..v, -logDeriv χ.LFunction (l + y * I) * perronIntervalKernel a b (l + y * I)) +
      ((∫ x : ℝ in l..c, -logDeriv χ.LFunction (x + v * I) * perronIntervalKernel a b (x + v * I)) -
       (∫ x : ℝ in l..c,
          -logDeriv χ.LFunction (x + u * I) * perronIntervalKernel a b (x + u * I))) / I -
      2 * π * ∑ᶠ z ∈ {z ∈ Icc l c ×ℂ Icc u v | χ.LFunction z = 0},
          (analyticOrderNatAt χ.LFunction z : ℂ) * perronIntervalKernel a b z := by
  have hf : AnalyticOnNhd ℂ χ.LFunction (Icc l c ×ℂ Icc u v) := fun z _ ↦
    (differentiable_LFunction hχ).analyticAt z
  have hg : AnalyticOnNhd ℂ (perronIntervalKernel a b) (Icc l c ×ℂ Icc u v) :=
    fun s _ ↦ analyticAt_perronIntervalKernel ha hb s
  have h := intervalIntegral_vertical_logDeriv_mul_eq hlc huv hf hg hzeros
  simp only [neg_mul, intervalIntegral.integral_neg]
  rw [h]
  ring

open scoped Classical in
/-- The origin residue for the half-interval Perron integral. An even primitive nonprincipal
character contributes `-log 2`, and an odd one contributes zero. -/
theorem residue_logDeriv_mul_perronIntervalKernel_half_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hne : χ ≠ 1) {b : ℝ} (hb : 0 < b) :
    residue (fun s ↦ -logDeriv χ.LFunction s * perronIntervalKernel (b / 2) b s) 0 =
      if χ.Even then -(Real.log 2 : ℂ) else 0 := by
  have ha : 0 < b / 2 := by positivity
  have hg := analyticAt_perronIntervalKernel ha.ne' hb.ne' 0
  have hK : perronIntervalKernel (b / 2) b 0 = (Real.log 2 : ℂ) := by
    rw [perronIntervalKernel_zero ha.ne' hb.ne', ← ofReal_log hb.le, ← ofReal_log ha.le,
      ← ofReal_sub, Real.log_div hb.ne' (by norm_num), sub_sub_cancel]
  have horder := χ.meromorphicOrderAt_LFunction_zero hχ hne
  have hres (n : ℤ) (hn : meromorphicOrderAt χ.LFunction 0 = n) :=
    residue_logDeriv_mul_eq_meromorphicOrderAt (χ.meromorphic_LFunction 0) hn hg.neg
  by_cases he : χ.Even
  · rw [ite_eq_left he] at horder
    simpa only [Pi.neg_apply, neg_mul, mul_neg, Int.cast_one, hK, one_mul, ite_eq_left he]
      using hres 1 horder
  · rw [ite_eq_right he] at horder
    simpa only [Pi.neg_apply, neg_mul, mul_neg, Int.cast_zero, zero_mul, neg_zero, ite_eq_right he]
      using hres 0 horder

end DirichletCharacter
