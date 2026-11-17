/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The Cauchy–Schwarz inequality for real integrals

For square-integrable real functions `f` and `g`,

`(∫ f g)² ≤ (∫ f²) (∫ g²)`

(`TauCeti.sq_integral_mul_le_integral_sq_mul_integral_sq`). Mathlib states Hölder's inequality
for real integrals with real exponents and roots
(`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`); this is the squared form for `p = q = 2`,
without roots or sign conditions, as it is used in energy estimates.

Also provides the square-root form
`TauCeti.abs_integral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq` and the finite-measure set
integral bound `TauCeti.abs_setIntegral_le_sqrt_integral_sq_mul_sqrt_measureReal`.
-/

public section

namespace TauCeti

open MeasureTheory

/-- **The Cauchy–Schwarz inequality** `(∫ f g)² ≤ (∫ f²) (∫ g²)` for square-integrable real
functions. -/
theorem sq_integral_mul_le_integral_sq_mul_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun x ↦ abs_nonneg (f x))
    (Filter.Eventually.of_forall fun x ↦ abs_nonneg (g x))
    (by simpa [Real.norm_eq_abs] using hf.norm) (by simpa [Real.norm_eq_abs] using hg.norm)
  have hF : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x ↦ sq_nonneg _
  have hG : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x ↦ sq_nonneg _
  simp only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] at h
  calc (∫ x, f x * g x ∂μ) ^ 2 = |∫ x, f x * g x ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ x, |f x| * |g x| ∂μ) ^ 2 := by
        gcongr
        calc |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := abs_integral_le_integral_abs
          _ = ∫ x, |f x| * |g x| ∂μ := by simp_rw [abs_mul]
    _ ≤ (√(∫ x, f x ^ 2 ∂μ) * √(∫ x, g x ^ 2 ∂μ)) ^ 2 :=
        pow_le_pow_left₀ (integral_nonneg fun x ↦ by positivity) h 2
    _ = (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
        rw [mul_pow, Real.sq_sqrt hF, Real.sq_sqrt hG]

/-- **The Cauchy–Schwarz inequality in square-root form:** `|∫ f g| ≤ √(∫ f²) * √(∫ g²)`. -/
theorem abs_integral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ √(∫ x, f x ^ 2 ∂μ) * √(∫ x, g x ^ 2 ∂μ) := by
  rw [← Real.sqrt_mul (integral_nonneg fun x ↦ sq_nonneg (f x))]
  exact Real.le_sqrt_of_sq_le
    (by rw [sq_abs]; exact sq_integral_mul_le_integral_sq_mul_integral_sq hf hg)

/-- **Cauchy–Schwarz bound for a set integral:** `|∫ x in s, f x ∂μ| ≤ √(∫ f²) * √(μ.real s)`. -/
theorem abs_setIntegral_le_sqrt_integral_sq_mul_sqrt_measureReal {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} {s : Set α} (hf : MemLp f 2 μ) (hs : μ s ≠ ⊤) :
    |∫ x in s, f x ∂μ| ≤ √(∫ x, f x ^ 2 ∂μ) * √(μ.real s) := by
  have : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hs.lt_top⟩
  have h := abs_integral_mul_le_sqrt_integral_sq_mul_sqrt_integral_sq (hf.restrict s)
    (memLp_const (1 : ℝ))
  simp only [mul_one, one_pow, integral_const, smul_eq_mul, Measure.real,
    Measure.restrict_apply_univ] at h ⊢
  exact h.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt
    (setIntegral_le_integral hf.integrable_sq (.of_forall fun _ ↦ sq_nonneg _)))
    (Real.sqrt_nonneg _))

end TauCeti
