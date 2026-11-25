/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The Cauchy–Schwarz inequality for real integrals

For square-integrable real functions `f` and `g`,

`(∫ f g)² ≤ (∫ f²) (∫ g²)`

(`TauCeti.sq_integral_mul_le_integral_sq_mul_integral_sq`). Mathlib states Hölder's inequality
for real integrals with real exponents and roots
(`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`); this is the squared form for `p = q = 2`,
without roots or sign conditions, as it is used in energy estimates.

Against the constant function `1` it gives the set-integral form
`(∫ x in S, f x ∂μ)² ≤ μ(S) ∫ x in S, f x² ∂μ` on a set of finite measure
(`TauCeti.sq_setIntegral_le_measureReal_mul_setIntegral_sq`), which needs only `f²`
to be integrable on `S`. For a measure of total mass at most `1`, such as a probability measure or
its restriction to an event, this becomes the first-moment bound `|∫ g dμ| ≤ √(∫ g² dμ)` for `g`
with `g²` integrable (`MeasureTheory.Integrable.abs_integral_le_sqrt_integral_sq`). Its
consequence for absolute moments is `∫ ‖f‖ᵏ dμ ≤ √(∫ ‖f‖²ᵏ dμ)` for `f` with `‖f‖²ᵏ` integrable
(`MeasureTheory.Integrable.integral_norm_pow_le_sqrt_integral_norm_pow_two_mul`).
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

/-- Cauchy--Schwarz for a real-valued set integral over a set of finite measure, in squared form.
Only `f²` needs to be integrable on `S`. -/
theorem sq_setIntegral_le_measureReal_mul_setIntegral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : Ω → ℝ) (S : Set Ω) (hS_top : μ S ≠ ⊤)
    (hf_sq : IntegrableOn (fun x => f x ^ 2) S μ) :
    (∫ x in S, f x ∂μ) ^ 2 ≤ μ.real S * ∫ x in S, f x ^ 2 ∂μ := by
  by_cases hf : AEStronglyMeasurable f (μ.restrict S)
  · have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hS_top
    have h := sq_integral_mul_le_integral_sq_mul_integral_sq
      ((memLp_two_iff_integrable_sq hf).2 hf_sq) (memLp_const (1 : ℝ))
    simpa [mul_comm] using h
  · rw [integral_non_aestronglyMeasurable hf]
    simpa using mul_nonneg measureReal_nonneg (integral_nonneg fun x => sq_nonneg (f x))

end TauCeti

namespace MeasureTheory.Integrable

/-- For a measure of total mass at most `1`, the absolute value of the mean of a real function with
integrable square is at most the square root of its second moment. -/
theorem abs_integral_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : Ω → ℝ} (hg : Integrable (fun x => g x ^ 2) μ) (hμ : μ Set.univ ≤ 1) :
    |∫ x, g x ∂μ| ≤ √(∫ x, g x ^ 2 ∂μ) := by
  apply Real.abs_le_sqrt
  have h := TauCeti.sq_setIntegral_le_measureReal_mul_setIntegral_sq g Set.univ
    (hμ.trans_lt ENNReal.one_lt_top).ne hg.integrableOn
  rw [Measure.restrict_univ] at h
  exact h.trans (mul_le_of_le_one_left (integral_nonneg fun x => sq_nonneg _)
    (ENNReal.toReal_le_of_le_ofReal zero_le_one (by rwa [ENNReal.ofReal_one])))

/-- For a measure of total mass at most `1`, the `k`-th absolute moment of a function is at most
the square root of its `2k`-th absolute moment, provided `‖f‖ ^ (2 * k)` is integrable. -/
theorem integral_norm_pow_le_sqrt_integral_norm_pow_two_mul {Ω E : Type*} [MeasurableSpace Ω]
    [Norm E] {μ : Measure Ω} {f : Ω → E} {k : ℕ}
    (hf : Integrable (fun x => ‖f x‖ ^ (2 * k)) μ) (hμ : μ Set.univ ≤ 1) :
    ∫ x, ‖f x‖ ^ k ∂μ ≤ √(∫ x, ‖f x‖ ^ (2 * k) ∂μ) := by
  simp only [pow_mul'] at hf ⊢
  exact le_of_abs_le (hf.abs_integral_le_sqrt_integral_sq hμ)

end MeasureTheory.Integrable
