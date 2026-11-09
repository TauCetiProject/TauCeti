/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Cauchy–Schwarz inequality for real integrals

For square-integrable real functions `f` and `g`,

`(∫ f g)² ≤ (∫ f²) (∫ g²)`

(`TauCeti.sq_integral_mul_le_integral_sq_mul_integral_sq`). Mathlib states Hölder's inequality
for real integrals with real exponents and roots
(`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`); this is the squared form for `p = q = 2`,
without roots or sign conditions, as it is used in energy estimates.

As a consequence, integrals converge under an `L²` comparison: if `|Fₙ - G| ≤ kₙ |aₙ - b|` with
`∫ kₙ²` bounded and `aₙ → b` in `L²`, then `∫ Fₙ → ∫ G`
(`TauCeti.tendsto_integral_of_abs_sub_le_mul_abs_sub`). This is how nonlinear integral functionals
with locally Lipschitz integrands are shown to be continuous along `L²`-convergent sequences.
-/

public section

namespace TauCeti

open Filter MeasureTheory Topology

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

/-- **Convergence of integrals from an `L²` comparison.** If `|Fₙ - G| ≤ kₙ |aₙ - b|` pointwise,
with `∫ kₙ²` eventually bounded and `∫ (aₙ - b)² → 0`, then `∫ Fₙ → ∫ G`. -/
theorem tendsto_integral_of_abs_sub_le_mul_abs_sub {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {F : ℕ → α → ℝ} {G : α → ℝ} {k a : ℕ → α → ℝ} {b : α → ℝ} {M : ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hG : Integrable G μ) (hk : ∀ n, MemLp (k n) 2 μ)
    (ha : ∀ n, MemLp (a n) 2 μ) (hb : MemLp b 2 μ)
    (hkM : ∀ᶠ n in atTop, ∫ x, k n x ^ 2 ∂μ ≤ M)
    (hab : Tendsto (fun n ↦ ∫ x, (a n x - b x) ^ 2 ∂μ) atTop (𝓝 0))
    (hle : ∀ n x, |F n x - G x| ≤ k n x * |a n x - b x|) :
    Tendsto (fun n ↦ ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, G x ∂μ)) := by
  have hlim : Tendsto (fun n ↦ √(M * ∫ x, (a n x - b x) ^ 2 ∂μ)) atTop (𝓝 0) := by
    simpa using ((hab.const_mul M).sqrt)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) ?_ hlim
  filter_upwards [hkM] with n hn
  have hd : MemLp (fun x ↦ |a n x - b x|) 2 μ := ((ha n).sub hb).abs
  have hint : Integrable (fun x ↦ k n x * |a n x - b x|) μ := (hk n).integrable_mul hd
  have h1 : |(∫ x, F n x ∂μ) - ∫ x, G x ∂μ| ≤ ∫ x, k n x * |a n x - b x| ∂μ := by
    rw [← integral_sub (hF n) hG]
    exact (abs_integral_le_integral_abs).trans (integral_mono ((hF n).sub hG).abs hint (hle n))
  have h2 := sq_integral_mul_le_integral_sq_mul_integral_sq (hk n) hd
  simp only [sq_abs] at h2
  have hnn : 0 ≤ ∫ x, (a n x - b x) ^ 2 ∂μ := integral_nonneg fun x ↦ sq_nonneg _
  rw [Real.norm_eq_abs]
  refine Real.abs_le_sqrt ?_
  calc ((∫ x, F n x ∂μ) - ∫ x, G x ∂μ) ^ 2 = |(∫ x, F n x ∂μ) - ∫ x, G x ∂μ| ^ 2 :=
        (sq_abs _).symm
    _ ≤ (∫ x, k n x * |a n x - b x| ∂μ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ ≤ M * ∫ x, (a n x - b x) ^ 2 ∂μ := h2.trans (mul_le_mul_of_nonneg_right hn hnn)

end TauCeti
