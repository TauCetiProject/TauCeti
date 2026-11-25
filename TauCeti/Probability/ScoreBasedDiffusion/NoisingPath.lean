/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Probability.DenoisingDiffusion.NoiseKernel

/-!
# Transition kernels of Gaussian noising paths

A *level* is a pair `(c, s)` of real numbers, a signal level and a noise level: at level `(c, s)`
data `X` with law `μ₀` are observed as `c • X + s • Z` with `Z` an independent standard Gaussian
vector, whose law is `μ₀.bind (gaussianKernel c (s ^ 2))`. A noising path in continuous time is a
level depending on time.

This file describes how the laws at two levels are related. For levels `(c₁, s₁)` and `(c₂, s₂)`
with `c₁ ≠ 0` and `(c₂ / c₁) ^ 2 * s₁ ^ 2 ≤ s₂ ^ 2`, the Gaussian kernel
`gaussianKernel (c₂ / c₁) (s₂ ^ 2 - (c₂ / c₁) ^ 2 * s₁ ^ 2)` carries the observation kernel at the
first level to the one at the second, and so carries the law at the first level to the law at
the second for every data law. These transition kernels satisfy the Chapman–Kolmogorov
equation. The condition on the two levels says that the noise-to-signal ratio `|s / c|` does not
decrease, so a path along which `c` does not vanish and `|s / c|` is nondecreasing has a transition
kernel from any time to any later time.

The main example is the variance-preserving path of a noise schedule `β`, with signal
level `vpSignal β t = exp (-(∫₀ᵗ β) / 2)` and noise level `vpNoise β t = √(1 - (vpSignal β t) ^ 2)`.
For a locally integrable nonnegative schedule and times `0 ≤ r ≤ t`, its transition kernel from
time `r` to time `t` is the variance-preserving noising kernel `noiseKernel (exp (-∫ᵣᵗ β))`; in
particular its law at time `t` is the law of the data noised with
the signal level `exp (-∫₀ᵗ β)`.

## Main definitions

* `TauCeti.Probability.vpSignal β t`: the signal level `exp (-(∫₀ᵗ β) / 2)` of the
  variance-preserving path.
* `TauCeti.Probability.vpNoise β t`: its noise level `√(1 - (vpSignal β t) ^ 2)`.

## Main results

* `TauCeti.Probability.gaussianKernel_div_comp_gaussianKernel`: the transition kernel between two
  levels carries the observation kernel at the first level to the one at the second.
* `TauCeti.Probability.bind_gaussianKernel_div`: the same statement for the laws of the data at
  the two levels.
* `TauCeti.Probability.gaussianKernel_div_comp_gaussianKernel_div`: the Chapman–Kolmogorov
  equation for three levels.
* `TauCeti.Probability.div_sq_mul_sq_le_sq_iff`: two levels admit a transition kernel exactly
  when the noise-to-signal ratio does not decrease.
* `TauCeti.Probability.gaussianKernel_vpSignal_vpNoise`: the observation kernel at time `t` of the
  variance-preserving path is `noiseKernel (exp (-∫₀ᵗ β))`.
* `TauCeti.Probability.gaussianKernel_vpSignal_div_eq_noiseKernel`: the two-level kernel from
  time `r` to time `t` is `noiseKernel (exp (-∫ᵣᵗ β))`; where `∫ᵣᵗ β ≥ 0` it is the transition
  kernel.

## References

* Y. Song, J. Sohl-Dickstein, D. P. Kingma, A. Kumar, S. Ermon and B. Poole, *Score-based
  generative modeling through stochastic differential equations*, ICLR 2021, Appendix B,
  equation (29).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Transition kernels between two levels -/

/-- The transition kernel between two levels. If `c₁ ≠ 0` and
`(c₂ / c₁) ^ 2 * s₁ ^ 2 ≤ s₂ ^ 2`, then observing at level `(c₁, s₁)` and then applying the kernel
`x ↦ N((c₂ / c₁) • x, s₂ ^ 2 - (c₂ / c₁) ^ 2 * s₁ ^ 2)` is observing at level `(c₂, s₂)`. -/
theorem gaussianKernel_div_comp_gaussianKernel {c₁ s₁ c₂ s₂ : ℝ} (hc₁ : c₁ ≠ 0)
    (h : (c₂ / c₁) ^ 2 * s₁ ^ 2 ≤ s₂ ^ 2) :
    gaussianKernel (ι := ι) (c₂ / c₁) (s₂ ^ 2 - (c₂ / c₁) ^ 2 * s₁ ^ 2) ∘ₖ
        gaussianKernel c₁ (s₁ ^ 2) =
      gaussianKernel c₂ (s₂ ^ 2) := by
  rw [gaussianKernel_comp (sq_nonneg s₁) (sub_nonneg.2 h), div_mul_cancel₀ c₂ hc₁,
    add_sub_cancel]

/-- The transition kernel between two levels carries the law of the data at the first level to
the law of the data at the second level, for every data law `μ₀`. -/
theorem bind_gaussianKernel_div (μ₀ : Measure (EuclideanSpace ℝ ι)) {c₁ s₁ c₂ s₂ : ℝ}
    (hc₁ : c₁ ≠ 0) (h : (c₂ / c₁) ^ 2 * s₁ ^ 2 ≤ s₂ ^ 2) :
    (μ₀.bind (gaussianKernel c₁ (s₁ ^ 2))).bind
        (gaussianKernel (c₂ / c₁) (s₂ ^ 2 - (c₂ / c₁) ^ 2 * s₁ ^ 2)) =
      μ₀.bind (gaussianKernel c₂ (s₂ ^ 2)) := by
  rw [← gaussianKernel_div_comp_gaussianKernel hc₁ h]
  exact Measure.comp_assoc

/-- **The Chapman–Kolmogorov equation for transition kernels between levels.** Passing from the
level `(c₁, s₁)` to `(c₂, s₂)` and then to `(c₃, s₃)` is passing from `(c₁, s₁)` to `(c₃, s₃)`.
The first signal level may vanish, in which case the first kernel and the composite forget their
input. -/
theorem gaussianKernel_div_comp_gaussianKernel_div {c₁ s₁ c₂ s₂ c₃ s₃ : ℝ} (hc₂ : c₂ ≠ 0)
    (h₁₂ : (c₂ / c₁) ^ 2 * s₁ ^ 2 ≤ s₂ ^ 2) (h₂₃ : (c₃ / c₂) ^ 2 * s₂ ^ 2 ≤ s₃ ^ 2) :
    gaussianKernel (ι := ι) (c₃ / c₂) (s₃ ^ 2 - (c₃ / c₂) ^ 2 * s₂ ^ 2) ∘ₖ
        gaussianKernel (c₂ / c₁) (s₂ ^ 2 - (c₂ / c₁) ^ 2 * s₁ ^ 2) =
      gaussianKernel (c₃ / c₁) (s₃ ^ 2 - (c₃ / c₁) ^ 2 * s₁ ^ 2) := by
  have hm : c₃ / c₂ * (c₂ / c₁) = c₃ / c₁ := by rw [mul_comm, div_mul_div_cancel₀' hc₂]
  rw [gaussianKernel_comp (sub_nonneg.2 h₁₂) (sub_nonneg.2 h₂₃), hm]
  congr 1
  rw [← hm]
  ring

/-- Two levels admit a transition kernel exactly when the noise-to-signal ratio does not
decrease: for `c₂ ≠ 0`, `(c₂ / c₁) ^ 2 * s₁ ^ 2 ≤ s₂ ^ 2` if and only if
`|s₁ / c₁| ≤ |s₂ / c₂|`. So a noising path along which `|s / c|` is nondecreasing and `c` does not
vanish has a transition kernel from any time to any later time, and these kernels compose by
`gaussianKernel_div_comp_gaussianKernel_div`. -/
theorem div_sq_mul_sq_le_sq_iff {c₁ s₁ c₂ s₂ : ℝ} (hc₂ : c₂ ≠ 0) :
    (c₂ / c₁) ^ 2 * s₁ ^ 2 ≤ s₂ ^ 2 ↔ |s₁ / c₁| ≤ |s₂ / c₂| := by
  have h₁ : (c₂ / c₁) ^ 2 * s₁ ^ 2 = c₂ ^ 2 * (s₁ / c₁) ^ 2 := by ring
  have h₂ : s₂ ^ 2 = c₂ ^ 2 * (s₂ / c₂) ^ 2 := by field_simp
  rw [h₁, h₂, mul_le_mul_iff_right₀ (by positivity), sq_le_sq]

/-! ### The variance-preserving path -/

/-- The signal level `exp (-(∫₀ᵗ β) / 2)` of the variance-preserving noising path with noise
schedule `β`. -/
def vpSignal (β : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(∫ u in (0 : ℝ)..t, β u) / 2)

/-- The noise level `√(1 - (vpSignal β t) ^ 2)` of the variance-preserving noising path with noise
schedule `β`. -/
def vpNoise (β : ℝ → ℝ) (t : ℝ) : ℝ :=
  √(1 - vpSignal β t ^ 2)

variable {β : ℝ → ℝ} {r t : ℝ}

/-- The defining formula of `vpSignal`. -/
theorem vpSignal_def (β : ℝ → ℝ) (t : ℝ) :
    vpSignal β t = Real.exp (-(∫ u in (0 : ℝ)..t, β u) / 2) :=
  (rfl)

/-- The defining formula of `vpNoise`. -/
theorem vpNoise_def (β : ℝ → ℝ) (t : ℝ) : vpNoise β t = √(1 - vpSignal β t ^ 2) :=
  (rfl)

theorem vpSignal_pos (β : ℝ → ℝ) (t : ℝ) : 0 < vpSignal β t :=
  Real.exp_pos _

theorem vpNoise_nonneg (β : ℝ → ℝ) (t : ℝ) : 0 ≤ vpNoise β t :=
  Real.sqrt_nonneg _

@[simp]
theorem vpSignal_zero (β : ℝ → ℝ) : vpSignal β 0 = 1 := by
  simp [vpSignal]

@[simp]
theorem vpNoise_zero (β : ℝ → ℝ) : vpNoise β 0 = 0 := by
  simp [vpNoise]

/-- The square of the signal level is `exp (-∫₀ᵗ β)`. -/
theorem vpSignal_sq (β : ℝ → ℝ) (t : ℝ) :
    vpSignal β t ^ 2 = Real.exp (-∫ u in (0 : ℝ)..t, β u) := by
  rw [vpSignal, ← Real.exp_natCast_mul]
  congr 1
  ring

/-- Where `∫₀ᵗ β ≥ 0`, the signal level of the variance-preserving path is at most `1`. -/
theorem vpSignal_le_one (h : 0 ≤ ∫ u in (0 : ℝ)..t, β u) : vpSignal β t ≤ 1 :=
  Real.exp_le_one_iff.2 (by linarith)

/-- Where `∫₀ᵗ β > 0`, the signal level of the variance-preserving path is less than `1`. -/
theorem vpSignal_lt_one (h : 0 < ∫ u in (0 : ℝ)..t, β u) : vpSignal β t < 1 :=
  Real.exp_lt_one_iff.2 (by linarith)

/-- Where `∫₀ᵗ β ≥ 0`, the signal and noise levels of the variance-preserving path are the
cosine and sine of an angle: their squares add up to `1`. -/
theorem vpNoise_sq (h : 0 ≤ ∫ u in (0 : ℝ)..t, β u) : vpNoise β t ^ 2 = 1 - vpSignal β t ^ 2 := by
  rw [vpNoise, Real.sq_sqrt]
  nlinarith [vpSignal_le_one h, vpSignal_pos β t]

/-- Where `∫₀ᵗ β > 0`, the noise level of the variance-preserving path is positive. -/
theorem vpNoise_pos (h : 0 < ∫ u in (0 : ℝ)..t, β u) : 0 < vpNoise β t := by
  rw [vpNoise, Real.sqrt_pos]
  nlinarith [vpSignal_lt_one h, vpSignal_pos β t]

/-- The ratio of the signal levels of the variance-preserving path at two times `r` and `t` is
`exp (-(∫ᵣᵗ β) / 2)`. -/
theorem vpSignal_div_vpSignal (h₀ : IntervalIntegrable β volume 0 r)
    (h₁ : IntervalIntegrable β volume r t) :
    vpSignal β t / vpSignal β r = Real.exp (-(∫ u in r..t, β u) / 2) := by
  rw [vpSignal, vpSignal, ← Real.exp_sub, ← intervalIntegral.integral_interval_sub_left
    (h₀.trans h₁) h₀]
  congr 1
  ring

/-- The observation kernel at time `t` of the variance-preserving path is the variance-preserving
noising kernel with signal level `exp (-∫₀ᵗ β)`, provided `∫₀ᵗ β ≥ 0`. -/
theorem gaussianKernel_vpSignal_vpNoise (h : 0 ≤ ∫ u in (0 : ℝ)..t, β u) :
    gaussianKernel (ι := ι) (vpSignal β t) (vpNoise β t ^ 2) =
      noiseKernel (Real.exp (-∫ u in (0 : ℝ)..t, β u)) := by
  rw [noiseKernel_eq_gaussianKernel, ← vpSignal_sq, Real.sqrt_sq (vpSignal_pos β t).le,
    vpNoise_sq h]

/-- **The transition kernels of the variance-preserving path.** If `β` is integrable on `[0, r]`
and on `[r, t]`, and `∫₀ʳ β ≥ 0` and `∫₀ᵗ β ≥ 0`, then the kernel given by the two-level formula
from time `r` to time `t` is the variance-preserving noising kernel with signal level
`exp (-∫ᵣᵗ β)`. When moreover `∫ᵣᵗ β ≥ 0`, it is a transition kernel, carrying the law at
time `r` to the law at time `t` by `gaussianKernel_div_comp_gaussianKernel`, and this signal level
lies in `(0, 1]`. Otherwise the variance argument is negative and both sides are point masses. -/
theorem gaussianKernel_vpSignal_div_eq_noiseKernel (h₀ : IntervalIntegrable β volume 0 r)
    (h₁ : IntervalIntegrable β volume r t) (hr : 0 ≤ ∫ u in (0 : ℝ)..r, β u)
    (ht : 0 ≤ ∫ u in (0 : ℝ)..t, β u) :
    gaussianKernel (ι := ι) (vpSignal β t / vpSignal β r)
        (vpNoise β t ^ 2 - (vpSignal β t / vpSignal β r) ^ 2 * vpNoise β r ^ 2) =
      noiseKernel (Real.exp (-∫ u in r..t, β u)) := by
  have hm : vpSignal β t / vpSignal β r = √(Real.exp (-∫ u in r..t, β u)) := by
    rw [vpSignal_div_vpSignal h₀ h₁, ← Real.exp_half]
  have hm₂ : (vpSignal β t / vpSignal β r) ^ 2 = Real.exp (-∫ u in r..t, β u) := by
    rw [hm, Real.sq_sqrt (Real.exp_pos _).le]
  have hαt : vpSignal β t ^ 2 = (vpSignal β t / vpSignal β r) ^ 2 * vpSignal β r ^ 2 := by
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 (vpSignal_pos β r).ne')]
  rw [noiseKernel_eq_gaussianKernel, ← hm, vpNoise_sq ht, vpNoise_sq hr, hαt, hm₂]
  congr 1
  ring

end TauCeti.Probability
