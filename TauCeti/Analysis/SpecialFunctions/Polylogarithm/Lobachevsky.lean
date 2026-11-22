/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrability.Log
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Log
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.ClosedDisc
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Holomorphy

/-!
# Lobachevsky's function

Lobachevsky's function is `Λ(θ) = -∫₀^θ log |2 sin t| dt`. Classically it computes hyperbolic
volumes: an ideal tetrahedron with dihedral angles `α, β, γ` has volume `Λ(α) + Λ(β) + Λ(γ)`, and
for a shape `z` in the upper half-plane this sum is the Bloch–Wigner dilogarithm `D(z)`. Neither
fact is proved here; this file supplies the function and its analytic properties.

This file defines `TauCeti.Polylog.lobachevsky` for every real argument, using that the
logarithmic integrand is locally integrable through its singularities at the multiples of `π`,
and proves its basic functional equations: it is odd, `π`-periodic, satisfies the reflection
`Λ(π - θ) = -Λ(θ)` and the duplication formula `Λ(2θ) = 2Λ(θ) + 2Λ(θ + π/2)`. Away from the
multiples of `π` it is differentiable with derivative `-log |2 sin θ|`. Its Fourier series
`Λ(θ) = 1/2 ∑_{m ≥ 1} sin (2mθ) / m²` converges absolutely and uniformly on the real line;
equivalently `Λ(θ) = Im Li₂(e^{2iθ}) / 2`, which is how the series is proved.

## Main results

* `TauCeti.Polylog.lobachevsky`: Lobachevsky's function.
* `TauCeti.Polylog.lobachevsky_neg`, `TauCeti.Polylog.lobachevsky_periodic`,
  `TauCeti.Polylog.lobachevsky_pi_sub` and `TauCeti.Polylog.lobachevsky_two_mul`: oddness,
  `π`-periodicity, reflection and duplication.
* `TauCeti.Polylog.hasDerivAt_lobachevsky`: the derivative away from the multiples of `π`.
* `TauCeti.Polylog.lobachevsky_eq_im_polylog_two`: `Λ(θ) = Im Li₂(e^{2iθ}) / 2`.
* `TauCeti.Polylog.hasSum_lobachevsky` and `TauCeti.Polylog.tendstoUniformly_lobachevsky`:
  the Fourier sine series and its uniform convergence.

## References

* John W. Milnor, *Computation of volume*, Chapter 7 of W. P. Thurston, *The Geometry and
  Topology of Three-Manifolds* (1980 notes, electronic edition 2002), §7.1, Lemmas 7.1.2–7.1.4,
  pp. 157–159.
* Don Zagier, *The dilogarithm function*, in Frontiers in Number Theory, Physics, and
  Geometry II (2007), Part I, §3.
-/

public section

open Filter MeasureTheory Real Set
open scoped Interval Topology

namespace TauCeti.Polylog

/-- The integrand `t ↦ log (2 sin t)` of Lobachevsky's function is interval integrable on every
interval, including those containing multiples of `π`, where it has logarithmic singularities. -/
theorem intervalIntegrable_log_two_mul_sin (a b : ℝ) :
    IntervalIntegrable (fun t ↦ log (2 * sin t)) volume a b :=
  (analyticOnNhd_const.mul analyticOnNhd_sin).meromorphicOn.intervalIntegrable_log

/-- **Lobachevsky's function** `Λ(θ) = -∫₀^θ log |2 sin t| dt`. Since Mathlib's `Real.log`
satisfies `log x = log |x|` (`Real.log_abs`), the integrand is written without the absolute value.
-/
noncomputable def lobachevsky (θ : ℝ) : ℝ :=
  -∫ t in 0..θ, log (2 * sin t)

/-- The defining integral of Lobachevsky's function. -/
theorem lobachevsky_def (θ : ℝ) : lobachevsky θ = -∫ t in 0..θ, log (2 * sin t) := (rfl)

/-- `Λ(0) = 0`. -/
@[simp] theorem lobachevsky_zero : lobachevsky 0 = 0 := by
  simp [lobachevsky_def]

/-- Away from the zeros of `sin`, `log (2 sin t) = log 2 + log (sin t)`; this holds off a discrete
set, which is enough to integrate it. -/
private lemma log_two_mul_sin_eventuallyEq :
    (fun t ↦ log (2 * sin t)) =ᶠ[codiscrete ℝ] fun t ↦ log 2 + log (sin t) := by
  have h : sin ⁻¹' {0}ᶜ ∈ codiscrete ℝ :=
    analyticOnNhd_sin.preimage_zero_mem_codiscrete (x := π / 2) (by simp)
  filter_upwards [h] with t ht
  exact log_mul two_ne_zero ht

/-- Integrals of `log (2 sin t)` split as `(b - a) log 2 + ∫ₐᵇ log (sin t)`. -/
private lemma integral_log_two_mul_sin (a b : ℝ) :
    ∫ t in a..b, log (2 * sin t) = (b - a) * log 2 + ∫ t in a..b, log (sin t) := by
  rw [intervalIntegral.integral_congr_codiscreteWithin
      (log_two_mul_sin_eventuallyEq.filter_mono (codiscreteWithin_mono (subset_univ _))),
    intervalIntegral.integral_add (g := fun t ↦ log (sin t)) intervalIntegrable_const
      intervalIntegrable_log_sin,
    intervalIntegral.integral_const, smul_eq_mul]

/-- `Λ(π) = 0`, equivalently `∫₀^π log |2 sin t| dt = 0`. -/
@[simp] theorem lobachevsky_pi : lobachevsky π = 0 := by
  simp [lobachevsky_def, integral_log_two_mul_sin, integral_log_sin_zero_pi]
  ring

/-- `Λ(π/2) = 0`, equivalently `∫₀^{π/2} log |2 sin t| dt = 0`. -/
@[simp] theorem lobachevsky_pi_div_two : lobachevsky (π / 2) = 0 := by
  simp [lobachevsky_def, integral_log_two_mul_sin, integral_log_sin_zero_pi_div_two]
  ring

/-- Lobachevsky's function is odd. -/
@[simp] theorem lobachevsky_neg (θ : ℝ) : lobachevsky (-θ) = -lobachevsky θ := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := θ) fun t ↦ log (2 * sin t)
  simp only [sin_neg, mul_neg, log_neg_eq_log, neg_zero] at h
  rw [lobachevsky_def, lobachevsky_def, h, intervalIntegral.integral_symm]

/-- Lobachevsky's function has period `π`. -/
theorem lobachevsky_periodic : Function.Periodic lobachevsky π := by
  intro θ
  have hper : Function.Periodic (fun t ↦ log (2 * sin t)) π := fun t ↦ by
    simp [sin_add_pi]
  rw [lobachevsky_def, lobachevsky_def, ← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_log_two_mul_sin 0 θ) (intervalIntegrable_log_two_mul_sin θ (θ + π)),
    hper.intervalIntegral_add_eq θ 0, zero_add]
  have h := lobachevsky_pi
  rw [lobachevsky_def, neg_eq_zero] at h
  rw [h, add_zero]

/-- The reflection formula `Λ(π - θ) = -Λ(θ)`. -/
theorem lobachevsky_pi_sub (θ : ℝ) : lobachevsky (π - θ) = -lobachevsky θ := by
  rw [sub_eq_neg_add, lobachevsky_periodic, lobachevsky_neg]

/-- Away from the zeros of `sin (2t)`, `log (2 sin 2t) = log (2 sin t) + log (2 sin (t + π/2))`;
this holds off a discrete set, which is enough to integrate it. -/
private lemma log_two_mul_sin_two_mul_eventuallyEq :
    (fun t ↦ log (2 * sin (2 * t))) =ᶠ[codiscrete ℝ]
      fun t ↦ log (2 * sin t) + log (2 * sin (t + π / 2)) := by
  have hs : sin ⁻¹' {0}ᶜ ∈ codiscrete ℝ :=
    analyticOnNhd_sin.preimage_zero_mem_codiscrete (x := π / 2) (by simp)
  have hc : cos ⁻¹' {0}ᶜ ∈ codiscrete ℝ :=
    analyticOnNhd_cos.preimage_zero_mem_codiscrete (x := 0) (by simp)
  filter_upwards [hs, hc] with t hst hct
  simp only [mem_preimage, mem_compl_iff, mem_singleton_iff] at hst hct
  rw [sin_add_pi_div_two, ← log_mul (by positivity) (by positivity), sin_two_mul]
  ring_nf

/-- The **duplication formula** `Λ(2θ) = 2Λ(θ) + 2Λ(θ + π/2)`. -/
theorem lobachevsky_two_mul (θ : ℝ) :
    lobachevsky (2 * θ) = 2 * lobachevsky θ + 2 * lobachevsky (θ + π / 2) := by
  have hdil : ∫ t in 0..2 * θ, log (2 * sin t) = 2 * ∫ t in 0..θ, log (2 * sin (2 * t)) := by
    rw [intervalIntegral.integral_comp_mul_left (fun t ↦ log (2 * sin t)) two_ne_zero, mul_zero,
      smul_eq_mul, mul_inv_cancel_left₀ two_ne_zero]
  have hshift : ∫ t in 0..θ, log (2 * sin (t + π / 2)) =
      (∫ t in 0..θ + π / 2, log (2 * sin t)) - ∫ t in 0..π / 2, log (2 * sin t) := by
    rw [intervalIntegral.integral_comp_add_right (fun t ↦ log (2 * sin t)), zero_add,
      intervalIntegral.integral_interval_sub_left (intervalIntegrable_log_two_mul_sin _ _)
        (intervalIntegrable_log_two_mul_sin _ _)]
  have hint : IntervalIntegrable (fun t ↦ log (2 * sin (t + π / 2))) volume 0 θ := by
    simpa using (intervalIntegrable_log_two_mul_sin (0 + π / 2) (θ + π / 2)).comp_add_right (π / 2)
  have hhalf := lobachevsky_pi_div_two
  rw [lobachevsky_def, neg_eq_zero] at hhalf
  rw [lobachevsky_def, lobachevsky_def, lobachevsky_def, hdil,
    intervalIntegral.integral_congr_codiscreteWithin
      (log_two_mul_sin_two_mul_eventuallyEq.filter_mono (codiscreteWithin_mono (subset_univ _))),
    intervalIntegral.integral_add (intervalIntegrable_log_two_mul_sin _ _) hint,
    hshift, hhalf]
  ring

/-- Lobachevsky's function is continuous. -/
theorem continuous_lobachevsky : Continuous lobachevsky :=
  (intervalIntegral.continuous_primitive intervalIntegrable_log_two_mul_sin 0).neg

/-- Away from the multiples of `π`, Lobachevsky's function has derivative `-log |2 sin θ|`. -/
theorem hasDerivAt_lobachevsky {θ : ℝ} (hθ : sin θ ≠ 0) :
    HasDerivAt lobachevsky (-log (2 * sin θ)) θ := by
  have hcont : ContinuousAt (fun t ↦ log (2 * sin t)) θ :=
    (continuous_const.mul continuous_sin).continuousAt.log (mul_ne_zero two_ne_zero hθ)
  have hmeas : Measurable fun t ↦ log (2 * sin t) := by fun_prop
  exact (intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_log_two_mul_sin 0 θ)
    hmeas.stronglyMeasurable.stronglyMeasurableAtFilter hcont).neg

/-! ### The Fourier series -/

/-- The chord `1 - e^{2iθ}` equals `-2i sin θ · e^{iθ}`. -/
private lemma one_sub_exp_two_mul_I (θ : ℝ) :
    1 - Complex.exp (2 * θ * Complex.I) =
      -2 * sin θ * Complex.I * Complex.exp (θ * Complex.I) := by
  rw [show (2 : ℂ) * θ * Complex.I = θ * Complex.I + θ * Complex.I by ring, Complex.exp_add,
    Complex.exp_mul_I]
  push_cast
  linear_combination (-1 : ℂ) * Complex.sin_sq_add_cos_sq (θ : ℂ) +
    Complex.sin θ ^ 2 * Complex.I_sq

/-- The chord length `|1 - e^{2iθ}| = |2 sin θ|`. -/
private lemma norm_one_sub_exp_two_mul_I (θ : ℝ) :
    ‖1 - Complex.exp (2 * θ * Complex.I)‖ = |2 * sin θ| := by
  rw [one_sub_exp_two_mul_I, norm_mul, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  norm_num

/-- Away from the multiples of `π`, the chord `1 - e^{2iθ}` has positive real part `2 sin² θ`. -/
private lemma one_sub_exp_two_mul_I_mem_slitPlane {θ : ℝ} (hθ : sin θ ≠ 0) :
    1 - Complex.exp (2 * θ * Complex.I) ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
  rw [one_sub_exp_two_mul_I]
  simp [Complex.mul_re, Complex.sin_ofReal_re]
  nlinarith [mul_self_pos.mpr hθ]

/-- The function `θ ↦ Im Li₂(e^{2iθ}) / 2` has derivative `-log |2 sin θ|` away from the multiples
of `π`, like Lobachevsky's function. -/
private lemma hasDerivAt_im_polylog_two_exp {θ : ℝ} (hθ : sin θ ≠ 0) :
    HasDerivAt (fun x : ℝ ↦ (polylog 2 (Complex.exp (2 * x * Complex.I))).im / 2)
      (-log (2 * sin θ)) θ := by
  have hz : Complex.exp (2 * θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hw : HasDerivAt (fun x : ℝ ↦ Complex.exp (2 * x * Complex.I))
      (Complex.exp (2 * θ * Complex.I) * (2 * Complex.I)) θ := by
    simpa using (((hasDerivAt_id θ).ofReal_comp.const_mul (2 : ℂ)).mul_const Complex.I).cexp
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ
    ((hasDerivAt_polylog 2 (one_sub_exp_two_mul_I_mem_slitPlane hθ) hz).comp θ hw)
  convert h.div_const 2 using 1
  · ext x
    simp
  have him : ∀ w : ℂ, (-w * (2 * Complex.I)).im = -2 * w.re := fun w ↦ by simp [mul_comm]
  have halg : polylog (2 - 1) (Complex.exp (2 * θ * Complex.I)) / Complex.exp (2 * θ * Complex.I) *
      (Complex.exp (2 * θ * Complex.I) * (2 * Complex.I)) =
        -Complex.log (1 - Complex.exp (2 * θ * Complex.I)) * (2 * Complex.I) := by
    rw [show ((2 : ℤ) - 1) = 1 by norm_num, polylog_one]
    field_simp
  rw [halg, Complex.imCLM_apply, him, Complex.log_re, norm_one_sub_exp_two_mul_I, log_abs]
  ring

/-- **Lobachevsky's function as a dilogarithm value**: `Λ(θ) = Im Li₂(e^{2iθ}) / 2`. -/
theorem lobachevsky_eq_im_polylog_two (θ : ℝ) :
    lobachevsky θ = (polylog 2 (Complex.exp (2 * θ * Complex.I))).im / 2 := by
  set G : ℝ → ℝ := fun x ↦ (polylog 2 (Complex.exp (2 * x * Complex.I))).im / 2
  set H : ℝ → ℝ := fun x ↦ lobachevsky x - G x
  have hGper : Function.Periodic G π := fun x ↦ by
    simp only [G]
    congr 3
    push_cast
    rw [mul_add, add_mul, Complex.exp_add, mul_assoc 2 (π : ℂ), ← mul_assoc,
      Complex.exp_two_pi_mul_I, mul_one]
  have hHper : Function.Periodic H π := lobachevsky_periodic.sub hGper
  have hGcont : Continuous G := by
    refine Complex.continuous_im.comp ((continuousOn_polylog_closedBall le_rfl).comp_continuous
      (by fun_prop) fun x ↦ ?_) |>.div_const 2
    rw [mem_closedBall_zero_iff, show (2 : ℂ) * x * Complex.I = ((2 * x : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have hH0 : H 0 = 0 := by
    have hπ : ((π : ℂ) ^ 2).im = 0 := by rw [← Complex.ofReal_pow, Complex.ofReal_im]
    simp [H, G, polylog_two_one, hπ]
  -- On `(0, π)` the mean value theorem forces `H` to vanish, since `H' = 0` there.
  have hIoo : ∀ x ∈ Ioo 0 π, H x = 0 := by
    intro x hx
    obtain ⟨c, -, hc'⟩ := exists_hasDerivAt_eq_slope H (fun _ ↦ 0) hx.1
      (continuous_lobachevsky.sub hGcont).continuousOn fun c hc ↦ by
        have hsin : sin c ≠ 0 := (sin_pos_of_pos_of_lt_pi hc.1 (hc.2.trans hx.2)).ne'
        exact ((hasDerivAt_lobachevsky hsin).sub (hasDerivAt_im_polylog_two_exp hsin)).congr_deriv
          (sub_self _)
    rw [hH0, sub_zero, sub_zero, eq_comm, div_eq_zero_iff] at hc'
    exact hc'.resolve_right hx.1.ne'
  obtain ⟨y, hy, hHy⟩ := hHper.exists_mem_Ico₀ pi_pos θ
  refine sub_eq_zero.mp (hHy.trans ?_)
  rcases hy.1.eq_or_lt with rfl | hy0
  · exact hH0
  · exact hIoo y ⟨hy0, hy.2⟩

/-- **Fourier series of Lobachevsky's function**: `Λ(θ) = 1/2 ∑_{m ≥ 1} sin (2mθ) / m²`. -/
theorem hasSum_lobachevsky (θ : ℝ) :
    HasSum (fun k : ℕ ↦ sin (2 * (k + 1) * θ) / (2 * (k + 1) ^ 2)) (lobachevsky θ) := by
  rw [lobachevsky_eq_im_polylog_two]
  refine ((Complex.imCLM.hasSum (hasSum_polylog_of_norm_le_one le_rfl
    (z := Complex.exp (2 * θ * Complex.I)) ?_)).div_const 2).congr_fun fun k ↦ ?_
  · rw [show (2 : ℂ) * θ * Complex.I = ((2 * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  · rw [← Complex.exp_natCast_mul, show ((k + 1 : ℕ) : ℂ) * (2 * θ * Complex.I) =
        ((2 * (k + 1) * θ : ℝ) : ℂ) * Complex.I by push_cast; ring,
      show ((k : ℂ) + 1) ^ (2 : ℤ) = (((k + 1) ^ 2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.imCLM_apply, Complex.div_ofReal_im, Complex.exp_ofReal_mul_I_im]
    field_simp

/-- The terms of the Fourier series of Lobachevsky's function are bounded by `1 / (k + 1) ^ 2`. -/
private lemma abs_sin_div_le (θ : ℝ) (k : ℕ) :
    |sin (2 * (k + 1) * θ) / (2 * (k + 1) ^ 2)| ≤ 1 / ((k + 1 : ℕ) : ℝ) ^ 2 := by
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (k + 1) ^ 2), div_le_div_iff₀
    (by positivity) (by positivity)]
  push_cast
  nlinarith [abs_sin_le_one (2 * (k + 1) * θ), sq_nonneg ((k : ℝ) + 1)]

/-- The Fourier series of Lobachevsky's function converges absolutely. -/
theorem summable_abs_sin_two_mul_div_sq (θ : ℝ) :
    Summable fun k : ℕ ↦ |sin (2 * (k + 1) * θ) / (2 * (k + 1) ^ 2)| :=
  ((summable_nat_add_iff 1).mpr (summable_one_div_nat_pow.mpr one_lt_two)).of_nonneg_of_le
    (fun _ ↦ abs_nonneg _) (abs_sin_div_le θ)

/-- The partial sums of the Fourier series of Lobachevsky's function converge uniformly on the
real line. -/
theorem tendstoUniformly_lobachevsky :
    TendstoUniformly (fun N θ ↦ ∑ k ∈ Finset.range N, sin (2 * (k + 1) * θ) / (2 * (k + 1) ^ 2))
      lobachevsky atTop := by
  have h := tendstoUniformly_tsum_nat
    ((summable_nat_add_iff 1).mpr (summable_one_div_nat_pow.mpr one_lt_two)) fun k θ ↦
    (Real.norm_eq_abs _).trans_le (abs_sin_div_le θ k)
  rwa [show (fun θ ↦ ∑' k : ℕ, sin (2 * (k + 1) * θ) / (2 * (k + 1) ^ 2)) = lobachevsky from
    funext fun θ ↦ (hasSum_lobachevsky θ).tsum_eq] at h

end TauCeti.Polylog
