/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Complex.ParametricIntegralHolomorphy

/-!
# The Anger and Weber functions

The Anger function `𝐉_ν(z)` and the Weber function `𝐄_ν(z)` are the integrals

`𝐉_ν(z) = π⁻¹ ∫₀^π cos(νθ − z sin θ) dθ`,  `𝐄_ν(z) = π⁻¹ ∫₀^π sin(νθ − z sin θ) dθ`

(DLMF 11.10.1–11.10.2), for complex order `ν` and complex argument `z`. At an integer order `n`,
Bessel's integral shows `𝐉_n = J_n`; at other orders `𝐉_ν` and `𝐄_ν` are particular solutions of
Bessel's equation with an elementary forcing term. With the Struve and Lommel functions they are
the classical particular solutions of the inhomogeneous Bessel equation.

This file defines `Complex.angerJ` and `Complex.weberE` and proves:

* both are entire functions of the pair `(ν, z)` (`Complex.analyticOnNhd_angerJ`,
  `Complex.analyticOnNhd_weberE`);
* the derivative formulas `2 𝐉_ν′(z) = 𝐉_{ν−1}(z) − 𝐉_{ν+1}(z)` and
  `2 𝐄_ν′(z) = 𝐄_{ν−1}(z) − 𝐄_{ν+1}(z)` (DLMF 11.10.33 and 11.10.36), by differentiating under the
  integral sign (`Complex.hasDerivAt_angerJ`, `Complex.hasDerivAt_weberE`);
* the three-term recurrences, in the form multiplied by `z`, which holds for every `z`:
  `2ν 𝐉_ν(z) = z 𝐉_{ν−1}(z) + z 𝐉_{ν+1}(z) + (2/π) sin(πν)` and
  `2ν 𝐄_ν(z) = z 𝐄_{ν−1}(z) + z 𝐄_{ν+1}(z) + (2/π)(1 − cos(πν))` (DLMF 11.10.32 and 11.10.35;
  `Complex.two_mul_self_mul_angerJ`, `Complex.two_mul_self_mul_weberE`), by integrating the
  derivative of `θ ↦ sin(νθ − z sin θ)` or `θ ↦ cos(νθ − z sin θ)` over `[0, π]`;
* the integral over a full period,
  `∫₀^{2π} cos(νθ − z sin θ) dθ = π ((1 + cos 2πν) 𝐉_ν(z) + sin(2πν) 𝐄_ν(z))` (DLMF 11.10.3;
  `Complex.integral_zero_two_pi_cos_mul_sub_mul_sin`);
* the values at `z = 0`, `𝐉_ν(0) = sin(πν)/(πν)` and `𝐄_ν(0) = (1 − cos(πν))/(πν)` for `ν ≠ 0`,
  and `𝐉_0(0) = 1`, `𝐄_0(0) = 0` (DLMF 11.10.25);
* the inhomogeneous Bessel equations (DLMF 11.10.5–11.10.7), in the form multiplied by `z²`,
  which holds for every `z`:
  `z² 𝐉_ν′′ + z 𝐉_ν′ + (z² − ν²) 𝐉_ν = (z − ν) sin(πν)/π` and
  `z² 𝐄_ν′′ + z 𝐄_ν′ + (z² − ν²) 𝐄_ν = −(z + ν + (z − ν) cos(πν))/π`
  (`Complex.angerJ_ode`, `Complex.weberE_ode`). They follow algebraically from the derivative
  formulas and the recurrences, as Bessel's equation for `J_ν` follows from DLMF 10.6.1.

## References

* NIST *Digital Library of Mathematical Functions*, §11.10, <https://dlmf.nist.gov/11.10>.
* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, 2nd ed., Cambridge University
  Press, 1944, §10.1.
* I. S. Gradshteyn and I. M. Ryzhik, *Table of Integrals, Series, and Products*, 7th ed.,
  §§8.580–8.584.
-/

public section

noncomputable section

open MeasureTheory Metric Set
open scoped Real

namespace Complex

/-- The Anger function `𝐉_ν(z) = π⁻¹ ∫₀^π cos(νθ − z sin θ) dθ` (DLMF 11.10.1). -/
def angerJ (ν z : ℂ) : ℂ :=
  (π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..π, cos (ν * θ - z * Real.sin θ)

/-- The Weber function `𝐄_ν(z) = π⁻¹ ∫₀^π sin(νθ − z sin θ) dθ` (DLMF 11.10.2). -/
def weberE (ν z : ℂ) : ℂ :=
  (π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..π, sin (ν * θ - z * Real.sin θ)

/-- The defining integral of the Anger function. -/
theorem angerJ_def (ν z : ℂ) :
    angerJ ν z = (π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..π, cos (ν * θ - z * Real.sin θ) := (rfl)

/-- The defining integral of the Weber function. -/
theorem weberE_def (ν z : ℂ) :
    weberE ν z = (π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..π, sin (ν * θ - z * Real.sin θ) := (rfl)

/-! ### Integrals of `G (νθ − z sin θ)` over `[0, π]` -/

/-- The integrands of the Anger and Weber integrals are bounded on `(0, π]`, uniformly for the
parameters `(ν, z)` in a compact set. -/
private theorem exists_bound_integrand {G : ℂ → ℂ} (hG : Continuous G) {K : Set (ℂ × ℂ)}
    (hK : IsCompact K) :
    ∃ C, ∀ θ ∈ Ioc (0 : ℝ) π, ∀ p ∈ K, ‖G (p.1 * θ - p.2 * Real.sin θ)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := π)).prod hK |>.exists_bound_of_continuousOn
    (f := fun q : ℝ × (ℂ × ℂ) => G (q.2.1 * q.1 - q.2.2 * Real.sin q.1))
    (by fun_prop : Continuous _).continuousOn
  exact ⟨C, fun θ hθ p hp => hC (θ, p) ⟨Ioc_subset_Icc_self hθ, hp⟩⟩

/-- For an entire `G`, the integral `∫₀^π G(νθ − z sin θ) dθ` is an entire function of
`(ν, z)`. -/
private theorem analyticOnNhd_integral {G : ℂ → ℂ} (hG : Differentiable ℂ G) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => ∫ θ in (0 : ℝ)..π, G (p.1 * θ - p.2 * Real.sin θ))
      univ := by
  have hGc := hG.continuous
  simp_rw [intervalIntegral.integral_of_le Real.pi_pos.le]
  refine TauCeti.analyticOnNhd_integral_of_dominated isOpen_univ
    (fun p _ => (by fun_prop : Continuous fun θ : ℝ =>
      G (p.1 * θ - p.2 * Real.sin θ)).aestronglyMeasurable) (fun p _ => ?_)
    (ae_of_all _ fun θ => (by fun_prop : Differentiable ℂ fun p : ℂ × ℂ =>
      G (p.1 * θ - p.2 * Real.sin θ)).differentiableOn)
  obtain ⟨C, hC⟩ := exists_bound_integrand hGc (isCompact_closedBall p 1)
  exact ⟨closedBall p 1, closedBall_mem_nhds p one_pos, fun _ => C, integrable_const C,
    (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun θ hθ q hq => hC θ hθ q hq)⟩

/-- Differentiation in `z` under the integral sign: if `G` is entire with derivative `G'`, then
`z ↦ ∫₀^π G(νθ − z sin θ) dθ` has derivative `−∫₀^π sin θ · G'(νθ − z sin θ) dθ`. -/
private theorem hasDerivAt_integral {G G' : ℂ → ℂ} (hG : ∀ w, HasDerivAt G (G' w) w)
    (ν z : ℂ) :
    HasDerivAt (fun w => ∫ θ in (0 : ℝ)..π, G (ν * θ - w * Real.sin θ))
      (∫ θ in (0 : ℝ)..π, -(Real.sin θ * G' (ν * θ - z * Real.sin θ))) z := by
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun w => (hG w).continuousAt
  have hd (θ : ℝ) (w : ℂ) : HasDerivAt (fun w => G (ν * θ - w * Real.sin θ))
      (-(Real.sin θ * G' (ν * θ - w * Real.sin θ))) w := by
    have hl : HasDerivAt (fun w : ℂ => ν * θ - w * Real.sin θ) (-(Real.sin θ : ℂ)) w := by
      simpa using ((hasDerivAt_id w).mul_const (Real.sin θ : ℂ)).const_sub (ν * θ)
    exact ((hG _).comp w hl).congr_deriv (by ring)
  obtain ⟨C, hC⟩ := exists_bound_integrand hGc (isCompact_singleton.prod
    (isCompact_closedBall z 1))
  have h := TauCeti.hasDerivAt_integral_of_dominated_of_differentiableOn
    (μ := volume.restrict (Ioc 0 π)) (F := fun w (θ : ℝ) => G (ν * θ - w * Real.sin θ))
    (bound := fun _ => C) isOpen_ball (mem_ball_self one_pos)
    (fun w _ => (by fun_prop : Continuous fun θ : ℝ =>
      G (ν * θ - w * Real.sin θ)).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun θ hθ w hw =>
      hC θ hθ (ν, w) ⟨rfl, ball_subset_closedBall hw⟩))
    (integrable_const C)
    (ae_of_all _ fun θ w _ => (hd θ w).differentiableAt.differentiableWithinAt)
  simp only [fun θ => (hd θ z).deriv] at h
  simp_rw [intervalIntegral.integral_of_le Real.pi_pos.le]
  exact h

/-- The integrands of the Anger and Weber integrals are interval integrable. -/
private theorem intervalIntegrable_integrand {G : ℂ → ℂ} (hG : Continuous G) (ν z : ℂ) :
    IntervalIntegrable (fun θ : ℝ => G (ν * θ - z * Real.sin θ)) volume 0 π :=
  (by fun_prop : Continuous fun θ : ℝ => G (ν * θ - z * Real.sin θ)).intervalIntegrable 0 π

/-- The phase `θ ↦ νθ − z sin θ` has derivative `ν − z cos θ`. -/
private theorem hasDerivAt_phase (ν z : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => ν * θ - z * Real.sin θ) (ν - z * Real.cos θ) θ := by
  have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ)) 1 θ := by
    simpa using (hasDerivAt_id θ).ofReal_comp
  convert (h1.const_mul ν).sub ((Real.hasDerivAt_sin θ).ofReal_comp.const_mul z) using 1
  ring

/-- Lowering the order by `1` lowers the phase by `θ`. -/
private theorem phase_sub_one (ν z : ℂ) (θ : ℝ) :
    (ν - 1) * θ - z * Real.sin θ = (ν * θ - z * Real.sin θ) - θ := by ring

/-- Raising the order by `1` raises the phase by `θ`. -/
private theorem phase_add_one (ν z : ℂ) (θ : ℝ) :
    (ν + 1) * θ - z * Real.sin θ = (ν * θ - z * Real.sin θ) + θ := by ring

/-! ### Holomorphy -/

/-- The Anger function `𝐉_ν(z)` is an entire function of the pair `(ν, z)`. -/
theorem analyticOnNhd_angerJ : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => angerJ p.1 p.2) univ := by
  simp only [angerJ_def]
  exact analyticOnNhd_const.mul (analyticOnNhd_integral differentiable_cos)

/-- The Weber function `𝐄_ν(z)` is an entire function of the pair `(ν, z)`. -/
theorem analyticOnNhd_weberE : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => weberE p.1 p.2) univ := by
  simp only [weberE_def]
  exact analyticOnNhd_const.mul (analyticOnNhd_integral differentiable_sin)

/-- The Anger function `𝐉_ν(z)` is complex differentiable in the pair `(ν, z)`. -/
theorem differentiable_angerJ : Differentiable ℂ fun p : ℂ × ℂ => angerJ p.1 p.2 :=
  fun p => (analyticOnNhd_angerJ p trivial).differentiableAt

/-- The Weber function `𝐄_ν(z)` is complex differentiable in the pair `(ν, z)`. -/
theorem differentiable_weberE : Differentiable ℂ fun p : ℂ × ℂ => weberE p.1 p.2 :=
  fun p => (analyticOnNhd_weberE p trivial).differentiableAt

/-! ### Derivatives -/

/-- The derivative of the Anger function (DLMF 11.10.33): `𝐉_ν′(z) = (𝐉_{ν−1}(z) − 𝐉_{ν+1}(z))/2`,
for every order `ν` and argument `z`. -/
theorem hasDerivAt_angerJ (ν z : ℂ) :
    HasDerivAt (angerJ ν) ((angerJ (ν - 1) z - angerJ (ν + 1) z) / 2) z := by
  have h := (hasDerivAt_integral (fun w => hasDerivAt_cos w) ν z).const_mul (π : ℂ)⁻¹
  convert h using 1
  · exact funext fun w => angerJ_def ν w
  · have key (θ : ℝ) : -((Real.sin θ : ℂ) * -sin (ν * θ - z * Real.sin θ)) =
        (cos ((ν - 1) * θ - z * Real.sin θ) - cos ((ν + 1) * θ - z * Real.sin θ)) / 2 := by
      rw [phase_sub_one, phase_add_one, cos_sub, cos_add, ofReal_sin]
      ring
    rw [angerJ_def, angerJ_def, intervalIntegral.integral_congr fun θ _ => key θ,
      intervalIntegral.integral_div, intervalIntegral.integral_sub
        (intervalIntegrable_integrand continuous_cos _ _)
        (intervalIntegrable_integrand continuous_cos _ _)]
    ring

/-- The derivative of the Weber function (DLMF 11.10.36): `𝐄_ν′(z) = (𝐄_{ν−1}(z) − 𝐄_{ν+1}(z))/2`,
for every order `ν` and argument `z`. -/
theorem hasDerivAt_weberE (ν z : ℂ) :
    HasDerivAt (weberE ν) ((weberE (ν - 1) z - weberE (ν + 1) z) / 2) z := by
  have h := (hasDerivAt_integral (fun w => hasDerivAt_sin w) ν z).const_mul (π : ℂ)⁻¹
  convert h using 1
  · exact funext fun w => weberE_def ν w
  · have key (θ : ℝ) : -((Real.sin θ : ℂ) * cos (ν * θ - z * Real.sin θ)) =
        (sin ((ν - 1) * θ - z * Real.sin θ) - sin ((ν + 1) * θ - z * Real.sin θ)) / 2 := by
      rw [phase_sub_one, phase_add_one, sin_sub, sin_add, ofReal_sin]
      ring
    rw [weberE_def, weberE_def, intervalIntegral.integral_congr fun θ _ => key θ,
      intervalIntegral.integral_div, intervalIntegral.integral_sub
        (intervalIntegrable_integrand continuous_sin _ _)
        (intervalIntegrable_integrand continuous_sin _ _)]
    ring

/-- `2 𝐉_ν′(z) = 𝐉_{ν−1}(z) − 𝐉_{ν+1}(z)` (DLMF 11.10.33), as a value of `deriv`. -/
theorem two_mul_deriv_angerJ (ν z : ℂ) :
    2 * deriv (angerJ ν) z = angerJ (ν - 1) z - angerJ (ν + 1) z := by
  rw [(hasDerivAt_angerJ ν z).deriv]
  ring

/-- `2 𝐄_ν′(z) = 𝐄_{ν−1}(z) − 𝐄_{ν+1}(z)` (DLMF 11.10.36), as a value of `deriv`. -/
theorem two_mul_deriv_weberE (ν z : ℂ) :
    2 * deriv (weberE ν) z = weberE (ν - 1) z - weberE (ν + 1) z := by
  rw [(hasDerivAt_weberE ν z).deriv]
  ring

/-! ### Recurrences -/

/-- The three-term recurrence of the Anger function (DLMF 11.10.32), multiplied by `z`:
`2ν 𝐉_ν(z) = z 𝐉_{ν−1}(z) + z 𝐉_{ν+1}(z) + (2/π) sin(πν)` for every order `ν` and argument
`z`. -/
theorem two_mul_self_mul_angerJ (ν z : ℂ) :
    2 * ν * angerJ ν z = z * angerJ (ν - 1) z + z * angerJ (ν + 1) z + 2 / π * sin (π * ν) := by
  have hftc : ∫ θ in (0 : ℝ)..π, cos (ν * θ - z * Real.sin θ) * (ν - z * Real.cos θ) =
      sin (π * ν) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun θ : ℝ => sin (ν * θ - z * Real.sin θ))
      (fun θ _ => (hasDerivAt_sin _).comp θ (hasDerivAt_phase ν z θ))
      ((by fun_prop : Continuous fun θ : ℝ =>
        cos (ν * θ - z * Real.sin θ) * (ν - z * Real.cos θ)).intervalIntegrable 0 π)]
    simp [mul_comm]
  have key (θ : ℝ) : cos (ν * θ - z * Real.sin θ) * (ν - z * Real.cos θ) =
      ν * cos (ν * θ - z * Real.sin θ) -
        z / 2 * (cos ((ν - 1) * θ - z * Real.sin θ) + cos ((ν + 1) * θ - z * Real.sin θ)) := by
    rw [phase_sub_one, phase_add_one, cos_sub _ (θ : ℂ), cos_add _ (θ : ℂ), ofReal_cos]
    ring
  have hi := intervalIntegrable_integrand continuous_cos
  rw [intervalIntegral.integral_congr fun θ _ => key θ, intervalIntegral.integral_sub
    ((hi ν z).const_mul ν) (((hi _ z).add (hi _ z)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hi _ z) (hi _ z)] at hftc
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [angerJ_def, angerJ_def, angerJ_def, ← hftc]
  field_simp
  ring

/-- The three-term recurrence of the Weber function (DLMF 11.10.35), multiplied by `z`:
`2ν 𝐄_ν(z) = z 𝐄_{ν−1}(z) + z 𝐄_{ν+1}(z) + (2/π)(1 − cos(πν))` for every order `ν` and argument
`z`. -/
theorem two_mul_self_mul_weberE (ν z : ℂ) :
    2 * ν * weberE ν z =
      z * weberE (ν - 1) z + z * weberE (ν + 1) z + 2 / π * (1 - cos (π * ν)) := by
  have hftc : ∫ θ in (0 : ℝ)..π, sin (ν * θ - z * Real.sin θ) * (ν - z * Real.cos θ) =
      1 - cos (π * ν) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun θ : ℝ => -cos (ν * θ - z * Real.sin θ))
      (fun θ _ => ((hasDerivAt_cos _).comp θ (hasDerivAt_phase ν z θ)).neg.congr_deriv (by ring))
      ((by fun_prop : Continuous fun θ : ℝ =>
        sin (ν * θ - z * Real.sin θ) * (ν - z * Real.cos θ)).intervalIntegrable 0 π)]
    simp [mul_comm]
    ring
  have key (θ : ℝ) : sin (ν * θ - z * Real.sin θ) * (ν - z * Real.cos θ) =
      ν * sin (ν * θ - z * Real.sin θ) -
        z / 2 * (sin ((ν - 1) * θ - z * Real.sin θ) + sin ((ν + 1) * θ - z * Real.sin θ)) := by
    rw [phase_sub_one, phase_add_one, sin_sub _ (θ : ℂ), sin_add _ (θ : ℂ), ofReal_cos]
    ring
  have hi := intervalIntegrable_integrand continuous_sin
  rw [intervalIntegral.integral_congr fun θ _ => key θ, intervalIntegral.integral_sub
    ((hi ν z).const_mul ν) (((hi _ z).add (hi _ z)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hi _ z) (hi _ z)] at hftc
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  rw [weberE_def, weberE_def, weberE_def, ← hftc]
  field_simp
  ring

/-! ### The integral over a full period -/

/-- The integral of `cos(νθ − z sin θ)` over a full period (DLMF 11.10.3):
`∫₀^{2π} cos(νθ − z sin θ) dθ = π ((1 + cos 2πν) 𝐉_ν(z) + sin(2πν) 𝐄_ν(z))`. -/
theorem integral_zero_two_pi_cos_mul_sub_mul_sin (ν z : ℂ) :
    ∫ θ in (0 : ℝ)..2 * π, cos (ν * θ - z * Real.sin θ) =
      π * ((1 + cos (2 * π * ν)) * angerJ ν z + sin (2 * π * ν) * weberE ν z) := by
  have hc : Continuous fun θ : ℝ => cos (ν * θ - z * Real.sin θ) := by fun_prop
  -- On `[π, 2π]`, substitute `θ = 2π − φ`: the phase becomes `2πν − (νφ − z sin φ)`.
  have h2 : ∫ θ in π..2 * π, cos (ν * θ - z * Real.sin θ) =
      ∫ θ in (0 : ℝ)..π, (cos (2 * π * ν) * cos (ν * θ - z * Real.sin θ) +
        sin (2 * π * ν) * sin (ν * θ - z * Real.sin θ)) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun θ : ℝ => cos (ν * θ - z * Real.sin θ)) (2 * π) (a := 0) (b := π)
    rw [show 2 * π - π = π by ring, sub_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    rw [Real.sin_two_pi_sub, ← cos_sub]
    push_cast
    ring_nf
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), h2, intervalIntegral.integral_add
    ((intervalIntegrable_integrand continuous_cos ν z).const_mul _)
    ((intervalIntegrable_integrand continuous_sin ν z).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, angerJ_def,
    weberE_def]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  field_simp
  ring

/-! ### Values at `z = 0` -/

/-- The Anger function at `z = 0` (DLMF 11.10.25): `𝐉_ν(0) = sin(πν)/(πν)` for `ν ≠ 0`. -/
theorem angerJ_zero {ν : ℂ} (hν : ν ≠ 0) : angerJ ν 0 = sin (π * ν) / (π * ν) := by
  have h := two_mul_self_mul_angerJ ν 0
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  simp only [zero_mul, zero_add] at h
  rw [eq_div_iff (mul_ne_zero hπ hν)]
  linear_combination (norm := (field_simp; ring)) π / 2 * h

/-- The Weber function at `z = 0` (DLMF 11.10.25): `𝐄_ν(0) = (1 − cos(πν))/(πν)` for `ν ≠ 0`. -/
theorem weberE_zero {ν : ℂ} (hν : ν ≠ 0) : weberE ν 0 = (1 - cos (π * ν)) / (π * ν) := by
  have h := two_mul_self_mul_weberE ν 0
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  simp only [zero_mul, zero_add] at h
  rw [eq_div_iff (mul_ne_zero hπ hν)]
  linear_combination (norm := (field_simp; ring)) π / 2 * h

/-- `𝐉_0(0) = π⁻¹ ∫₀^π dθ = 1`. -/
@[simp]
theorem angerJ_zero_zero : angerJ 0 0 = 1 := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  simp [angerJ_def, hπ]

/-- `𝐄_0(0) = π⁻¹ ∫₀^π sin 0 dθ = 0`. -/
@[simp]
theorem weberE_zero_zero : weberE 0 0 = 0 := by
  simp [weberE_def]

/-! ### The inhomogeneous Bessel equations -/

/-- The equation of the Anger function (DLMF 11.10.5–11.10.6), multiplied by `z²`:
`z² 𝐉_ν′′(z) + z 𝐉_ν′(z) + (z² − ν²) 𝐉_ν(z) = (z − ν) sin(πν)/π` for every order `ν` and
argument `z`. -/
theorem angerJ_ode (ν z : ℂ) :
    z ^ 2 * deriv^[2] (angerJ ν) z + z * deriv (angerJ ν) z + (z ^ 2 - ν ^ 2) * angerJ ν z =
      (z - ν) * sin (π * ν) / π := by
  have hd (μ : ℂ) : deriv (angerJ μ) = fun w => (angerJ (μ - 1) w - angerJ (μ + 1) w) / 2 :=
    funext fun w => (hasDerivAt_angerJ μ w).deriv
  have h2 : deriv^[2] (angerJ ν) z = ((angerJ (ν - 1 - 1) z - angerJ (ν - 1 + 1) z) / 2 -
      (angerJ (ν + 1 - 1) z - angerJ (ν + 1 + 1) z) / 2) / 2 := by
    rw [Function.iterate_succ_apply', Function.iterate_one, hd]
    exact (((hasDerivAt_angerJ (ν - 1) z).sub (hasDerivAt_angerJ (ν + 1) z)).div_const 2).deriv
  have r₀ := two_mul_self_mul_angerJ ν z
  have r₁ := two_mul_self_mul_angerJ (ν - 1) z
  have r₂ := two_mul_self_mul_angerJ (ν + 1) z
  rw [mul_sub (π : ℂ) ν 1, mul_one, sin_sub_pi] at r₁
  rw [mul_add (π : ℂ) ν 1, mul_one, sin_add_pi] at r₂
  rw [h2, hd]
  simp only [sub_add_cancel, add_sub_cancel_right] at r₁ r₂ ⊢
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  linear_combination (norm := (field_simp; ring)) -(z / 4) * r₁ - z / 4 * r₂ - ν / 2 * r₀

/-- The equation of the Weber function (DLMF 11.10.5 and 11.10.7), multiplied by `z²`:
`z² 𝐄_ν′′(z) + z 𝐄_ν′(z) + (z² − ν²) 𝐄_ν(z) = −(z + ν + (z − ν) cos(πν))/π` for every order `ν`
and argument `z`. -/
theorem weberE_ode (ν z : ℂ) :
    z ^ 2 * deriv^[2] (weberE ν) z + z * deriv (weberE ν) z + (z ^ 2 - ν ^ 2) * weberE ν z =
      -(z + ν + (z - ν) * cos (π * ν)) / π := by
  have hd (μ : ℂ) : deriv (weberE μ) = fun w => (weberE (μ - 1) w - weberE (μ + 1) w) / 2 :=
    funext fun w => (hasDerivAt_weberE μ w).deriv
  have h2 : deriv^[2] (weberE ν) z = ((weberE (ν - 1 - 1) z - weberE (ν - 1 + 1) z) / 2 -
      (weberE (ν + 1 - 1) z - weberE (ν + 1 + 1) z) / 2) / 2 := by
    rw [Function.iterate_succ_apply', Function.iterate_one, hd]
    exact (((hasDerivAt_weberE (ν - 1) z).sub (hasDerivAt_weberE (ν + 1) z)).div_const 2).deriv
  have r₀ := two_mul_self_mul_weberE ν z
  have r₁ := two_mul_self_mul_weberE (ν - 1) z
  have r₂ := two_mul_self_mul_weberE (ν + 1) z
  rw [mul_sub (π : ℂ) ν 1, mul_one, cos_sub_pi] at r₁
  rw [mul_add (π : ℂ) ν 1, mul_one, cos_add_pi] at r₂
  rw [h2, hd]
  simp only [sub_add_cancel, add_sub_cancel_right] at r₁ r₂ ⊢
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  linear_combination (norm := (field_simp; ring)) -(z / 4) * r₁ - z / 4 * r₂ - ν / 2 * r₀

end Complex
