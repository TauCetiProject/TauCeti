/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.PoissonIntegral.Ball
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Analyticity of the Poisson integral of the unit ball

This file proves that the Poisson integral

`P[g](x) = ∫_S K(x, y) g(y) dσ(y)`,  `K(x, y) = (1 - ‖x‖²) / (n ωₙ ‖x - y‖ⁿ)`,

of integrable boundary data `g` on the unit sphere of `ℝⁿ` is real analytic in the open unit ball
(`TauCeti.analyticOnNhd_ballPoissonIntegral`).

The kernel extends holomorphically to complex arguments: with `q(w) = ∑ i, w i ^ 2`, the function

`(z, w) ↦ (1 - q z) / (n ωₙ q(z - w) ^ (n / 2))`

on `ℂⁿ × ℂⁿ` is holomorphic near every pair `(x, y)` of distinct real points, since there
`q(x - y) = ‖x - y‖²` is a positive real number, at which the principal power is holomorphic. It
restricts to `K` on real points. Integrating over the sphere preserves holomorphy in `z`
(`TauCeti.analyticAt_integral_smul`), so `P[g]` is the restriction to `ℝⁿ` of a holomorphic
function on a neighbourhood of the ball in `ℂⁿ`, hence real analytic there.

## Main declarations

* `TauCeti.analyticOnNhd_ballPoissonIntegral`: the Poisson integral of integrable boundary data is
  real analytic in the open unit ball.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.2.3, Theorem 10.
* S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, 2nd ed., Chapter 1.
-/

public section

noncomputable section

open Complex InnerProductSpace MeasureTheory Metric Set Filter

namespace TauCeti

variable {n : ℕ}

/-! ### The complexified Poisson kernel -/

/-- The inclusion of `ℝⁿ` into `ℂⁿ`, coordinatewise. -/
private def complexify (n : ℕ) : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℂ) :=
  (ContinuousLinearMap.piMap fun _ ↦ ofRealCLM).comp
    (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap

private theorem complexify_apply (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    complexify n x i = x i := by
  simp [complexify]

/-- The complex quadratic form `q(w) = ∑ i, w i ^ 2` on `ℂⁿ`, which restricts to `‖x‖²` on
`ℝⁿ`. -/
private def sumSq (w : Fin n → ℂ) : ℂ :=
  ∑ i, w i ^ 2

private theorem sumSq_complexify (x : EuclideanSpace ℝ (Fin n)) :
    sumSq (complexify n x) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  simp [sumSq, complexify_apply, EuclideanSpace.real_norm_sq_eq]

private theorem analyticAt_sumSq (w : Fin n → ℂ) : AnalyticAt ℂ sumSq w :=
  Finset.analyticAt_fun_sum _ fun i _ ↦ (analyticAt_pi_iff.1 analyticAt_id i).pow 2

/-- The holomorphic extension of the Poisson kernel of the unit ball to `ℂⁿ × ℂⁿ`. -/
private def complexPoissonKernel (n : ℕ) (p : (Fin n → ℂ) × (Fin n → ℂ)) : ℂ :=
  (1 - sumSq p.1) / ((n : ℂ) * (volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) : ℂ) *
    sumSq (p.1 - p.2) ^ ((n : ℂ) / 2))

/-- On real points the complexified kernel is the Poisson kernel. -/
private theorem complexPoissonKernel_complexify (x y : EuclideanSpace ℝ (Fin n)) :
    complexPoissonKernel n (complexify n x, complexify n y) = ballPoissonKernel n x y := by
  have hpos : 0 ≤ ‖x - y‖ := norm_nonneg _
  -- The exponent `n / 2` is real, so the complex power of a positive real is a real power.
  have hexp : ((n : ℂ) / 2) = (((n : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
  have hpow : ((‖x - y‖ ^ 2 : ℝ) : ℂ) ^ ((n : ℂ) / 2) = ((‖x - y‖ ^ n : ℝ) : ℂ) := by
    rw [hexp,
      ← ofReal_cpow (by positivity), ← Real.rpow_natCast ‖x - y‖ 2, ← Real.rpow_mul hpos,
      ← Real.rpow_natCast]
    congr 2
    ring
  rw [complexPoissonKernel, ← map_sub, sumSq_complexify, sumSq_complexify, hpow,
    ballPoissonKernel_def]
  norm_cast

/-- The complexified kernel is holomorphic near every pair of distinct real points. -/
private theorem analyticAt_complexPoissonKernel (hn : n ≠ 0) {x y : EuclideanSpace ℝ (Fin n)}
    (hxy : x ≠ y) :
    AnalyticAt ℂ (complexPoissonKernel n) (complexify n x, complexify n y) := by
  have hq : sumSq (complexify n x - complexify n y) = ((‖x - y‖ ^ 2 : ℝ) : ℂ) := by
    rw [← map_sub, sumSq_complexify]
  have hq₀ : 0 < ‖x - y‖ ^ 2 := by
    have := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    positivity
  have hdiff : AnalyticAt ℂ (fun p : (Fin n → ℂ) × (Fin n → ℂ) ↦ sumSq (p.1 - p.2))
      (complexify n x, complexify n y) :=
    (analyticAt_sumSq _).comp (analyticAt_fst.sub analyticAt_snd)
  refine (analyticAt_const.sub ((analyticAt_sumSq _).comp analyticAt_fst)).div
    (analyticAt_const.mul (hdiff.cpow analyticAt_const ?_)) ?_
  · simpa [hq] using ofReal_mem_slitPlane.mpr hq₀
  · simp only [hq, ne_eq, mul_eq_zero, Nat.cast_eq_zero, hn, ofReal_eq_zero, false_or,
      cpow_eq_zero_iff, not_or, not_and, not_not]
    exact ⟨(volume_real_unitBall_pos n).ne', fun h ↦ absurd h hq₀.ne'⟩

/-! ### Analyticity of the Poisson integral -/

/-- **The Poisson integral is real analytic.** For integrable boundary data `g` on the unit
sphere of `ℝⁿ`, the Poisson integral `P[g]` is real analytic in the open unit ball. -/
theorem analyticOnNhd_ballPoissonIntegral {g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ}
    (hg : Integrable g volume.toSphere) :
    AnalyticOnNhd ℝ (ballPoissonIntegral g) (ball 0 1) := by
  intro x hx
  rcases eq_or_ne n 0 with rfl | hn
  · -- `ℝ⁰` is a point, on which every function is analytic.
    exact analyticAt_const.congr
      (Eventually.of_forall fun y ↦ congrArg (ballPoissonIntegral g) (Subsingleton.elim x y))
  have hxS : ∀ y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1, x ≠ y := fun y hxy ↦ by
    rw [mem_ball_zero_iff, hxy, norm_eq_of_mem_sphere y] at hx
    exact lt_irrefl _ hx
  -- The holomorphic extension `F` of the Poisson integral to complex arguments.
  set F : (Fin n → ℂ) → ℂ := fun z ↦
    ∫ y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      (g y : ℂ) • complexPoissonKernel n (z, complexify n y) ∂volume.toSphere
  have hF : AnalyticAt ℂ F (complexify n x) := by
    refine analyticAt_integral_smul ((isCompact_sphere 0 1).image (complexify n).continuous)
      ((complexify n).continuous.comp continuous_subtype_val)
      (fun y ↦ mem_image_of_mem _ y.2) ?_ hg.ofReal
    rintro _ ⟨y, hy, rfl⟩
    exact analyticAt_complexPoissonKernel hn (hxS ⟨y, hy⟩)
  -- On real points, `F` is the Poisson integral.
  have hFP : ballPoissonIntegral g = fun x' ↦ (F (complexify n x')).re := by
    ext x'
    simp only [F, complexPoissonKernel_complexify, smul_eq_mul, ← ofReal_mul,
      ballPoissonIntegral_def, mul_comm (g _)]
    rw [integral_complex_ofReal, ofReal_re]
  rw [hFP]
  exact (reCLM.analyticAt _).comp (hF.restrictScalars.comp ((complexify n).analyticAt x))

end TauCeti
