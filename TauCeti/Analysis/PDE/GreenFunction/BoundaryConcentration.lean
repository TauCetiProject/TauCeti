/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.GreenFunction.Ball

/-!
# Boundary concentration of the Poisson kernel of the ball

For a point approaching the unit sphere from inside the ball, the Poisson kernel has
vanishing integral on every part of the sphere a fixed positive distance from that point.
This is the concentration estimate needed to recover continuous boundary data from the
Poisson integral, once its total mass is known to be one.

The estimate is the elementary far-field half of the approximate-identity argument in
L. C. Evans, *Partial Differential Equations*, Section 2.2.4.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Metric Set Filter

variable {n : ℕ}

/-- Far from a boundary point `z`, the Poisson kernel is bounded by its vanishing
numerator divided by a denominator depending only on the separation distance. -/
theorem ballPoissonKernel_le_of_dist_le_half_of_le_dist {x z : EuclideanSpace ℝ (Fin n)}
    {delta : ℝ} (hdelta : 0 < delta) (hx : ‖x‖ ≤ 1)
    (hnear : dist x z ≤ delta / 2)
    {y : EuclideanSpace ℝ (Fin n)} (hfar : delta ≤ dist y z) :
    ballPoissonKernel n x y ≤
      (1 - ‖x‖ ^ 2) /
        ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
          (delta / 2) ^ n) := by
  by_cases hn : n = 0
  · subst n
    simp [ballPoissonKernel_def]
  have hvol := volume_real_unitBall_pos n
  have hnorm : delta / 2 ≤ ‖x - y‖ := by
    rw [← dist_eq_norm]
    have htri := dist_triangle y x z
    rw [dist_comm y x] at htri
    linarith [dist_comm y z]
  have hpow : (delta / 2) ^ n ≤ ‖x - y‖ ^ n :=
    pow_le_pow_left₀ (by positivity) hnorm _
  have hnum : 0 ≤ 1 - ‖x‖ ^ 2 := by
    nlinarith [norm_nonneg x]
  rw [ballPoissonKernel_def]
  exact div_le_div_of_nonneg_left hnum (by positivity)
    (mul_le_mul_of_nonneg_left hpow (by positivity))

/-- The contribution of integrable boundary data from a fixed positive distance away from `z`
vanishes in the Poisson integral as the pole approaches `z` from inside the ball. -/
theorem tendsto_setIntegral_ballPoissonKernel_mul_away
    (f : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ)
    {z : EuclideanSpace ℝ (Fin n)} (hz : ‖z‖ = 1)
    {delta : ℝ} (hdelta : 0 < delta)
    (hf : IntegrableOn f
      {y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
        delta ≤ dist (y : EuclideanSpace ℝ (Fin n)) z} volume.toSphere) :
    Tendsto (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ y in {y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
          delta ≤ dist (y : EuclideanSpace ℝ (Fin n)) z},
        ballPoissonKernel n x y * f y ∂volume.toSphere)
      (nhdsWithin z (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) (nhds 0) := by
  let s : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    {y | delta ≤ dist (y : EuclideanSpace ℝ (Fin n)) z}
  let B : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    (1 - ‖x‖ ^ 2) /
      ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
        (delta / 2) ^ n)
  let C := ∫ y in s, ‖f y‖ ∂volume.toSphere
  have hs : MeasurableSet s := by
    exact (isClosed_le continuous_const
      (continuous_subtype_val.dist continuous_const)).measurableSet
  have hnear : ∀ᶠ x in nhdsWithin z (ball (0 : EuclideanSpace ℝ (Fin n)) 1),
      dist x z ≤ delta / 2 := by
    have hmem : ∀ᶠ x in nhds z, x ∈ ball z (delta / 2) :=
      Metric.ball_mem_nhds z (half_pos hdelta)
    filter_upwards [hmem.filter_mono nhdsWithin_le_nhds] with x hx
    exact (mem_ball.mp hx).le
  have hinside : ∀ᶠ x in nhdsWithin z (ball (0 : EuclideanSpace ℝ (Fin n)) 1),
      ‖x‖ < 1 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mem_ball_zero_iff.mp hx
  have hlim : Tendsto (fun x : EuclideanSpace ℝ (Fin n) => B x * C)
      (nhdsWithin z (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) (nhds 0) := by
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) => B x * C) := by
      dsimp [B]
      fun_prop
    have hval : B z * C = 0 := by simp [B, hz]
    have ht := hcont.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : nhdsWithin z (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≤ nhds z)
    rwa [hval] at ht
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hinside, hnear] with x hx hnearx
  let nu : Measure (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := volume.toSphere
  have hg : Integrable (fun y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      B x * ‖f y‖) (nu.restrict s) := hf.norm.const_mul (B x)
  have hbound : ∀ᵐ (y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ∂(nu.restrict s),
      ‖ballPoissonKernel n x y * f y‖ ≤ B x * ‖f y‖ := by
    filter_upwards [ae_restrict_mem hs] with y hy
    have hK := (ballPoissonKernel_pos_on_sphere x hx y).le
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hK]
    exact mul_le_mul_of_nonneg_right
      (ballPoissonKernel_le_of_dist_le_half_of_le_dist hdelta hx.le hnearx hy)
      (norm_nonneg _)
  have hmeas : AEStronglyMeasurable
      (fun y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        ballPoissonKernel n x y * f y) (nu.restrict s) :=
    ((continuous_ballPoissonKernel_on_sphere x hx.ne).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self).mul hf.aestronglyMeasurable
  have hweighted : Integrable
      (fun y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        ballPoissonKernel n x y * f y) (nu.restrict s) :=
    Integrable.mono' hg hmeas hbound
  have h := (norm_integral_le_integral_norm _).trans
    (integral_mono_ae hweighted.norm hg hbound)
  simpa only [integral_const_mul] using h

/-- The mass of the unit-ball Poisson kernel outside a fixed boundary neighbourhood
vanishes as the pole approaches the boundary point through the open ball. -/
theorem tendsto_setIntegral_ballPoissonKernel_away {z : EuclideanSpace ℝ (Fin n)}
    (hz : ‖z‖ = 1) {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ y in {y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
          delta ≤ dist (y : EuclideanSpace ℝ (Fin n)) z},
        ballPoissonKernel n x y ∂volume.toSphere)
      (nhdsWithin z (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) (nhds 0) := by
  have h := tendsto_setIntegral_ballPoissonKernel_mul_away
    (fun _ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => (1 : ℝ)) hz hdelta
    ((integrable_const _).integrableOn)
  simpa only [mul_one] using h

/-- The far-field Poisson integral of continuous boundary data vanishes as the pole
approaches the boundary point through the open ball. -/
theorem tendsto_setIntegral_ballPoissonKernel_mul_away_of_continuous
    (f : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ) (hf : Continuous f)
    {z : EuclideanSpace ℝ (Fin n)} (hz : ‖z‖ = 1)
    {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ y in {y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
          delta ≤ dist (y : EuclideanSpace ℝ (Fin n)) z},
        ballPoissonKernel n x y * f y ∂volume.toSphere)
      (nhdsWithin z (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) (nhds 0) := by
  exact tendsto_setIntegral_ballPoissonKernel_mul_away f hz hdelta
    (by
      have hint : Integrable f volume.toSphere := by
        simpa only [integrableOn_univ] using
          hf.continuousOn.integrableOn_compact isCompact_univ
      exact hint.integrableOn)

end TauCeti

end
