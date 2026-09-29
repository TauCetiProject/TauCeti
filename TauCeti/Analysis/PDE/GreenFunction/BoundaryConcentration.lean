/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.GreenFunction.Ball
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

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

/-- The Poisson kernel is integrable over any subset of the sphere for a pole
strictly inside the ball. -/
theorem integrableOn_ballPoissonKernel
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ < 1)
    (s : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :
    IntegrableOn (fun y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      ballPoissonKernel n x y) s volume.toSphere := by
  have hint : Integrable (fun y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      ballPoissonKernel n x y) volume.toSphere := by
    simpa only [integrableOn_univ] using
      (continuous_ballPoissonKernel_on_sphere x hx).continuousOn.integrableOn_compact
        isCompact_univ
  exact hint.integrableOn

/-- Far from a boundary point `z`, the Poisson kernel is bounded by its vanishing
numerator divided by a denominator depending only on the separation distance. -/
theorem ballPoissonKernel_le_of_dist_le_half {x z : EuclideanSpace ℝ (Fin n)}
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
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
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

/-- The mass of the unit-ball Poisson kernel outside a fixed boundary neighbourhood
vanishes as the pole approaches the boundary point through the open ball. -/
theorem tendsto_setIntegral_ballPoissonKernel_away {z : EuclideanSpace ℝ (Fin n)}
    (hz : ‖z‖ = 1) {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ y in {y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
          delta ≤ dist (y : EuclideanSpace ℝ (Fin n)) z},
        ballPoissonKernel n x y ∂volume.toSphere)
      (nhdsWithin z (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) (nhds 0) := by
  let s : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    {y | delta ≤ dist (y : EuclideanSpace ℝ (Fin n)) z}
  have hdist : Continuous (fun y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      dist (y : EuclideanSpace ℝ (Fin n)) z) :=
    continuous_subtype_val.dist continuous_const
  have hs : MeasurableSet s :=
    (isClosed_le continuous_const hdist).measurableSet
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
  have hlim : Tendsto (fun x : EuclideanSpace ℝ (Fin n) =>
      (volume.toSphere s).toReal * ((1 - ‖x‖ ^ 2) /
        ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
          (delta / 2) ^ n)))
      (nhdsWithin z (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) (nhds 0) := by
    have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
        (volume.toSphere s).toReal * ((1 - ‖x‖ ^ 2) /
          ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
            (delta / 2) ^ n))) := by fun_prop
    have hval : (volume.toSphere s).toReal * ((1 - ‖z‖ ^ 2) /
        ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
          (delta / 2) ^ n)) = 0 := by simp [hz]
    have ht := hcont.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : nhdsWithin z (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≤ nhds z)
    rwa [hval] at ht
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hinside] with x hx
    exact setIntegral_nonneg hs (fun y hy =>
      (ballPoissonKernel_pos hx (by
        intro h
        have hy' : ‖(y : EuclideanSpace ℝ (Fin n))‖ = 1 := norm_eq_of_mem_sphere y
        rw [h] at hx
        linarith)).le)
  · filter_upwards [hinside, hnear] with x hx hnearx
    have hint := integrableOn_ballPoissonKernel x hx s
    have hconst : IntegrableOn
        (fun _y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          (1 - ‖x‖ ^ 2) /
            ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
              (delta / 2) ^ n)) s volume.toSphere := (integrable_const _).integrableOn
    calc
      (∫ y in s, ballPoissonKernel n x y ∂volume.toSphere) ≤
          ∫ _y in s, (1 - ‖x‖ ^ 2) /
            ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
              (delta / 2) ^ n) ∂volume.toSphere := by
              apply setIntegral_mono_on hint hconst hs
              intro y hy
              exact ballPoissonKernel_le_of_dist_le_half hdelta hx.le hnearx hy
      _ = (volume.toSphere s).toReal * ((1 - ‖x‖ ^ 2) /
          ((n : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
            (delta / 2) ^ n)) := by
          simp only [setIntegral_const, smul_eq_mul, measureReal_def]

/-- The contribution of boundary data from a fixed positive distance away from `z`
vanishes in the Poisson integral as the pole approaches `z` from inside the ball. -/
theorem tendsto_setIntegral_ballPoissonKernel_mul_away
    (f : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ) (hf : Continuous f)
    {z : EuclideanSpace ℝ (Fin n)} (hz : ‖z‖ = 1)
    {delta : ℝ} (hdelta : 0 < delta) :
    Tendsto (fun x : EuclideanSpace ℝ (Fin n) =>
      ∫ y in {y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 |
          delta ≤ dist (y : EuclideanSpace ℝ (Fin n)) z},
        ballPoissonKernel n x y * f y ∂volume.toSphere)
      (nhdsWithin z (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) (nhds 0) := by
  let s : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    {y | delta ≤ dist (y : EuclideanSpace ℝ (Fin n)) z}
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hinside : ∀ᶠ x in nhdsWithin z (ball (0 : EuclideanSpace ℝ (Fin n)) 1),
      ‖x‖ < 1 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mem_ball_zero_iff.mp hx
  have hmass := tendsto_setIntegral_ballPoissonKernel_away hz hdelta
  have hlim : Tendsto (fun x : EuclideanSpace ℝ (Fin n) =>
      C * ∫ y in s, ballPoissonKernel n x y ∂volume.toSphere)
      (nhdsWithin z (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) (nhds 0) := by
    simpa only [mul_zero] using hmass.const_mul C
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hinside] with x hx
  have hK : ∀ y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      0 ≤ ballPoissonKernel n x y := by
    intro y
    apply (ballPoissonKernel_pos hx ?_).le
    intro h
    have hy : ‖(y : EuclideanSpace ℝ (Fin n))‖ = 1 := norm_eq_of_mem_sphere y
    rw [h] at hx
    linarith
  let nu : Measure (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := volume.toSphere
  have hg : Integrable (fun y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      C * ballPoissonKernel n x y) (nu.restrict s) :=
    (integrableOn_ballPoissonKernel x hx s).const_mul C
  have hbound : ∀ᵐ (y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ∂(nu.restrict s),
      ‖ballPoissonKernel n x y * f y‖ ≤ C * ballPoissonKernel n x y := by
    filter_upwards [] with y
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hK y)]
    simpa only [mul_comm C] using
      mul_le_mul_of_nonneg_left (hC y (mem_univ _)) (hK y)
  have h := norm_integral_le_of_norm_le hg hbound
  simpa only [integral_const_mul] using h

end TauCeti

end
