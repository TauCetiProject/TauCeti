/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import TauCeti.Analysis.Sobolev.W1p.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Scaling
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Mean oscillation of the weak gradient on balls

Let `u ∈ H¹(Ω)` on an open set `Ω ⊆ ℝ^{n+1}`, and write `B_t = ball z t` for balls inside `Ω`.
This file collects the elementary facts about the square mean oscillation
`ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²` of the weak gradient that Campanato's method uses, together
with their conversion into bounds on the mean oscillation and the averages of `∇u` over closed
balls, the form taken by Campanato's theorem
(`TauCeti.MeasureTheory.holderOnWith_preciseRepresentative_of_setAverage_norm_sub_le`). None of
them uses an equation for `u`.

## Main declarations

All in the `TauCeti.W1p` namespace.

* `setIntegral_norm_gradient_sub_setAverage_sq_le`: `ψ(t) ≤ ∫_{B_t} ‖∇u‖²`.
* `monotoneOn_setIntegral_norm_gradient_sub_setAverage_sq`: `ψ` is nondecreasing.
* `integrableOn_closedBall_gradient`: `∇u` is integrable on closed balls inside `Ω`.
* `setAverage_closedBall_norm_gradient_sub_le` and
  `setAverage_closedBall_norm_gradient_sub_le_mul_rpow`: power decay of `ψ` bounds the mean
  oscillation of `∇u` on closed balls.
* `sq_norm_setAverage_closedBall_gradient_mul_le` and
  `norm_setAverage_closedBall_gradient_le_div`: the `L²` mass of `∇u` on a ball bounds its
  average over the closed ball.
-/

public section

noncomputable section

open MeasureTheory Metric Module Set TopologicalSpace

namespace TauCeti

variable {n : ℕ}

/-- The square mean oscillation of the gradient on `B_t` is at most its `L²` mass on `B_t`. -/
theorem W1p.setIntegral_norm_gradient_sub_setAverage_sq_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {t : ℝ} (hball : ball z t ⊆ Omega) :
    ∫ x in ball z t, ‖W1p.gradient u x - ⨍ y in ball z t, W1p.gradient u y‖ ^ 2 ≤
      ∫ x in ball z t, ‖W1p.gradient u x‖ ^ 2 := by
  have h := setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq measure_ball_lt_top.ne
    ((Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two hball measure_ball_lt_top.ne)
    ((Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset hball
      measure_ball_lt_top.ne 0)
  simpa only [sub_zero] using h

/-- The square mean oscillation `∫_{B_t} ‖∇u - (∇u)_{B_t}‖²` is nondecreasing in the radius,
since the average is the best constant in square mean. -/
theorem W1p.monotoneOn_setIntegral_norm_gradient_sub_setAverage_sq
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {R : ℝ} (hball : ball z R ⊆ Omega) :
    MonotoneOn
      (fun t => ∫ x in ball z t, ‖W1p.gradient u x - ⨍ y in ball z t, W1p.gradient u y‖ ^ 2)
      (Ioc 0 R) := fun r hr t ht hst => by
  have hr' := (ball_subset_ball hr.2).trans hball
  have ht' := (ball_subset_ball ht.2).trans hball
  exact (setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq measure_ball_lt_top.ne
    ((Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two hr' measure_ball_lt_top.ne)
    ((Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset hr'
      measure_ball_lt_top.ne _)).trans
    (setIntegral_mono_set ((Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset ht'
      measure_ball_lt_top.ne _) (ae_of_all _ fun _ => by positivity)
      (ball_subset_ball hst).eventuallySubset)

/-- The gradient is integrable on `closedBall z t` whenever `ball z R ⊆ Ω` and `t ≤ R`; for
`t = R` because `closedBall z R` and `ball z R` differ by a null set. -/
theorem W1p.integrableOn_closedBall_gradient {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (u : W1p volume Omega 2) {z : EuclideanSpace ℝ (Fin (n + 1))} {R t : ℝ}
    (hball : ball z R ⊆ Omega) (ht : t ≤ R) :
    IntegrableOn (W1p.gradient u) (closedBall z t) := by
  rcases ht.lt_or_eq with ht | rfl
  · exact (Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two
      ((closedBall_subset_ball ht).trans hball) measure_closedBall_lt_top.ne
  · exact ((Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two hball
      measure_ball_lt_top.ne).congr_set_ae (volume.addHaar_closedBall_ae_eq_ball z t)

/-- **Jensen's inequality for the mean oscillation.** The squared mean oscillation of `∇u` on
`closedBall z t`, times the volume of the ball, is at most the square mean oscillation
`∫_{B_t} ‖∇u - (∇u)_{B_t}‖²`. -/
private theorem W1p.sq_setAverage_closedBall_norm_gradient_sub_mul_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {t : ℝ} (hball : ball z t ⊆ Omega) (ht : 0 < t) :
    (⨍ y in closedBall z t, ‖W1p.gradient u y - ⨍ w in closedBall z t, W1p.gradient u w‖) ^ 2 *
        volume.real (ball z t) ≤
      ∫ x in ball z t, ‖W1p.gradient u x - ⨍ y in ball z t, W1p.gradient u y‖ ^ 2 := by
  rw [volume.restrict_closedBall_eq_restrict_ball z t]
  have hpos := measureReal_ball_pos volume z ht
  have hJ := sq_setAverage_norm_le_setAverage_norm_sq
    ((Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset hball measure_ball_lt_top.ne
      (⨍ y in ball z t, W1p.gradient u y))
  have hav : ⨍ x in ball z t, ‖W1p.gradient u x - ⨍ y in ball z t, W1p.gradient u y‖ ^ 2 =
      (volume.real (ball z t))⁻¹ *
        ∫ x in ball z t, ‖W1p.gradient u x - ⨍ y in ball z t, W1p.gradient u y‖ ^ 2 := by
    rw [setAverage_eq, smul_eq_mul]
  rw [hav] at hJ
  calc _ ≤ _ := mul_le_mul_of_nonneg_right hJ hpos.le
    _ = _ := by field_simp

/-- The squared norm of the average of `∇u` over `closedBall z t`, times the volume of the ball,
is at most `∫_{B_t} ‖∇u‖²`. -/
theorem W1p.sq_norm_setAverage_closedBall_gradient_mul_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {t : ℝ} (hball : ball z t ⊆ Omega) :
    ‖⨍ y in closedBall z t, W1p.gradient u y‖ ^ 2 * volume.real (ball z t) ≤
      ∫ x in ball z t, ‖W1p.gradient u x‖ ^ 2 := by
  rw [volume.restrict_closedBall_eq_restrict_ball z t]
  have h := setIntegral_norm_sub_sq_eq_setIntegral_norm_sub_setAverage_sq_add
    measure_ball_lt_top.ne
    ((Lp.memLp (W1p.gradient u)).integrableOn_of_subset one_le_two hball measure_ball_lt_top.ne)
    ((Lp.memLp (W1p.gradient u)).integrableOn_norm_sub_sq_of_subset hball
      measure_ball_lt_top.ne 0)
  simp only [sub_zero] at h
  rw [h, mul_comm]
  exact le_add_of_nonneg_left (setIntegral_nonneg measurableSet_ball fun _ _ => by positivity)

/-- **Mean oscillation from square mean oscillation.** If
`∫_{B_r} ‖∇u - (∇u)_{B_r}‖² ≤ C V (r / R)^{n+1} (r / R)^{2κ}`, then the mean oscillation of `∇u`
on `closedBall z r` is at most `√(C V / (ω R^{n+1})) R^{-κ} r^κ`, where `ω` is the volume of the
unit ball. -/
theorem W1p.setAverage_closedBall_norm_gradient_sub_le
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {r R C V κ : ℝ} (hball : ball z r ⊆ Omega) (hr : 0 < r)
    (hR : 0 < R)
    (hψ : ∫ x in ball z r, ‖W1p.gradient u x - ⨍ y in ball z r, W1p.gradient u y‖ ^ 2 ≤
      C * V * ((r / R) ^ (n + 1) * (r / R) ^ (2 * κ))) :
    ⨍ y in closedBall z r, ‖W1p.gradient u y - ⨍ w in closedBall z r, W1p.gradient u w‖ ≤
      √(C * (V / (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * R ^ (n + 1)))) *
        R ^ (-κ) * r ^ κ := by
  have hω := measureReal_ball_pos volume (0 : EuclideanSpace ℝ (Fin (n + 1))) one_pos
  have h1 := (W1p.sq_setAverage_closedBall_norm_gradient_sub_mul_le u hball hr).trans hψ
  rw [Measure.addHaar_real_ball_of_pos _ z hr, finrank_euclideanSpace_fin,
    mul_comm _ (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))] at h1
  have hsq : ((r / R) ^ κ) ^ 2 = (r / R) ^ (2 * κ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    ring_nf
  have h2 : C * V * ((r / R) ^ (n + 1) * (r / R) ^ (2 * κ)) =
      C * (V / (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * R ^ (n + 1))) *
        ((r / R) ^ κ) ^ 2 *
        (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * r ^ (n + 1)) := by
    rw [hsq, div_pow]
    field_simp
  have h3 := le_of_mul_le_mul_right (h1.trans_eq h2) (by positivity)
  have h4 : (⨍ y in closedBall z r,
      ‖W1p.gradient u y - ⨍ w in closedBall z r, W1p.gradient u w‖) ≤
        √(C * (V / (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * R ^ (n + 1)))) *
          (r / R) ^ κ := by
    rw [← Real.sqrt_sq (average_nonneg fun _ => norm_nonneg _),
      ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (r / R) ^ κ), ← Real.sqrt_mul' _ (by positivity)]
    exact Real.sqrt_le_sqrt h3
  refine h4.trans_eq ?_
  rw [Real.div_rpow_eq_rpow_neg_mul_rpow hr.le hR]
  ring

/-- If `∫_{B_t} ‖∇u - (∇u)_{B_t}‖² ≤ C (R^{(n+1)/2+a} Q)² (t / R)^{n+1+2a}`, then the mean
oscillation of `∇u` on `closedBall z t` is at most `√(C / ω) Q t^a`, where `ω` is the volume of
the unit ball. -/
theorem W1p.setAverage_closedBall_norm_gradient_sub_le_mul_rpow
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {t R Q C a : ℝ} (hball : ball z t ⊆ Omega) (ht : 0 < t)
    (hR : 0 < R) (hQ : 0 ≤ Q)
    (hψ : ∫ x in ball z t, ‖W1p.gradient u x - ⨍ y in ball z t, W1p.gradient u y‖ ^ 2 ≤
      C * (R ^ (((n : ℝ) + 1) / 2 + a) * Q) ^ 2 * (t / R) ^ (2 * a + ((n : ℝ) + 1))) :
    ⨍ y in closedBall z t, ‖W1p.gradient u y - ⨍ w in closedBall z t, W1p.gradient u w‖ ≤
      √(C / volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) * Q * t ^ a := by
  set ω := volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  have hω : 0 < ω := measureReal_ball_pos volume _ one_pos
  have hV : (R ^ (((n : ℝ) + 1) / 2 + a) * Q) ^ 2 = R ^ (n + 1) * (R ^ a * Q) ^ 2 := by
    rw [Real.rpow_div_two_add_mul_sq Q hR]
    norm_cast
  refine (W1p.setAverage_closedBall_norm_gradient_sub_le u hball ht hR (C := C) (κ := a)
    (V := (R ^ (((n : ℝ) + 1) / 2 + a) * Q) ^ 2) (hψ.trans_eq ?_)).trans_eq ?_
  · rw [← Real.rpow_natCast (t / R) (n + 1), ← Real.rpow_add (div_pos ht hR)]
    congr 2
    push_cast
    ring
  · have hRa : R ^ a ≠ 0 := (Real.rpow_pos_of_pos hR a).ne'
    have hC : C * (R ^ (n + 1) * (R ^ a * Q) ^ 2 / (ω * R ^ (n + 1))) =
        C / ω * (R ^ a * Q) ^ 2 := by
      field_simp
    rw [hV, hC, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (by positivity), Real.rpow_neg hR.le]
    field_simp

/-- If `∫_{B_{θR}} ‖∇u‖² ≤ R^{n+1} (R^a Q)²`, then the average of `∇u` over `closedBall z (θ R)`
is at most `R^a Q / √(ω θ^{n+1})`, where `ω` is the volume of the unit ball. -/
theorem W1p.norm_setAverage_closedBall_gradient_le_div
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} (u : W1p volume Omega 2)
    {z : EuclideanSpace ℝ (Fin (n + 1))} {θ R Q a : ℝ} (hball : ball z (θ * R) ⊆ Omega)
    (hθ : 0 < θ) (hR : 0 < R) (hQ : 0 ≤ Q)
    (hΦ : ∫ x in ball z (θ * R), ‖W1p.gradient u x‖ ^ 2 ≤ R ^ (n + 1) * (R ^ a * Q) ^ 2) :
    ‖⨍ y in closedBall z (θ * R), W1p.gradient u y‖ ≤
      R ^ a * Q / √(volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) * θ ^ (n + 1)) := by
  have hω := measureReal_ball_pos volume (0 : EuclideanSpace ℝ (Fin (n + 1))) one_pos
  have h := (W1p.sq_norm_setAverage_closedBall_gradient_mul_le u hball).trans hΦ
  rw [Measure.addHaar_real_ball_of_pos _ z (by positivity), finrank_euclideanSpace_fin,
    mul_comm _ (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)), mul_pow] at h
  have h' : ‖⨍ y in closedBall z (θ * R), W1p.gradient u y‖ ^ 2 ≤
      (R ^ a * Q) ^ 2 / (volume.real (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) *
        θ ^ (n + 1)) := by
    rw [le_div_iff₀ (by positivity)]
    have hRn : 0 < R ^ (n + 1) := by positivity
    nlinarith
  rw [le_div_iff₀ (by positivity), ← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_mul
    (sq_nonneg _), ← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ R ^ a * Q)]
  refine Real.sqrt_le_sqrt ?_
  rwa [← le_div_iff₀ (by positivity)]

end TauCeti
