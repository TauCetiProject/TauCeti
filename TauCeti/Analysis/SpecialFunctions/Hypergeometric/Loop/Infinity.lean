/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Loop.Integral
import all TauCeti.Analysis.SpecialFunctions.Hypergeometric.Loop.Integral
public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import TauCeti.Analysis.Calculus.RealCharts
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# A hypergeometric loop based at infinity

The change of variables `v = u / (1 - u)` carries the loop based at `1` in DLMF 15.6.4
to the loop based at infinity in DLMF 15.6.3. The circular part is parametrized by the
image of `u = ρ exp (iθ)`, and its power of `v` uses continuation of the logarithm.
At `θ = π` the image lies at `-ρ / (1 + ρ)` between `-1` and `0`. The continued
argument of `v` there is `π`, and the argument of `1 + v` is zero.

The contour equals the `(0+)` loop for `0 < ρ < 1` and `‖z‖ * ρ < 1`. With an integrable
tail its value is independent of the admissible radius. The multiplied evaluations give Euler's
integral in its cut-plane convergence region and the regularized Gauss series on the open
unit disk. The reciprocal evaluations additionally exclude positive integral `b`.

## References

* NIST Digital Library of Mathematical Functions, §15.6, equations 15.6.3 and 15.6.4.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Real Set
open scoped Topology Interval

namespace Complex

private def infinityRay (a b c z : ℂ) (v : ℝ) : ℂ :=
  (v : ℂ) ^ (b - 1) * (1 + (v : ℂ)) ^ (a - c) * (1 + v - z * v) ^ (-a)

private def infinityCircle (a b c z : ℂ) (ρ θ : ℝ) : ℂ :=
  let u : ℂ := ρ * exp (θ * I)
  let v := u / (1 - u)
  exp (((Real.log ρ : ℂ) + θ * I - log (1 - u)) * (b - 1)) *
    (1 + v) ^ (a - c) * (1 + v - z * v) ^ (-a) * (I * u / (1 - u) ^ 2)

/-- The loop based at infinity in DLMF 15.6.3, obtained from the `(0+)` loop by
`v = u / (1 - u)`. For `0 < ρ < 1` and `‖z‖ * ρ < 1`, this is the intended
continued contour. The outgoing ray carries the monodromy of `v ^ (b - 1)`.
The integrals are totalized when the rays do not converge. -/
def hypergeometricLoopInfinity (a b c z : ℂ) (ρ : ℝ) : ℂ :=
  (exp (2 * π * I * (b - 1)) - 1) *
    (∫ v : ℝ in Ioi (ρ / (1 - ρ)), infinityRay a b c z v) +
    ∫ θ : ℝ in 0..(2 * π), infinityCircle a b c z ρ θ

/-- The real ray and continued circular piece defining the loop at infinity. -/
theorem hypergeometricLoopInfinity_def (a b c z : ℂ) (ρ : ℝ) :
    hypergeometricLoopInfinity a b c z ρ =
      (exp (2 * π * I * (b - 1)) - 1) *
        (∫ v : ℝ in Ioi (ρ / (1 - ρ)),
          (v : ℂ) ^ (b - 1) * (1 + (v : ℂ)) ^ (a - c) * (1 + v - z * v) ^ (-a)) +
      ∫ θ : ℝ in 0..(2 * π),
        let u : ℂ := ρ * exp (θ * I)
        let v := u / (1 - u)
        exp (((Real.log ρ : ℂ) + θ * I - log (1 - u)) * (b - 1)) *
          (1 + v) ^ (a - c) * (1 + v - z * v) ^ (-a) *
            (I * u / (1 - u) ^ 2) := (rfl)

private theorem mobius_factors {u : ℂ} (hu : 1 - u ≠ 0) (z : ℂ) :
    1 + u / (1 - u) = (1 - u)⁻¹ ∧
      1 + u / (1 - u) - z * (u / (1 - u)) = (1 - z * u) * (1 - u)⁻¹ := by
  constructor <;> field_simp <;> ring

private theorem ray_pullback (a b c z : ℂ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    (((1 - u) ^ 2)⁻¹ : ℝ) • infinityRay a b c z (u / (1 - u)) =
      affineSegIntegrand a b (c - b) 1 z u := by
  rw [affineSegIntegrand_unit]
  change _ = (u : ℂ) ^ (b - 1) * (1 - (u : ℂ)) ^ (c - b - 1) * (1 - z * u) ^ (-a)
  have hs : 0 < 1 - u := sub_pos.mpr hu1
  have hs0 : (1 : ℂ) - u ≠ 0 := by exact_mod_cast hs.ne'
  obtain ⟨h1, hq⟩ := mobius_factors hs0 z
  have hp : ((u / (1 - u) : ℝ) : ℂ) ^ (b - 1) =
      exp ((log (u : ℂ) - log (1 - (u : ℂ))) * (b - 1)) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (div_pos hu hs).ne'),
      ← ofReal_log (div_pos hu hs).le, Real.log_div hu.ne' hs.ne']
    simp only [ofReal_sub, ofReal_log hu.le, ofReal_log hs.le, ofReal_one]
  have hpow : ((1 - z * u) * ((1 : ℂ) - u)⁻¹) ^ (-a) =
      (1 - z * u) ^ (-a) * ((1 : ℂ) - u)⁻¹ ^ (-a) := by
    simpa only [ofReal_inv, ofReal_sub, ofReal_one] using
      mul_ofReal_cpow (1 - z * u) (inv_nonneg.mpr hs.le) (-a)
  have ht := exp_sub_log_mul_mul_inv_cpow (b - 1) (a - c) (-a)
    (s := 1 - (u : ℂ)) (q := 1 - z * u) hs0
    (slitPlane_arg_ne_pi (mem_slitPlane_iff.mpr (Or.inl (by simpa using hs))))
    hpow (log (u : ℂ)) 1
  have hexponent : -(b - 1) - (a - c) - -a - 2 = c - b - 1 := by ring
  rw [hexponent] at ht
  unfold infinityRay
  rw [hp]
  push_cast
  rw [hq, h1, real_smul]
  push_cast
  simpa only [one_div, mul_one, one_mul, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hu.ne'),
    mul_comm, mul_left_comm, mul_assoc] using ht

private theorem circle_pullback (a b c z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hzρ : ‖z‖ * ρ < 1) (θ : ℝ) :
    infinityCircle a b c z ρ θ =
      affineCircIntegrand a b (c - b) 1 z ρ θ := by
  change _ = ((ρ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) *
    (1 - ρ * exp (θ * I)) ^ (c - b - 1) *
      (1 - z * (ρ * exp (θ * I))) ^ (-a) * (I * ρ * exp (θ * I))
  let u : ℂ := ρ * exp (θ * I)
  have hun : ‖u‖ = ρ := by
    simp [u, norm_exp_ofReal_mul_I, Real.norm_of_nonneg hρ.le]
  have hs : 0 < (1 - u).re := by
    have := re_le_norm u
    simp only [sub_re, one_re]
    linarith
  have hq : 0 < (1 - z * u).re := by
    have := re_le_norm (z * u)
    rw [norm_mul, hun] at this
    simp only [sub_re, one_re]
    linarith
  have hs0 : 1 - u ≠ 0 := ne_zero_of_re_pos hs
  obtain ⟨h1, h2⟩ := mobius_factors hs0 z
  have hi : 0 < ((1 - u)⁻¹).re := by
    rw [inv_re]
    exact div_pos hs (normSq_pos.mpr hs0)
  have ht := exp_sub_log_mul_mul_inv_cpow (b - 1) (a - c) (-a) hs0
    (slitPlane_arg_ne_pi (mem_slitPlane_iff.mpr (Or.inl hs)))
    (TauCeti.mul_cpow_of_re_pos hq hi (-a)) ((Real.log ρ : ℂ) + θ * I) (I * u)
  have hexponent : -(b - 1) - (a - c) - -a - 2 = c - b - 1 := by ring
  rw [hexponent] at ht
  have he : exp (((Real.log ρ : ℂ) + θ * I) * (b - 1)) =
      (ρ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1)) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hρ.ne'),
      ← ofReal_log hρ.le, ← exp_add]
    congr 1; ring
  -- Use the local name `u` in the unfolded circular integrand to apply the chart identities.
  change exp (((Real.log ρ : ℂ) + θ * I - log (1 - u)) * (b - 1)) *
    (1 + u / (1 - u)) ^ (a - c) *
      (1 + u / (1 - u) - z * (u / (1 - u))) ^ (-a) * (I * u / (1 - u) ^ 2) = _
  rw [h2, h1]
  simpa only [he, u, mul_assoc] using ht

private theorem infinityChart {ρ : ℝ} (hρ1 : ρ < 1) :
    (fun u : ℝ => u / (1 - u)) '' Ioo ρ 1 = Ioi (ρ / (1 - ρ)) ∧
    (∀ u ∈ Ioo ρ 1, HasDerivWithinAt (fun t : ℝ => t / (1 - t))
      ((1 - u) ^ 2)⁻¹ (Ioo ρ 1) u) ∧
    MonotoneOn (fun u : ℝ => u / (1 - u)) (Ioo ρ 1) :=
  ⟨TauCeti.image_div_one_sub_Ioo hρ1,
    fun _ hu => (TauCeti.hasDerivAt_div_one_sub hu.2.ne).hasDerivWithinAt,
    (TauCeti.strictMonoOn_div_one_sub (α := ℝ)).monotoneOn.mono Ioo_subset_Iio_self⟩

private theorem ray_pullback_eqOn (a b c z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    EqOn (fun u : ℝ => (((1 - u) ^ 2)⁻¹ : ℝ) • infinityRay a b c z (u / (1 - u)))
      (affineSegIntegrand a b (c - b) 1 z) (Ioo ρ 1) :=
  fun _ hu => ray_pullback a b c z (hρ.trans hu.1) hu.2

private theorem integral_infinityRay (a b c z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    (∫ v : ℝ in Ioi (ρ / (1 - ρ)), infinityRay a b c z v) =
      ∫ u : ℝ in ρ..1, affineSegIntegrand a b (c - b) 1 z u := by
  obtain ⟨himage, hd, hm⟩ := infinityChart hρ1
  rw [intervalIntegral.integral_of_le hρ1.le, integral_Ioc_eq_integral_Ioo, ← himage]
  rw [integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioo hd hm]
  exact setIntegral_congr_fun measurableSet_Ioo (ray_pullback_eqOn a b c z hρ)

private theorem integrableOn_infinityRay_iff (a b c z : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    IntegrableOn (infinityRay a b c z) (Ioi (ρ / (1 - ρ))) ↔
      IntegrableOn (affineSegIntegrand a b (c - b) 1 z) (Ioo ρ 1) := by
  obtain ⟨himage, hd, hm⟩ := infinityChart hρ1
  rw [← himage,
    integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn measurableSet_Ioo hd hm]
  exact ⟨fun h => h.congr_fun (ray_pullback_eqOn a b c z hρ) measurableSet_Ioo,
    fun h => h.congr_fun (fun _ hu => (ray_pullback_eqOn a b c z hρ hu).symm)
      measurableSet_Ioo⟩

/-- On the cut plane, the real tail of the loop at infinity is absolutely integrable for
`re b < re c`, including when `re b` is nonpositive. -/
theorem integrableOn_hypergeometricLoopInfinity_ray (a b c z : ℂ) (hbc : b.re < c.re)
    (hz : 1 - z ∈ slitPlane) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    IntegrableOn (fun v : ℝ =>
      (v : ℂ) ^ (b - 1) * (1 + (v : ℂ)) ^ (a - c) * (1 + v - z * v) ^ (-a))
      (Ioi (ρ / (1 - ρ))) := by
  -- Use the private ray integrand to match the pullback equation.
  change IntegrableOn (infinityRay a b c z) _
  rw [integrableOn_infinityRay_iff a b c z hρ hρ1, affineSegIntegrand_unit]
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hρ1.le).mp
    (intervalIntegrable_eulerIntegrand_right a hbc hz hρ hρ1.le)

/-- The continued circular piece of the loop at infinity is integrable for every
complex parameter under `0 < ρ < 1` and `‖z‖ * ρ < 1`. These bounds keep
the remaining complex powers on the intended branches. -/
theorem intervalIntegrable_hypergeometricLoopInfinity_circle (a b c z : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hzρ : ‖z‖ * ρ < 1) :
    IntervalIntegrable (fun θ : ℝ =>
      let u : ℂ := ρ * exp (θ * I)
      let v := u / (1 - u)
      exp (((Real.log ρ : ℂ) + θ * I - log (1 - u)) * (b - 1)) *
        (1 + v) ^ (a - c) * (1 + v - z * v) ^ (-a) * (I * u / (1 - u) ^ 2))
      volume 0 (2 * π) := by
  have hc : Continuous (affineCircIntegrand a b (c - b) 1 z ρ) := by
    have heq : affineCircIntegrand a b (c - b) 1 z ρ = fun θ : ℝ =>
        I * affineLogIntegrand a b (c - b) 1 z ((Real.log ρ : ℂ) + θ * I) :=
      funext fun θ => (I_mul_affineLogIntegrand_vertical a b (c - b) 1 z hρ θ).symm
    rw [heq]
    refine continuous_iff_continuousAt.mpr fun θ => ?_
    have hw : (((Real.log ρ : ℂ) + θ * I) : ℂ).re < 0 := by
      simpa using Real.log_neg hρ hρ1
    have hslit : 1 - z * exp ((Real.log ρ : ℂ) + θ * I) ∈ slitPlane := by
      apply (closedBall_one_subset_slitPlane_iff.mpr hzρ)
      rw [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul,
        norm_exp]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
        zero_mul, sub_self, add_zero, Real.exp_log hρ]
      exact le_rfl
    exact continuousAt_const.mul
      ((differentiableAt_affineLogIntegrand a b (c - b) 1 z hw hslit).continuousAt.comp
        (f := fun θ : ℝ => (Real.log ρ : ℂ) + θ * I)
        (by fun_prop : ContinuousAt (fun θ : ℝ => (Real.log ρ : ℂ) + θ * I) θ))
  change IntervalIntegrable (infinityCircle a b c z ρ) volume 0 (2 * π)
  have heq := funext (circle_pullback a b c z hρ hρ1 hzρ)
  rw [heq]
  exact hc.intervalIntegrable _ _

/-- The Möbius substitution `v = u / (1 - u)` identifies the loop based at infinity
with the `(0+)` loop. It requires `0 < ρ < 1` and `‖z‖ * ρ < 1` to control the contour
and branches. Totalization removes the need for ray convergence, while retaining those bounds. -/
theorem hypergeometricLoopInfinity_eq_hypergeometricLoopZero (a b c z : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hzρ : ‖z‖ * ρ < 1) :
    hypergeometricLoopInfinity a b c z ρ = hypergeometricLoopZero a b c z ρ := by
  rw [hypergeometricLoopZero_eq_affineLoopZero]
  unfold hypergeometricLoopInfinity affineLoopZero
  rw [integral_infinityRay a b c z hρ hρ1]
  congr 1
  exact intervalIntegral.integral_congr fun θ _ => circle_pullback a b c z hρ hρ1 hzρ θ

/-- Radius independence under integrability of the tail starting at the smaller radius.
The radius and norm bounds ensure that both continued contours use the intended branches. -/
theorem hypergeometricLoopInfinity_eq_of_integrableOn (a b c z : ℂ) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂ : 0 < ρ₂) (hρ₂1 : ρ₂ < 1)
    (hz₁ : ‖z‖ * ρ₁ < 1) (hz₂ : ‖z‖ * ρ₂ < 1)
    (hint : IntegrableOn (fun v : ℝ =>
      (v : ℂ) ^ (b - 1) * (1 + (v : ℂ)) ^ (a - c) * (1 + v - z * v) ^ (-a))
      (Ioi (min ρ₁ ρ₂ / (1 - min ρ₁ ρ₂)))) :
    hypergeometricLoopInfinity a b c z ρ₁ = hypergeometricLoopInfinity a b c z ρ₂ := by
  rw [hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c z hρ₁ hρ₁1 hz₁,
    hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c z hρ₂ hρ₂1 hz₂]
  apply hypergeometricLoopZero_eq_of_integrableOn a b c z hρ₁ hρ₁1 hρ₂ hρ₂1 hz₁ hz₂
  change IntegrableOn (infinityRay a b c z) _ at hint
  rw [integrableOn_infinityRay_iff a b c z (lt_min hρ₁ hρ₂)
    (min_lt_iff.mpr (Or.inl hρ₁1)), affineSegIntegrand_unit] at hint
  exact hint

/-- On the cut plane `1 - z ∈ slitPlane`, under `b.re < c.re`, the half-line loop is
independent of the radius satisfying `0 < ρ < 1` and `‖z‖ * ρ < 1`. -/
theorem hypergeometricLoopInfinity_eq (a b c z : ℂ) (hbc : b.re < c.re)
    (hz : 1 - z ∈ slitPlane) {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁1 : ρ₁ < 1)
    (hρ₂ : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) (hz₁ : ‖z‖ * ρ₁ < 1) (hz₂ : ‖z‖ * ρ₂ < 1) :
    hypergeometricLoopInfinity a b c z ρ₁ = hypergeometricLoopInfinity a b c z ρ₂ := by
  apply hypergeometricLoopInfinity_eq_of_integrableOn a b c z hρ₁ hρ₁1 hρ₂ hρ₂1 hz₁ hz₂
  exact integrableOn_hypergeometricLoopInfinity_ray a b c z hbc hz (lt_min hρ₁ hρ₂)
    (min_lt_iff.mpr (Or.inl hρ₁1))

/-- Joint holomorphy of the half-line loop along fixed `c - b`, on the open domain
where `1 - z ∈ slitPlane` and `‖z‖ * ρ < 1`, with `0 < ρ < 1`. -/
theorem analyticOnNhd_hypergeometricLoopInfinity {d : ℂ} (hd : 0 < d.re) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ =>
      hypergeometricLoopInfinity p.1 p.2.1 (p.2.1 + d) p.2.2 ρ)
      {p | 1 - p.2.2 ∈ slitPlane ∧ ‖p.2.2‖ * ρ < 1} := by
  intro p hp
  have hopen : IsOpen {q : ℂ × ℂ × ℂ | 1 - q.2.2 ∈ slitPlane ∧ ‖q.2.2‖ * ρ < 1} :=
    (isOpen_slitPlane.preimage (show Continuous (fun q : ℂ × ℂ × ℂ => 1 - q.2.2) by
      fun_prop)).inter
      (isOpen_lt (show Continuous (fun q : ℂ × ℂ × ℂ => ‖q.2.2‖ * ρ) by fun_prop)
        continuous_const)
  exact (analyticOnNhd_hypergeometricLoopZero hd hρ hρ1 p hp).congr (by
    filter_upwards [hopen.mem_nhds hp] with q hq
    exact (hypergeometricLoopInfinity_eq_hypergeometricLoopZero _ _ _ _ hρ hρ1 hq.2).symm)

/-- The half-line loop gives Euler's integral on the cut plane when `0 < b.re < c.re`,
including positive integral `b`, where its multiplier vanishes. -/
theorem hypergeometricLoopInfinity_eq_mul_eulerIntegral (a : ℂ) {b c z : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) (hz : 1 - z ∈ slitPlane) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hzρ : ‖z‖ * ρ < 1) :
    hypergeometricLoopInfinity a b c z ρ =
      2 * π * I * exp (b * π * I) * Gamma (c - b) / Gamma (1 - b) * eulerIntegral a b c z := by
  rw [hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c z hρ hρ1 hzρ]
  exact hypergeometricLoopZero_eq_eulerIntegral a hb hbc hz hρ hρ1 hzρ

/-- Euler's integral in the region `0 < b.re < c.re` on the cut plane, with positive
integral `b` excluded so that the reciprocal DLMF 15.6.3 prefactor is valid. -/
theorem eulerIntegral_eq_mul_hypergeometricLoopInfinity (a : ℂ) {b c z : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) (hb_int : ∀ n : ℕ, b ≠ n + 1) (hz : 1 - z ∈ slitPlane) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hzρ : ‖z‖ * ρ < 1) :
    eulerIntegral a b c z =
      exp (-b * π * I) * Gamma (1 - b) / (2 * π * I * Gamma (c - b)) *
        hypergeometricLoopInfinity a b c z ρ := by
  exact eq_mul_of_eq_mul_hypergeometricLoopZeroFactor hbc hb_int
    (hypergeometricLoopInfinity_eq_mul_eulerIntegral a hb hbc hz hρ hρ1 hzρ)

/-- On the open unit disk the half-line loop equals the regularized Gauss series times its
Gamma and phase factors, including positive integral `b`. The continuation argument is shared
with `Complex.hypergeometricLoopZero_zero` through the zero-loop series identity. -/
theorem hypergeometricLoopInfinity_eq_mul_regularizedGaussHGFun (a : ℂ) {b c z : ℂ}
    (hbc : b.re < c.re) (hz : ‖z‖ < 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    hypergeometricLoopInfinity a b c z ρ =
      2 * π * I * exp (b * π * I) * Gamma (c - b) / Gamma (1 - b) *
        regularizedGaussHGFun a b c z := by
  have hzρ : ‖z‖ * ρ < 1 := by nlinarith [norm_nonneg z]
  rw [hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c z hρ hρ1 hzρ]
  exact hypergeometricLoopZero_eq_mul_regularizedGaussHGFun a hbc hz hρ hρ1

/-- DLMF 15.6.3 on the open unit disk, under `b.re < c.re`, excluding positive integral `b`. -/
theorem regularizedGaussHGFun_eq_mul_hypergeometricLoopInfinity (a : ℂ) {b c z : ℂ}
    (hbc : b.re < c.re) (hb_int : ∀ n : ℕ, b ≠ n + 1) (hz : ‖z‖ < 1) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    regularizedGaussHGFun a b c z =
      exp (-b * π * I) * Gamma (1 - b) / (2 * π * I * Gamma (c - b)) *
        hypergeometricLoopInfinity a b c z ρ := by
  -- Share the prefactor inversion from `Complex.eulerIntegral_eq_hypergeometricLoopZero`.
  exact eq_mul_of_eq_mul_hypergeometricLoopZeroFactor hbc hb_int
    (hypergeometricLoopInfinity_eq_mul_regularizedGaussHGFun a hbc hz hρ hρ1)

/-- At zero argument the half-line loop has the same Gamma evaluation as the `(0+)` loop. -/
@[simp]
theorem hypergeometricLoopInfinity_zero (a : ℂ) {b c : ℂ} (hbc : b.re < c.re) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    hypergeometricLoopInfinity a b c 0 ρ =
      2 * π * I * exp (b * π * I) * Gamma (c - b) / (Gamma (1 - b) * Gamma c) := by
  rw [hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c 0 hρ hρ1 (by simp)]
  exact hypergeometricLoopZero_zero a hbc hρ hρ1

/-- With first parameter zero the half-line loop is independent of `z`; its evaluation
requires no bound on `‖z‖ * ρ`. -/
@[simp]
theorem hypergeometricLoopInfinity_zero_left {b c : ℂ} (hbc : b.re < c.re) (z : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    hypergeometricLoopInfinity 0 b c z ρ =
      2 * π * I * exp (b * π * I) * Gamma (c - b) / (Gamma (1 - b) * Gamma c) := by
  have heq : hypergeometricLoopInfinity 0 b c z ρ = hypergeometricLoopInfinity 0 b c 0 ρ := by
    simp only [hypergeometricLoopInfinity_def, neg_zero, cpow_zero]
  rw [heq, hypergeometricLoopInfinity_zero 0 hbc hρ hρ1]

end Complex
