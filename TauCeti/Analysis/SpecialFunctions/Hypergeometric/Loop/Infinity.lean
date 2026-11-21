/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Loop.Integral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Algebra.Field.LinearFractional
import all TauCeti.Analysis.SpecialFunctions.Hypergeometric.Loop.Integral
import TauCeti.Analysis.Complex.Basic
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

The Möbius substitution maps the `(0+)` contour to the contour based at infinity; their
integral values agree for `0 < ρ < 1` and `‖z‖ * ρ < 1`. With an integrable tail the value
is independent of the admissible radius. The multiplied evaluations give Euler's
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

/-- The real-ray kernel of the hypergeometric loop based at infinity. -/
def hypergeometricLoopInfinityRay (a b c z : ℂ) (v : ℝ) : ℂ :=
  (v : ℂ) ^ (b - 1) * (1 + (v : ℂ)) ^ (a - c) * (1 + v - z * v) ^ (-a)

/-- The circular kernel with the continued logarithm of the Möbius coordinate. -/
def hypergeometricLoopInfinityCircle (a b c z : ℂ) (ρ θ : ℝ) : ℂ :=
  let u := circleMap 0 ρ θ
  let v := u / (1 - u)
  exp (((Real.log ρ : ℂ) + θ * I - log (1 - u)) * (b - 1)) *
    (1 + v) ^ (a - c) * (1 + v - z * v) ^ (-a) *
      (deriv (circleMap 0 ρ) θ / (1 - u) ^ 2)

/-- Evaluation of the real-ray kernel. -/
theorem hypergeometricLoopInfinityRay_def (a b c z : ℂ) (v : ℝ) :
    hypergeometricLoopInfinityRay a b c z v =
      (v : ℂ) ^ (b - 1) * (1 + (v : ℂ)) ^ (a - c) * (1 + v - z * v) ^ (-a) := (rfl)

/-- Evaluation of the continued circular kernel. -/
theorem hypergeometricLoopInfinityCircle_def (a b c z : ℂ) (ρ θ : ℝ) :
    hypergeometricLoopInfinityCircle a b c z ρ θ =
      let u : ℂ := ρ * exp (θ * I)
      let v := u / (1 - u)
      exp (((Real.log ρ : ℂ) + θ * I - log (1 - u)) * (b - 1)) *
        (1 + v) ^ (a - c) * (1 + v - z * v) ^ (-a) * (I * u / (1 - u) ^ 2) := by
  simp only [hypergeometricLoopInfinityCircle, deriv_circleMap, circleMap_zero, mul_comm I]

/-- The loop based at infinity in DLMF 15.6.3, obtained from the `(0+)` loop by
`v = u / (1 - u)`. For `0 < ρ < 1` and `‖z‖ * ρ < 1`, this is the intended
continued contour. The outgoing ray carries the monodromy of `v ^ (b - 1)`.
The integrals are totalized when the rays do not converge. -/
def hypergeometricLoopInfinity (a b c z : ℂ) (ρ : ℝ) : ℂ :=
  (exp (2 * π * I * (b - 1)) - 1) *
    (∫ v : ℝ in Ioi (ρ / (1 - ρ)), hypergeometricLoopInfinityRay a b c z v) +
    ∫ θ : ℝ in 0..(2 * π), hypergeometricLoopInfinityCircle a b c z ρ θ

/-- The real ray and continued circular piece defining the loop at infinity. -/
theorem hypergeometricLoopInfinity_def (a b c z : ℂ) (ρ : ℝ) :
    hypergeometricLoopInfinity a b c z ρ =
      (exp (2 * π * I * (b - 1)) - 1) *
        (∫ v : ℝ in Ioi (ρ / (1 - ρ)), hypergeometricLoopInfinityRay a b c z v) +
      ∫ θ : ℝ in 0..(2 * π), hypergeometricLoopInfinityCircle a b c z ρ θ := (rfl)

/-- Under the Möbius substitution, the infinity-ray kernel times its real Jacobian
is the Euler kernel on `0 < u < 1`. No convergence or cut-plane assumption is needed. -/
theorem hypergeometricLoopInfinityRay_pullback (a b c z : ℂ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    (((1 - u) ^ 2)⁻¹ : ℝ) • hypergeometricLoopInfinityRay a b c z (u / (1 - u)) =
      (u : ℂ) ^ (b - 1) * (1 - (u : ℂ)) ^ (c - b - 1) * (1 - z * u) ^ (-a) := by
  have hs : 0 < 1 - u := sub_pos.mpr hu1
  have hs0 : (1 : ℂ) - u ≠ 0 := by exact_mod_cast hs.ne'
  have h1 := TauCeti.one_add_div_one_sub hs0
  have hq := TauCeti.one_add_div_one_sub_sub_mul_div_one_sub hs0 z
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
  rw [hypergeometricLoopInfinityRay_def]
  rw [hp]
  push_cast
  rw [hq, h1, real_smul]
  push_cast
  simpa only [one_div, mul_one, one_mul, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hu.ne'),
    mul_comm, mul_left_comm, mul_assoc] using ht

private theorem infinityCircle_bounds {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hzρ : ‖z‖ * ρ < 1) (θ : ℝ) :
    0 < (1 - circleMap 0 ρ θ).re ∧ 0 < (1 - z * circleMap 0 ρ θ).re := by
  have hρnorm : ‖(ρ : ℂ)‖ < 1 := by
    calc
      ‖(ρ : ℂ)‖ = ‖circleMap 0 ρ 0‖ := by simp
      _ = ρ := by rw [norm_circleMap_zero, abs_of_pos hρ]
      _ < 1 := hρ1
  constructor
  · simpa only [circleMap_zero] using re_one_sub_mul_exp_mul_I_pos hρnorm θ
  · have hzρnorm : ‖z * (ρ : ℂ)‖ < 1 := by
      simpa only [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hρ] using hzρ
    simpa only [circleMap_zero, mul_assoc] using re_one_sub_mul_exp_mul_I_pos hzρnorm θ

private theorem exp_log_radius_add_mul_I_mul {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) (e : ℂ) :
    exp (((Real.log ρ : ℂ) + θ * I) * e) = (ρ : ℂ) ^ e * exp (θ * I * e) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hρ.ne'),
    ← ofReal_log hρ.le, ← exp_add]
  congr 1
  ring

/-- The continued circular kernel pulls back to the circular kernel of the `(0+)` loop.
The bounds `0 < ρ < 1` and `‖z‖ * ρ < 1` keep both remaining factors in the right half-plane,
so the principal powers agree with the continued logarithm. -/
theorem hypergeometricLoopInfinityCircle_pullback (a b c z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hzρ : ‖z‖ * ρ < 1) (θ : ℝ) :
    hypergeometricLoopInfinityCircle a b c z ρ θ =
      ((ρ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) *
        (1 - ρ * exp (θ * I)) ^ (c - b - 1) *
        (1 - z * (ρ * exp (θ * I))) ^ (-a) * (I * ρ * exp (θ * I)) := by
  rw [hypergeometricLoopInfinityCircle_def]
  dsimp only
  set u : ℂ := ρ * exp (θ * I)
  obtain ⟨hs, hq⟩ := infinityCircle_bounds hρ hρ1 hzρ θ
  simp only [circleMap_zero] at hs hq
  have hs0 : 1 - u ≠ 0 := ne_zero_of_re_pos hs
  have h1 := TauCeti.one_add_div_one_sub hs0
  have h2 := TauCeti.one_add_div_one_sub_sub_mul_div_one_sub hs0 z
  have hi : 0 < ((1 - u)⁻¹).re := inv_re_pos.mpr hs
  have ht := exp_sub_log_mul_mul_inv_cpow (b - 1) (a - c) (-a) hs0
    (slitPlane_arg_ne_pi (mem_slitPlane_iff.mpr (Or.inl hs)))
    (TauCeti.mul_cpow_of_re_pos hq hi (-a)) ((Real.log ρ : ℂ) + θ * I) (I * u)
  have hexponent : -(b - 1) - (a - c) - -a - 2 = c - b - 1 := by ring
  rw [hexponent] at ht
  have he := exp_log_radius_add_mul_I_mul hρ θ (b - 1)
  rw [h2, h1]
  simpa only [he, u, mul_assoc] using ht

private theorem ray_pullback_eqOn (a b c z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    EqOn (fun u : ℝ => (((1 - u) ^ 2)⁻¹ : ℝ) • hypergeometricLoopInfinityRay a b c z (u / (1 - u)))
      (affineSegIntegrand a b (c - b) 1 z) (Ioo ρ 1) :=
  fun _ hu => hypergeometricLoopInfinityRay_pullback a b c z (hρ.trans hu.1) hu.2

private theorem infinityRay_hasDerivWithinAt {ρ : ℝ} (u : ℝ) (hu : u ∈ Ioo ρ 1) :
    HasDerivWithinAt (fun t : ℝ => t / (1 - t)) ((1 - u) ^ 2)⁻¹ (Ioo ρ 1) u :=
  (TauCeti.hasDerivAt_div_one_sub hu.2.ne).hasDerivWithinAt

private theorem infinityRay_monotoneOn (ρ : ℝ) :
    MonotoneOn (fun u : ℝ => u / (1 - u)) (Ioo ρ 1) :=
  TauCeti.strictMonoOn_div_one_sub.monotoneOn.mono Ioo_subset_Iio_self

/-- The Möbius substitution identifies the infinity-ray integral with the Euler tail.
The identity holds for `0 < ρ < 1`, including totalized integrals without convergence. -/
theorem integral_hypergeometricLoopInfinityRay_eq (a b c z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    (∫ v : ℝ in Ioi (ρ / (1 - ρ)), hypergeometricLoopInfinityRay a b c z v) =
      ∫ u : ℝ in ρ..1,
        (u : ℂ) ^ (b - 1) * (1 - (u : ℂ)) ^ (c - b - 1) * (1 - z * u) ^ (-a) := by
  rw [intervalIntegral.integral_of_le hρ1.le, integral_Ioc_eq_integral_Ioo,
    ← TauCeti.image_div_one_sub_Ioo hρ1]
  rw [integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioo
    infinityRay_hasDerivWithinAt (infinityRay_monotoneOn ρ)]
  exact setIntegral_congr_fun measurableSet_Ioo (ray_pullback_eqOn a b c z hρ)

/-- Absolute integrability on the infinity ray is equivalent to Euler-tail integrability
for `0 < ρ < 1`. This transfers arbitrary tail hypotheses without a cut-plane condition. -/
theorem integrableOn_hypergeometricLoopInfinityRay_iff (a b c z : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    IntegrableOn (hypergeometricLoopInfinityRay a b c z) (Ioi (ρ / (1 - ρ))) ↔
      IntegrableOn (fun u : ℝ =>
        (u : ℂ) ^ (b - 1) * (1 - (u : ℂ)) ^ (c - b - 1) * (1 - z * u) ^ (-a))
        (Ioo ρ 1) := by
  rw [← TauCeti.image_div_one_sub_Ioo hρ1,
    integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn measurableSet_Ioo
      infinityRay_hasDerivWithinAt (infinityRay_monotoneOn ρ)]
  exact integrableOn_congr_fun (ray_pullback_eqOn a b c z hρ) measurableSet_Ioo

/-- On the cut plane, the ray kernel is absolutely integrable from every positive
cutoff when `b.re < c.re`; positivity of `b.re` is not required. -/
theorem integrableOn_hypergeometricLoopInfinityRay (a b c z : ℂ) (hbc : b.re < c.re)
    (hz : 1 - z ∈ slitPlane) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (hypergeometricLoopInfinityRay a b c z) (Ioi R) := by
  let ρ := R / (1 + R)
  have hd : 0 < 1 + R := by linarith
  have hρ : 0 < ρ := div_pos hR hd
  have hρ1 : ρ < 1 := (div_lt_one hd).mpr (by linarith)
  have hcut : ρ / (1 - ρ) = R := by dsimp [ρ]; field_simp; ring
  rw [← hcut, integrableOn_hypergeometricLoopInfinityRay_iff a b c z hρ hρ1]
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hρ1.le).mp
    (intervalIntegrable_eulerIntegrand_right a hbc hz hρ hρ1.le)

/-- The continued circular piece of the loop at infinity is integrable for every
complex parameter under `0 < ρ < 1` and `‖z‖ * ρ < 1`. These bounds keep
the remaining complex powers on the intended branches. -/
theorem intervalIntegrable_hypergeometricLoopInfinityCircle (a b c z : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hzρ : ‖z‖ * ρ < 1) :
    IntervalIntegrable (hypergeometricLoopInfinityCircle a b c z ρ)
      volume 0 (2 * π) := by
  have hc : Continuous (affineCircIntegrand a b (c - b) 1 z ρ) := by
    have heq : affineCircIntegrand a b (c - b) 1 z ρ = fun θ : ℝ =>
        I * affineLogIntegrand a b (c - b) 1 z ((Real.log ρ : ℂ) + θ * I) :=
      funext fun θ => (I_mul_affineLogIntegrand_vertical a b (c - b) 1 z hρ θ).symm
    rw [heq]
    refine continuous_iff_continuousAt.mpr fun θ => ?_
    have hw : (((Real.log ρ : ℂ) + θ * I) : ℂ).re < 0 := by
      simpa using Real.log_neg hρ hρ1
    have hexp : exp ((Real.log ρ : ℂ) + θ * I) = circleMap 0 ρ θ := by
      simpa only [mul_one, cpow_one, circleMap_zero] using
        exp_log_radius_add_mul_I_mul hρ θ 1
    have hslit : 1 - z * exp ((Real.log ρ : ℂ) + θ * I) ∈ slitPlane := by
      rw [hexp]
      exact mem_slitPlane_iff.mpr (Or.inl (infinityCircle_bounds hρ hρ1 hzρ θ).2)
    exact continuousAt_const.mul
      ((differentiableAt_affineLogIntegrand a b (c - b) 1 z hw hslit).continuousAt.comp
        (f := fun θ : ℝ => (Real.log ρ : ℂ) + θ * I)
        (by fun_prop : ContinuousAt (fun θ : ℝ => (Real.log ρ : ℂ) + θ * I) θ))
  have heq : hypergeometricLoopInfinityCircle a b c z ρ =
      affineCircIntegrand a b (c - b) 1 z ρ :=
    funext (hypergeometricLoopInfinityCircle_pullback a b c z hρ hρ1 hzρ)
  rw [heq]
  exact hc.intervalIntegrable _ _

/-- The Möbius substitution `v = u / (1 - u)` identifies the loop based at infinity
with the `(0+)` loop. It requires `0 < ρ < 1` and `‖z‖ * ρ < 1` to control the contour
and branches. Totalization removes the need for ray convergence, while retaining those bounds. -/
theorem hypergeometricLoopInfinity_eq_hypergeometricLoopZero (a b c z : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hzρ : ‖z‖ * ρ < 1) :
    hypergeometricLoopInfinity a b c z ρ = hypergeometricLoopZero a b c z ρ := by
  rw [hypergeometricLoopInfinity_def, hypergeometricLoopZero_eq_affineLoopZero,
    affineLoopZero, integral_hypergeometricLoopInfinityRay_eq a b c z hρ hρ1,
    ← affineSegIntegrand_unit]
  congr 1
  exact intervalIntegral.integral_congr fun θ _ =>
    hypergeometricLoopInfinityCircle_pullback a b c z hρ hρ1 hzρ θ

/-- Radius independence under integrability of the tail starting at the smaller radius.
The radius and norm bounds ensure that both continued contours use the intended branches. -/
theorem hypergeometricLoopInfinity_eq_of_integrableOn (a b c z : ℂ) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂ : 0 < ρ₂) (hρ₂1 : ρ₂ < 1)
    (hz₁ : ‖z‖ * ρ₁ < 1) (hz₂ : ‖z‖ * ρ₂ < 1)
    (hint : IntegrableOn (hypergeometricLoopInfinityRay a b c z)
      (Ioi (min ρ₁ ρ₂ / (1 - min ρ₁ ρ₂)))) :
    hypergeometricLoopInfinity a b c z ρ₁ = hypergeometricLoopInfinity a b c z ρ₂ := by
  rw [hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c z hρ₁ hρ₁1 hz₁,
    hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c z hρ₂ hρ₂1 hz₂]
  apply hypergeometricLoopZero_eq_of_integrableOn a b c z hρ₁ hρ₁1 hρ₂ hρ₂1 hz₁ hz₂
  rw [integrableOn_hypergeometricLoopInfinityRay_iff a b c z (lt_min hρ₁ hρ₂)
    (min_lt_iff.mpr (Or.inl hρ₁1))] at hint
  exact hint

/-- On the cut plane `1 - z ∈ slitPlane`, under `b.re < c.re`, the half-line loop is
independent of the radius satisfying `0 < ρ < 1` and `‖z‖ * ρ < 1`. -/
theorem hypergeometricLoopInfinity_eq (a b c z : ℂ) (hbc : b.re < c.re)
    (hz : 1 - z ∈ slitPlane) {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₁1 : ρ₁ < 1)
    (hρ₂ : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) (hz₁ : ‖z‖ * ρ₁ < 1) (hz₂ : ‖z‖ * ρ₂ < 1) :
    hypergeometricLoopInfinity a b c z ρ₁ = hypergeometricLoopInfinity a b c z ρ₂ := by
  rw [hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c z hρ₁ hρ₁1 hz₁,
    hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c z hρ₂ hρ₂1 hz₂]
  exact hypergeometricLoopZero_eq a b c z hbc hz hρ₁ hρ₁1 hρ₂ hρ₂1 hz₁ hz₂

/-- Joint holomorphy in `(a, b, z)` for fixed `d = c - b` with `0 < d.re`, on the open
domain where `1 - z ∈ slitPlane` and `‖z‖ * ρ < 1`, with `0 < ρ < 1`. -/
theorem analyticOnNhd_hypergeometricLoopInfinity {d : ℂ} (hd : 0 < d.re) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ × ℂ =>
      hypergeometricLoopInfinity p.1 p.2.1 (p.2.1 + d) p.2.2 ρ)
      {p | 1 - p.2.2 ∈ slitPlane ∧ ‖p.2.2‖ * ρ < 1} := by
  have hproj : Continuous (fun q : ℂ × ℂ × ℂ => q.2.2) :=
    continuous_snd.comp continuous_snd
  have hnorm : Continuous (fun q : ℂ × ℂ × ℂ => ‖q.2.2‖ * ρ) := by fun_prop
  have hopen : IsOpen {q : ℂ × ℂ × ℂ | 1 - q.2.2 ∈ slitPlane ∧ ‖q.2.2‖ * ρ < 1} :=
    (isOpen_setOf_one_sub_mem_slitPlane.preimage hproj).inter
      (isOpen_lt hnorm continuous_const)
  exact AnalyticOnNhd.congr hopen (analyticOnNhd_hypergeometricLoopZero hd hρ hρ1)
    (fun _ hq =>
      (hypergeometricLoopInfinity_eq_hypergeometricLoopZero _ _ _ _ hρ hρ1 hq.2).symm)

/-- On the cut plane with `0 < b.re < c.re`, the half-line loop equals a Gamma and
phase prefactor times the normalized Euler integral for `0 < ρ < 1` and `‖z‖ * ρ < 1`.
At positive integral `b`, the loop vanishes. -/
theorem hypergeometricLoopInfinity_eq_mul_eulerIntegral (a : ℂ) {b c z : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) (hz : 1 - z ∈ slitPlane) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hzρ : ‖z‖ * ρ < 1) :
    hypergeometricLoopInfinity a b c z ρ =
      2 * π * I * exp (b * π * I) * Gamma (c - b) / Gamma (1 - b) * eulerIntegral a b c z := by
  rw [hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c z hρ hρ1 hzρ]
  exact hypergeometricLoopZero_eq_eulerIntegral a hb hbc hz hρ hρ1 hzρ

/-- Euler's integral in the region `0 < b.re < c.re` on the cut plane, with positive
integral `b` excluded so that the reciprocal DLMF 15.6.3 prefactor is valid. The radius
satisfies `0 < ρ < 1` and `‖z‖ * ρ < 1`. -/
theorem eulerIntegral_eq_mul_hypergeometricLoopInfinity (a : ℂ) {b c z : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) (hb_int : ∀ n : ℕ, b ≠ n + 1) (hz : 1 - z ∈ slitPlane) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hzρ : ‖z‖ * ρ < 1) :
    eulerIntegral a b c z =
      exp (-b * π * I) * Gamma (1 - b) / (2 * π * I * Gamma (c - b)) *
        hypergeometricLoopInfinity a b c z ρ := by
  exact eq_mul_of_eq_mul_hypergeometricLoopZeroFactor hbc hb_int
    (hypergeometricLoopInfinity_eq_mul_eulerIntegral a hb hbc hz hρ hρ1 hzρ)

/-- On the open unit disk the half-line loop equals the regularized Gauss series times its
Gamma and phase factors for `b.re < c.re` and `0 < ρ < 1`, including positive integral `b`.
The multiplied identity does not require `0 < b.re`. -/
theorem hypergeometricLoopInfinity_eq_mul_regularizedGaussHGFun (a : ℂ) {b c z : ℂ}
    (hbc : b.re < c.re) (hz : ‖z‖ < 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    hypergeometricLoopInfinity a b c z ρ =
      2 * π * I * exp (b * π * I) * Gamma (c - b) / Gamma (1 - b) *
        regularizedGaussHGFun a b c z := by
  have hzρ : ‖z‖ * ρ < 1 := by nlinarith [norm_nonneg z]
  rw [hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c z hρ hρ1 hzρ]
  exact hypergeometricLoopZero_eq_mul_regularizedGaussHGFun a hbc hz hρ hρ1

/-- DLMF 15.6.3 on the open unit disk, under `b.re < c.re` and `0 < ρ < 1`,
excluding positive integral `b`. -/
theorem regularizedGaussHGFun_eq_mul_hypergeometricLoopInfinity (a : ℂ) {b c z : ℂ}
    (hbc : b.re < c.re) (hb_int : ∀ n : ℕ, b ≠ n + 1) (hz : ‖z‖ < 1) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    regularizedGaussHGFun a b c z =
      exp (-b * π * I) * Gamma (1 - b) / (2 * π * I * Gamma (c - b)) *
        hypergeometricLoopInfinity a b c z ρ := by
  -- Share the prefactor inversion from `Complex.eulerIntegral_eq_hypergeometricLoopZero`.
  exact eq_mul_of_eq_mul_hypergeometricLoopZeroFactor hbc hb_int
    (hypergeometricLoopInfinity_eq_mul_regularizedGaussHGFun a hbc hz hρ hρ1)

/-- At zero argument, under `b.re < c.re` and `0 < ρ < 1`, the half-line loop has
the same Gamma evaluation as the `(0+)` loop. -/
@[simp]
theorem hypergeometricLoopInfinity_zero (a : ℂ) {b c : ℂ} (hbc : b.re < c.re) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    hypergeometricLoopInfinity a b c 0 ρ =
      2 * π * I * exp (b * π * I) * Gamma (c - b) / (Gamma (1 - b) * Gamma c) := by
  rw [hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c 0 hρ hρ1 (by simp)]
  exact hypergeometricLoopZero_zero a hbc hρ hρ1

/-- With first parameter zero the half-line loop is independent of `z`; its evaluation
requires `b.re < c.re` and `0 < ρ < 1`, with no bound on `‖z‖ * ρ`. -/
@[simp]
theorem hypergeometricLoopInfinity_zero_left {b c : ℂ} (hbc : b.re < c.re) (z : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    hypergeometricLoopInfinity 0 b c z ρ =
      2 * π * I * exp (b * π * I) * Gamma (c - b) / (Gamma (1 - b) * Gamma c) := by
  have heq : hypergeometricLoopInfinity 0 b c z ρ = hypergeometricLoopInfinity 0 b c 0 ρ := by
    simp only [hypergeometricLoopInfinity_def, hypergeometricLoopInfinityRay_def,
      hypergeometricLoopInfinityCircle_def, neg_zero, cpow_zero]
  rw [heq, hypergeometricLoopInfinity_zero 0 hbc hρ hρ1]

end Complex
