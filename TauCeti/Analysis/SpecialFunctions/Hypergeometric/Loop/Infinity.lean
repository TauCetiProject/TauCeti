/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Loop.Integral
import TauCeti.Algebra.Field.LinearFractional
import TauCeti.Algebra.Order.Field.Basic
import all TauCeti.Analysis.SpecialFunctions.Hypergeometric.Loop.Integral
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Calculus.RealCharts
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
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
unit disk when `b.re < c.re`. The reciprocal evaluations additionally exclude positive integral `b`.

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
theorem hypergeometricLoopInfinityCircle_apply (a b c z : ℂ) (ρ θ : ℝ) :
    hypergeometricLoopInfinityCircle a b c z ρ θ =
      let u : ℂ := ρ * exp (θ * I)
      let v := u / (1 - u)
      exp (((Real.log ρ : ℂ) + θ * I - log (1 - u)) * (b - 1)) *
        (1 + v) ^ (a - c) * (1 + v - z * v) ^ (-a) * (I * u / (1 - u) ^ 2) := by
  simp only [hypergeometricLoopInfinityCircle, deriv_circleMap, circleMap_zero, mul_comm I]

/-- The loop based at infinity in DLMF 15.6.3, obtained from the `(0+)` loop by
`v = u / (1 - u)`. The bounds `0 < ρ < 1` and `‖z‖ * ρ < 1` control
the circular branches. The ray integrals use principal powers and are totalized when
they do not converge. On the cut plane `1 - z ∈ slitPlane`, these ray branches give
the DLMF contour; the outgoing ray carries the monodromy of `v ^ (b - 1)`. -/
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

private theorem mul_inv_cpow_collect (p r t : ℂ) {s q : ℂ} (hs : s ≠ 0)
    (harg : s.arg ≠ Real.pi) (hpow : (q * s⁻¹) ^ t = q ^ t * s⁻¹ ^ t) (E D : ℂ) :
    E * s⁻¹ ^ p * s⁻¹ ^ r * (q * s⁻¹) ^ t * (D / s ^ 2) =
      E * s ^ (-p - r - t - 2) * q ^ t * D := by
  have hinv (e : ℂ) : s⁻¹ ^ e = s ^ (-e) := by
    rw [inv_cpow s e harg, cpow_neg]
  have hsq : (s ^ 2)⁻¹ = s ^ (-2 : ℂ) := by rw [cpow_neg]; norm_num
  calc
    _ = E * (s ^ (-p) * s ^ (-r) * s ^ (-t) * s ^ (-2 : ℂ)) * q ^ t * D := by
      rw [hpow, hinv p, hinv r, hinv t, div_eq_mul_inv, hsq]
      ring
    _ = _ := by
      rw [← cpow_add (-p) (-r) hs, ← cpow_add (-p + -r) (-t) hs,
        ← cpow_add (-p + -r + -t) (-2) hs]
      simp only [sub_eq_add_neg]

/-- Under the Möbius substitution, the infinity-ray kernel times its real Jacobian
is the Euler kernel on `0 < u < 1`. No convergence or cut-plane assumption is needed. -/
theorem hypergeometricLoopInfinityRay_pullback (a b c z : ℂ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    (((1 - u) ^ 2)⁻¹ : ℝ) • hypergeometricLoopInfinityRay a b c z (u / (1 - u)) =
      (u : ℂ) ^ (b - 1) * (1 - (u : ℂ)) ^ (c - b - 1) * (1 - z * u) ^ (-a) := by
  have hs : 0 < 1 - u := sub_pos.mpr hu1
  have hs0 : (1 : ℂ) - u ≠ 0 := by exact_mod_cast hs.ne'
  have h1 : 1 + (u : ℂ) / (1 - u) = (1 - (u : ℂ))⁻¹ := by
    simpa using TauCeti.one_add_div_one_sub_sub_mul_div_one_sub hs0 0
  have hq := TauCeti.one_add_div_one_sub_sub_mul_div_one_sub hs0 z
  have hp : ((u / (1 - u) : ℝ) : ℂ) ^ (b - 1) =
      (u : ℂ) ^ (b - 1) * ((1 : ℂ) - u)⁻¹ ^ (b - 1) := by
    rw [ofReal_div, div_cpow_ofReal_nonneg hu.le hs.le, div_eq_mul_inv,
      ← inv_cpow_ofReal_nonneg hs.le]
    push_cast
    rfl
  have hpow : ((1 - z * u) * ((1 : ℂ) - u)⁻¹) ^ (-a) =
      (1 - z * u) ^ (-a) * ((1 : ℂ) - u)⁻¹ ^ (-a) := by
    simpa only [ofReal_inv, ofReal_sub, ofReal_one] using
      mul_ofReal_cpow (1 - z * u) (inv_nonneg.mpr hs.le) (-a)
  have ht := mul_inv_cpow_collect (b - 1) (a - c) (-a)
    (s := 1 - (u : ℂ)) (q := 1 - z * u) hs0
    (slitPlane_arg_ne_pi (mem_slitPlane_iff.mpr (Or.inl (by simpa using hs))))
    hpow ((u : ℂ) ^ (b - 1)) 1
  have hexponent : -(b - 1) - (a - c) - -a - 2 = c - b - 1 := by ring
  rw [hexponent] at ht
  rw [hypergeometricLoopInfinityRay_def]
  rw [hp]
  push_cast
  rw [hq, h1, real_smul]
  push_cast
  simpa only [one_div, mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc] using ht

private theorem re_one_sub_mul_circleMap_pos {z : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hzρ : ‖z‖ * ρ < 1) (θ : ℝ) : 0 < (1 - z * circleMap 0 ρ θ).re := by
  apply TauCeti.re_pos_of_norm_sub_one_lt_one
  simpa [norm_mul, norm_circleMap_zero, abs_of_pos hρ] using hzρ

/-- The continued circular kernel pulls back to the circular kernel of the `(0+)` loop.
For `u = circleMap 0 ρ θ`, the radius bound puts `1 - u` in the right half-plane.
The pointwise argument-sum hypothesis permits splitting the principal power of
`(1 - z * u) / (1 - u)`. -/
theorem hypergeometricLoopInfinityCircle_pullback (a b c z : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ < 1) (θ : ℝ) (hq : (1 - z * circleMap 0 ρ θ).arg +
      ((1 - circleMap 0 ρ θ)⁻¹).arg ∈ Ioc (-π) π) :
    hypergeometricLoopInfinityCircle a b c z ρ θ =
      ((ρ : ℂ) ^ (b - 1) * exp (θ * I * (b - 1))) *
        (1 - ρ * exp (θ * I)) ^ (c - b - 1) *
        (1 - z * (ρ * exp (θ * I))) ^ (-a) * (I * ρ * exp (θ * I)) := by
  rw [hypergeometricLoopInfinityCircle_apply]
  dsimp only
  set u : ℂ := ρ * exp (θ * I)
  have hs : 0 < (1 - u).re := by
    simpa only [circleMap_zero, one_mul, u] using
      re_one_sub_mul_circleMap_pos (z := 1) hρ (by simpa using hρ1) θ
  rw [circleMap_zero] at hq
  have hs0 : 1 - u ≠ 0 := ne_zero_of_re_pos hs
  have h1 : 1 + u / (1 - u) = (1 - u)⁻¹ := by
    simpa using TauCeti.one_add_div_one_sub_sub_mul_div_one_sub hs0 0
  have h2 := TauCeti.one_add_div_one_sub_sub_mul_div_one_sub hs0 z
  have ht := mul_inv_cpow_collect (b - 1) (a - c) (-a) hs0
    (slitPlane_arg_ne_pi (mem_slitPlane_iff.mpr (Or.inl hs)))
    (mul_cpow hq (-a)) (exp (((Real.log ρ : ℂ) + θ * I) * (b - 1))) (I * u)
  have hexponent : -(b - 1) - (a - c) - -a - 2 = c - b - 1 := by ring
  rw [hexponent] at ht
  have he := exp_log_add_mul (ofReal_ne_zero.mpr hρ.ne') (θ * I) (b - 1)
  rw [← ofReal_log hρ.le] at he
  have hlog : exp (((Real.log ρ : ℂ) + θ * I - log (1 - u)) * (b - 1)) =
      exp (((Real.log ρ : ℂ) + θ * I) * (b - 1)) * (1 - u)⁻¹ ^ (b - 1) := by
    rw [inv_cpow _ _ (slitPlane_arg_ne_pi (mem_slitPlane_iff.mpr (Or.inl hs))),
      ← cpow_neg, cpow_def_of_ne_zero hs0, ← exp_add]
    congr 1
    ring
  rw [h2, h1, hlog]
  simpa only [he, u, mul_assoc] using ht

private theorem ray_pullback_eqOn (a b c z : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    EqOn (fun u : ℝ => (((1 - u) ^ 2)⁻¹ : ℝ) • hypergeometricLoopInfinityRay a b c z (u / (1 - u)))
      (fun u : ℝ => (u : ℂ) ^ (b - 1) * (1 - (u : ℂ)) ^ (c - b - 1) *
        (1 - z * u) ^ (-a)) (Ioo ρ 1) :=
  fun _ hu => hypergeometricLoopInfinityRay_pullback a b c z (hρ.trans_lt hu.1) hu.2

private theorem infinityCircle_eq_affineCircIntegrand (a b c z : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hzρ : ‖z‖ * ρ < 1) :
    hypergeometricLoopInfinityCircle a b c z ρ = affineCircIntegrand a b (c - b) 1 z ρ := by
  rw [affineCircIntegrand_unit]
  refine funext fun θ => hypergeometricLoopInfinityCircle_pullback a b c z hρ hρ1 θ ?_
  have hq := re_one_sub_mul_circleMap_pos hρ hzρ θ
  have hs : 0 < (1 - circleMap 0 ρ θ).re := by
    simpa only [one_mul] using
      re_one_sub_mul_circleMap_pos (z := 1) hρ (by simpa using hρ1) θ
  have hqarg := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hq)
  have hsarg := abs_arg_lt_pi_div_two_iff.mpr (Or.inl (inv_re_pos.mpr hs))
  exact ⟨by linarith [abs_lt.mp hqarg, abs_lt.mp hsarg],
    by linarith [abs_lt.mp hqarg, abs_lt.mp hsarg]⟩

/-- The Möbius substitution identifies the infinity-ray integral with the Euler tail.
The identity holds for `0 ≤ ρ < 1`, including totalized integrals without convergence. -/
theorem integral_hypergeometricLoopInfinityRay_eq (a b c z : ℂ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (∫ v : ℝ in Ioi (ρ / (1 - ρ)), hypergeometricLoopInfinityRay a b c z v) =
      ∫ u : ℝ in ρ..1,
        (u : ℂ) ^ (b - 1) * (1 - (u : ℂ)) ^ (c - b - 1) * (1 - z * u) ^ (-a) := by
  rw [intervalIntegral.integral_of_le hρ1.le, integral_Ioc_eq_integral_Ioo,
    ← TauCeti.image_div_one_sub_Ioo hρ1]
  rw [integral_image_eq_integral_deriv_smul_of_monotoneOn measurableSet_Ioo
    (fun u hu => (TauCeti.hasDerivAt_div_one_sub hu.2.ne).hasDerivWithinAt)
    (TauCeti.strictMonoOn_div_one_sub.monotoneOn.mono Ioo_subset_Iio_self)]
  exact setIntegral_congr_fun measurableSet_Ioo (ray_pullback_eqOn a b c z hρ)

/-- Absolute integrability on the infinity ray is equivalent to Euler-tail integrability
for `0 ≤ ρ < 1`. This transfers arbitrary tail hypotheses without a cut-plane condition. -/
theorem integrableOn_hypergeometricLoopInfinityRay_iff (a b c z : ℂ) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) :
    IntegrableOn (hypergeometricLoopInfinityRay a b c z) (Ioi (ρ / (1 - ρ))) ↔
      IntegrableOn (fun u : ℝ =>
        (u : ℂ) ^ (b - 1) * (1 - (u : ℂ)) ^ (c - b - 1) * (1 - z * u) ^ (-a))
        (Ioo ρ 1) := by
  rw [← TauCeti.image_div_one_sub_Ioo hρ1,
    integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn measurableSet_Ioo
      (fun u hu => (TauCeti.hasDerivAt_div_one_sub hu.2.ne).hasDerivWithinAt)
      (TauCeti.strictMonoOn_div_one_sub.monotoneOn.mono Ioo_subset_Iio_self)]
  exact integrableOn_congr_fun (ray_pullback_eqOn a b c z hρ) measurableSet_Ioo

/-- On the cut plane, the ray kernel is absolutely integrable from every positive
cutoff when `b.re < c.re`; positivity of `b.re` is not required. -/
theorem integrableOn_hypergeometricLoopInfinityRay (a b c z : ℂ) (hbc : b.re < c.re)
    (hz : 1 - z ∈ slitPlane) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (hypergeometricLoopInfinityRay a b c z) (Ioi R) := by
  let ρ := R / (1 + R)
  have hd : 0 < 1 + R := by linarith
  have hρ : 0 < ρ := div_pos hR hd
  have hρ1 : ρ < 1 := TauCeti.div_one_add_lt_one hR.le
  have hcut : ρ / (1 - ρ) = R := by dsimp [ρ]; field_simp; ring
  rw [← hcut, integrableOn_hypergeometricLoopInfinityRay_iff a b c z hρ.le hρ1]
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hρ1.le).mp
    (intervalIntegrable_eulerIntegrand_right a hbc hz hρ hρ1.le)

private theorem infinityCircle_denominators_ne_zero (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hzρ : ‖z‖ * ρ ≠ 1) (θ : ℝ) :
    1 - circleMap 0 ρ θ ≠ 0 ∧
      1 + circleMap 0 ρ θ / (1 - circleMap 0 ρ θ) -
        z * (circleMap 0 ρ θ / (1 - circleMap 0 ρ θ)) ≠ 0 := by
  have hs := re_one_sub_mul_circleMap_pos (z := 1) hρ (by simpa using hρ1) θ
  have hs0 : 1 - circleMap 0 ρ θ ≠ 0 := ne_zero_of_re_pos (by simpa using hs)
  have hq0 : 1 - z * circleMap 0 ρ θ ≠ 0 := by
    intro heq
    have hn := congrArg norm (sub_eq_zero.mp heq)
    exact hzρ (by simpa [norm_mul, norm_circleMap_zero, abs_of_pos hρ] using hn.symm)
  refine ⟨hs0, ?_⟩
  rw [TauCeti.one_add_div_one_sub_sub_mul_div_one_sub hs0 z]
  exact mul_ne_zero hq0 (inv_ne_zero hs0)

/-- The circular kernel is integrable whenever `0 < ρ < 1` and `‖z‖ * ρ ≠ 1`.
The latter condition prevents zeros of its affine factors. Principal powers can jump across
branch cuts, but their norms are bounded by continuous functions on the angle interval. -/
theorem intervalIntegrable_hypergeometricLoopInfinityCircle (a b c z : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hzρ : ‖z‖ * ρ ≠ 1) :
    IntervalIntegrable (hypergeometricLoopInfinityCircle a b c z ρ)
      volume 0 (2 * π) := by
  let u := circleMap 0 ρ
  let v := fun θ => u θ / (1 - u θ)
  let g := fun θ => 1 + v θ - z * v θ
  have hu : Continuous u := continuous_circleMap 0 ρ
  have hs (θ : ℝ) : 1 - u θ ≠ 0 := (infinityCircle_denominators_ne_zero z hρ hρ1 hzρ θ).1
  have hv : Continuous v := hu.div (continuous_const.sub hu) hs
  have hg : Continuous g := (continuous_const.add hv).sub (continuous_const.mul hv)
  have hg0 (θ : ℝ) : g θ ≠ 0 := (infinityCircle_denominators_ne_zero z hρ hρ1 hzρ θ).2
  have hhalf (θ : ℝ) : 0 < (1 - u θ).re := by
    simpa [u] using re_one_sub_mul_circleMap_pos (z := 1) hρ (by simpa using hρ1) θ
  have hinv (θ : ℝ) : 1 + v θ = (1 - u θ)⁻¹ := by
    simpa [v] using TauCeti.one_add_div_one_sub_sub_mul_div_one_sub (hs θ) 0
  have hlog : Continuous (fun θ => log (1 - u θ)) :=
    (continuous_const.sub hu).clog fun θ => mem_slitPlane_iff.mpr (Or.inl (hhalf θ))
  have hpow : Continuous (fun θ => (1 + v θ) ^ (a - c)) := by
    apply continuous_iff_continuousAt.mpr fun θ => ?_
    apply (continuousAt_cpow_const ?_).comp (continuous_const.add hv).continuousAt
    simp only [Pi.add_apply, hinv θ]
    exact mem_slitPlane_iff.mpr (Or.inl (inv_re_pos.mpr (hhalf θ)))
  let h := fun θ : ℝ =>
    exp (((Real.log ρ : ℂ) + θ * I - log (1 - u θ)) * (b - 1)) *
      (1 + v θ) ^ (a - c) * (I * u θ / (1 - u θ) ^ 2)
  have hh : Continuous h := by
    refine ((continuous_exp.comp ?_).mul hpow).mul ?_
    · exact ((continuous_const.add (continuous_ofReal.mul continuous_const)).sub hlog).mul
        continuous_const
    · exact (continuous_const.mul hu).div ((continuous_const.sub hu).pow 2)
        (fun θ => pow_ne_zero _ (hs θ))
  have hmeas : Measurable (fun θ => g θ ^ (-a)) := by
    simp_rw [cpow_def_of_ne_zero (hg0 _)]
    exact continuous_exp.measurable.comp ((measurable_log.comp hg.measurable).mul_const (-a))
  have hdom : Continuous (fun θ => ‖h θ‖ *
      (‖g θ‖ ^ (-a).re * Real.exp (π * |(-a).im|))) :=
    hh.norm.mul ((hg.norm.rpow_const
      (fun θ => Or.inl (norm_ne_zero_iff.mpr (hg0 θ)))).mul continuous_const)
  have hint : IntervalIntegrable (fun θ => h θ * g θ ^ (-a)) volume 0 (2 * π) :=
    (hdom.intervalIntegrable 0 (2 * π)).mono_fun'
    (hh.measurable.mul hmeas).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ => by
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_cpow_le_mul_exp _ _) (norm_nonneg _))
  refine hint.congr fun θ _ => ?_
  rw [hypergeometricLoopInfinityCircle_apply]
  dsimp [h, g, v, u]
  simp only [circleMap_zero]
  ring

/-- The Möbius substitution `v = u / (1 - u)` identifies the loop based at infinity
with the `(0+)` loop. It requires `0 < ρ < 1` and `‖z‖ * ρ < 1` to control the contour
and the circular branches. The ray integrals use totalized principal powers, so no
ray convergence or cut-plane condition is needed for this identity. -/
theorem hypergeometricLoopInfinity_eq_hypergeometricLoopZero (a b c z : ℂ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ < 1) (hzρ : ‖z‖ * ρ < 1) :
    hypergeometricLoopInfinity a b c z ρ = hypergeometricLoopZero a b c z ρ := by
  rw [hypergeometricLoopInfinity_def, hypergeometricLoopZero_eq_affineLoopZero,
    affineLoopZero, integral_hypergeometricLoopInfinityRay_eq a b c z hρ.le hρ1,
    affineSegIntegrand_unit, infinityCircle_eq_affineCircIntegrand a b c z hρ hρ1 hzρ]

/-- Radius independence under integrability of the infinity-ray tail starting at
`m / (1 - m)`, where `m = min ρ₁ ρ₂`.
The radius and norm bounds control the circular branches. The principal-power ray
integrals agree with the DLMF ray branches on the cut plane `1 - z ∈ slitPlane`. -/
theorem hypergeometricLoopInfinity_eq_of_integrableOn (a b c z : ℂ) {ρ₁ ρ₂ : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ₁1 : ρ₁ < 1) (hρ₂ : 0 < ρ₂) (hρ₂1 : ρ₂ < 1)
    (hz₁ : ‖z‖ * ρ₁ < 1) (hz₂ : ‖z‖ * ρ₂ < 1)
    (hint : IntegrableOn (hypergeometricLoopInfinityRay a b c z)
      (Ioi (min ρ₁ ρ₂ / (1 - min ρ₁ ρ₂)))) :
    hypergeometricLoopInfinity a b c z ρ₁ = hypergeometricLoopInfinity a b c z ρ₂ := by
  rw [hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c z hρ₁ hρ₁1 hz₁,
    hypergeometricLoopInfinity_eq_hypergeometricLoopZero a b c z hρ₂ hρ₂1 hz₂]
  apply hypergeometricLoopZero_eq_of_integrableOn a b c z hρ₁ hρ₁1 hρ₂ hρ₂1 hz₁ hz₂
  rw [integrableOn_hypergeometricLoopInfinityRay_iff a b c z (le_min hρ₁.le hρ₂.le)
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
  have hzρ : ‖z‖ * ρ < 1 := (mul_le_of_le_one_right (norm_nonneg z) hρ1.le).trans_lt hz
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
      hypergeometricLoopInfinityCircle_apply, neg_zero, cpow_zero]
  rw [heq, hypergeometricLoopInfinity_zero 0 hbc hρ hρ1]

end Complex
