/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.Complex.ParametricIntegralHolomorphy
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecialFunctions.Pow.ParametricIntegral

/-!
# The complex upper incomplete Gamma function

`Complex.upperIncompleteGamma` is the principal upper incomplete Gamma function, defined
by the integral along the horizontal ray from `z` to infinity. When `z` belongs to
`Complex.slitPlane`, this ray stays away from zero, so its integrand is absolutely integrable
for every complex parameter `a`, including nonpositive integers. This avoids relying on
`Γ(a) - γ(a, z)` or `Γ(a) Q(a, z)` at the poles of the classical Gamma function.

On the positive real axis it agrees with the usual integral over `(x, ∞)`, including
parameters with nonpositive real part. `Complex.partialGamma_add_upperIncompleteGamma`
splits Euler's Gamma integral into Mathlib's `Complex.partialGamma` and the upper tail
when `0 < a.re` and the real endpoint is nonnegative.

For `z` on the branch cut the same totalized Bochner integral is used: it need not converge
and then takes the junk value zero. No agreement with analytic continuation on the branch
cut is asserted.

For `z` in the slit plane, `Γ(a, z)` is holomorphic in `z` with derivative `−z^{a−1} e^{−z}`
(DLMF 8.8.13) and entire in `a`, and it satisfies the differential equations DLMF 8.2.12–8.2.13.
On the closed positive real axis `x ↦ Γ(a, x)` is continuous for `0 < Re a`, so `Γ(a, x) → Γ(a)`
as `x → 0+`.

## Main results

* `Complex.upperIncompleteGamma_ofReal_eq_ofReal_integral`,
  `Complex.upperIncompleteGamma_ofReal_im`: for real `a` and `0 ≤ x`, `Γ(a, x)` is the real
  integral `∫ₓ^∞ t^{a−1} e^{−t} dt`, hence real;
* `Complex.hasDerivAt_upperIncompleteGamma`, `Complex.deriv_upperIncompleteGamma`,
  `Complex.analyticOnNhd_upperIncompleteGamma`: `∂Γ(a, z)/∂z = −z^{a−1} e^{−z}` on the slit
  plane (DLMF 8.8.13), so `Γ(a, ·)` is holomorphic there;
* `Complex.differentiable_upperIncompleteGamma_left`: `Γ(·, z)` is entire for `z` in the slit
  plane;
* `Complex.continuousOn_upperIncompleteGamma_ofReal`,
  `Complex.tendsto_upperIncompleteGamma_ofReal_nhdsGT_zero`: for `0 < Re a`, `x ↦ Γ(a, x)` is
  continuous on `[0, ∞)` and `Γ(a, x) → Γ(a)` as `x → 0+`;
* `Complex.upperIncompleteGamma_ode`: DLMF 8.2.12 for `Γ(a, ·)`;
* `Complex.deriv_exp_mul_cpow_one_sub_mul_upperIncompleteGamma`,
  `Complex.exp_mul_cpow_one_sub_mul_upperIncompleteGamma_ode`: the derivative of
  `e^z z^{1−a} Γ(a, z)` and DLMF 8.2.13 for it.

## Implementation notes

The derivative in `z` differentiates under the ray integral with
`TauCeti.hasDerivAt_integral_mul_ofReal_add_cpow` and integrates the derivative of
`t ↦ e^{−t} (t + z)^{a−1}` along the ray. Holomorphy in `a` is
`TauCeti.hasDerivAt_integral_of_dominated_of_differentiableOn`, with the integrand dominated on
the unit ball of parameters by `Complex.norm_cpow_le_of_mem_closedBall`. Continuity on the
positive axis is Mathlib's `MeasureTheory.IntegrableOn.continuousOn_Ici_primitive_Ioi`.

## References

* NIST Digital Library of Mathematical Functions, §§8.2, 8.8, especially 8.2.2.
  <https://dlmf.nist.gov/8.2>

The results after `Complex.partialGamma_add_upperIncompleteGamma` are new proofs; the statements
follow DLMF. `Complex.upperIncompleteGamma_ofReal_eq_ofReal_integral` is adapted from the lean-DLMF
project (<https://github.com/bjbraams/lean-DLMF>), file `DLMF/IncompleteGamma/RealIntegrals.lean`.
-/

public section

open MeasureTheory Set Filter Asymptotics
open scoped Topology

namespace Complex

/-- The principal upper incomplete Gamma function with complex parameter `a` and ray
endpoint `z`, defined by
`Γ(a, z) = exp (-z) * ∫ t in Ioi (0 : ℝ), (z + t) ^ (a - 1) * exp (-t)`.
When `z` lies on the nonpositive real axis this still uses the principal complex power and
the Bochner integral, which is zero when the integrand is not integrable; agreement with
analytic continuation there is not asserted. -/
noncomputable def upperIncompleteGamma (a z : ℂ) : ℂ :=
  _root_.Complex.exp (-z) *
    ∫ t in Ioi (0 : ℝ), (z + t) ^ (a - 1) * _root_.Complex.exp (-(t : ℂ))

/-- The defining horizontal-ray integral with its exponential prefactor. -/
theorem upperIncompleteGamma_def (a z : ℂ) :
    upperIncompleteGamma a z =
      _root_.Complex.exp (-z) *
        ∫ t in Ioi (0 : ℝ), (z + t) ^ (a - 1) * _root_.Complex.exp (-(t : ℂ)) := (rfl)

/-- Absolute convergence of the horizontal-ray integrand
`(z + t) ^ (a - 1) * exp (-(z + t))` of `Complex.upperIncompleteGamma_eq_integral` on the slit
plane, for every complex parameter `a`. -/
theorem integrableOn_upperIncompleteGamma_integrand (a : ℂ) {z : ℂ}
    (hz : z ∈ _root_.Complex.slitPlane) :
    IntegrableOn (fun t : ℝ => (z + t) ^ (a - 1) * _root_.Complex.exp (-(z + t)))
      (Ioi 0) := by
  -- The integrand with the constant factor `exp (-z)` taken out.
  suffices h : IntegrableOn (fun t : ℝ => (z + t) ^ (a - 1) * _root_.Complex.exp (-(t : ℂ)))
      (Ioi 0) by
    refine IntegrableOn.congr_fun (h.const_mul (_root_.Complex.exp (-z))) (fun t _ => ?_)
      measurableSet_Ioi
    rw [neg_add, _root_.Complex.exp_add]
    ring
  have hi : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (a - 1).re) (Ioi 1) :=
    integrable_of_isBigO_exp_neg one_half_pos
      (continuousOn_id.neg.rexp.mul (continuousOn_id.rpow_const (by grind)))
      (Real.Gamma_integrand_isLittleO _).isBigO
  have hs := ((measurePreserving_add_left volume (1 : ℝ)).integrableOn_comp_preimage
    (MeasurableEquiv.addLeft (1 : ℝ)).measurableEmbedding).mpr hi
  have hw : IntegrableOn
      (fun t : ℝ => ‖_root_.Complex.exp (-(t : ℂ))‖ * (1 + t) ^ (a - 1).re)
      (Ioi 0) := by
    simpa [IntegrableOn, preimage_const_add_Ioi, Function.comp_def, norm_exp, neg_add, Real.exp_add,
      Real.exp_neg, mul_comm, mul_left_comm, mul_assoc] using hs.const_mul (Real.exp 1)
  simpa only [mul_comm, add_comm] using
    (TauCeti.integrableOn_mul_ofReal_add_cpow_iff_norm_mul_one_add_rpow
      hz (a - 1)).mpr ⟨(by fun_prop : Continuous
        (fun t : ℝ => _root_.Complex.exp (-(t : ℂ)))).aestronglyMeasurable, hw⟩

/-- The defining ray integral with the exponential prefactor absorbed into the integrand
(DLMF 8.2.2). -/
theorem upperIncompleteGamma_eq_integral (a z : ℂ) :
    upperIncompleteGamma a z =
      ∫ t in Ioi (0 : ℝ), (z + t) ^ (a - 1) * _root_.Complex.exp (-(z + t)) := by
  rw [upperIncompleteGamma, ← integral_const_mul]
  congr 1
  ext t
  rw [neg_add, _root_.Complex.exp_add]
  ring

/-- On a real ray, the upper incomplete Gamma function is the usual tail integral.
The identity also holds at the definition's junk values; convergence is guaranteed for `x > 0`. -/
theorem upperIncompleteGamma_ofReal (a : ℂ) (x : ℝ) :
    upperIncompleteGamma a x =
      ∫ t in Ioi x, (t : ℂ) ^ (a - 1) * _root_.Complex.exp (-(t : ℂ)) := by
  rw [upperIncompleteGamma_eq_integral]
  simpa only [preimage_const_add_Ioi, sub_self, _root_.Complex.ofReal_add] using
    (measurePreserving_add_left volume x).setIntegral_preimage_emb
      (MeasurableEquiv.addLeft x).measurableEmbedding
      (fun t : ℝ => (t : ℂ) ^ (a - 1) * _root_.Complex.exp (-(t : ℂ))) (Ioi x)

/-- For real `a` and `0 ≤ x`, `Γ(a, x)` is the real tail integral `∫ₓ^∞ t^{a−1} e^{−t} dt`. -/
theorem upperIncompleteGamma_ofReal_eq_ofReal_integral (a : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    upperIncompleteGamma a x = ((∫ t in Ioi x, t ^ (a - 1) * Real.exp (-t) : ℝ) : ℂ) := by
  rw [upperIncompleteGamma_ofReal, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [ofReal_mul, ofReal_cpow (hx.trans ht.le), ofReal_exp, ofReal_sub, ofReal_one, ofReal_neg]

/-- `Γ(a, x)` is real for every real `a` and `0 ≤ x`. -/
@[simp]
theorem upperIncompleteGamma_ofReal_im (a : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    (upperIncompleteGamma a x).im = 0 := by
  rw [upperIncompleteGamma_ofReal_eq_ofReal_integral a hx, ofReal_im]

/-- At shape one the ray integral is an exponential, even on the branch cut. -/
@[simp]
theorem upperIncompleteGamma_one_left (z : ℂ) :
    upperIncompleteGamma 1 z = _root_.Complex.exp (-z) := by
  have hi : (∫ t in Ioi (0 : ℝ), _root_.Complex.exp (-(t : ℂ))) = 1 := by
    simpa using integral_exp_mul_complex_Ioi (a := -1) (by norm_num) 0
  simp [upperIncompleteGamma, hi]

/-- The upper incomplete Gamma function at zero agrees with Gamma in its integral
half-plane. This does not assert convergence at zero for other parameters. -/
@[simp]
theorem upperIncompleteGamma_zero_right {a : ℂ} (ha : 0 < a.re) :
    upperIncompleteGamma a 0 = _root_.Complex.Gamma a := by
  rw [upperIncompleteGamma, _root_.Complex.Gamma_eq_integral ha,
    _root_.Complex.GammaIntegral]
  simp only [neg_zero, _root_.Complex.exp_zero, zero_add, one_mul]
  congr 1
  ext t
  simp [_root_.Complex.ofReal_exp, mul_comm]

/-- Splitting Euler's Gamma integral at a nonnegative real endpoint gives the upper
incomplete Gamma function and Mathlib's `Complex.partialGamma`. -/
theorem partialGamma_add_upperIncompleteGamma {a : ℂ} (ha : 0 < a.re)
    {x : ℝ} (hx : 0 ≤ x) :
    _root_.Complex.partialGamma a x + upperIncompleteGamma a x = _root_.Complex.Gamma a := by
  rw [upperIncompleteGamma_ofReal, _root_.Complex.partialGamma,
    _root_.Complex.Gamma_eq_integral ha, _root_.Complex.GammaIntegral]
  simpa only [_root_.Complex.ofReal_exp, _root_.Complex.ofReal_neg, mul_comm] using
    intervalIntegral.integral_interval_add_Ioi (_root_.Complex.GammaIntegral_convergent ha)
      ((_root_.Complex.GammaIntegral_convergent ha).mono_set (Ioi_subset_Ioi hx))

/-! ### Holomorphy in the endpoint -/

/-- **DLMF 8.8.13**: on the slit plane, `Γ(a, ·)` has derivative `−z^{a−1} e^{−z}`. -/
theorem hasDerivAt_upperIncompleteGamma {z : ℂ} (hz : z ∈ slitPlane) (a : ℂ) :
    HasDerivAt (upperIncompleteGamma a) (-(z ^ (a - 1) * cexp (-z))) z := by
  -- the ray integrand in the product order of the parametric-integral API
  have hint (b : ℂ) : IntegrableOn (fun t : ℝ => cexp (-(t : ℂ)) * ((t : ℂ) + z) ^ b) (Ioi 0) := by
    -- the integrand of `upperIncompleteGamma_eq_integral` times the constant `e^z`
    refine IntegrableOn.congr_fun
      ((integrableOn_upperIncompleteGamma_integrand (b + 1) hz).const_mul (cexp z))
      (fun t _ => ?_) measurableSet_Ioi
    rw [add_sub_cancel_right, neg_add, exp_add, exp_neg z, add_comm z]
    field_simp
  have hfun : upperIncompleteGamma a =
      fun w => cexp (-w) * ∫ t in Ioi (0 : ℝ), cexp (-(t : ℂ)) * ((t : ℂ) + w) ^ (a - 1) := by
    funext w
    rw [upperIncompleteGamma_def]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [add_comm, mul_comm]
  have hI := TauCeti.hasDerivAt_integral_mul_ofReal_add_cpow hz (hint (a - 1))
  -- the integral of the derivative along the ray, by the fundamental theorem of calculus
  have hG (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      HasDerivAt (fun s : ℝ => cexp (-(s : ℂ)) * ((s : ℂ) + z) ^ (a - 1))
        ((a - 1) * (cexp (-(t : ℂ)) * ((t : ℂ) + z) ^ (a - 1 - 1)) -
          cexp (-(t : ℂ)) * ((t : ℂ) + z) ^ (a - 1)) t := by
    have hmem := TauCeti.ofReal_add_mem_slitPlane hz ht
    have hf : (fun s : ℝ => cexp (-(s : ℂ)) * ((s : ℂ) + z) ^ (a - 1)) =
        fun s : ℝ => ((s : ℂ) + z) ^ (a - 1) * cexp (-1 * s) := by
      funext s
      rw [neg_one_mul, mul_comm]
    rw [hf]
    refine (hasDerivAt_add_cpow_mul_exp_mul (a - 1) z (-1) hmem).comp_ofReal.congr_deriv ?_
    rw [cpow_sub (a - 1) 1 (slitPlane_ne_zero hmem), cpow_one, neg_one_mul]
    field_simp
    ring
  have h₂ := (hint (a - 1 - 1)).const_mul (a - 1)
  have h₁ := hint (a - 1)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' hG (h₂.sub h₁)
    (tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun t ht => hG t (mem_Ici_of_Ioi ht))
      (h₂.sub h₁) h₁)
  rw [integral_sub h₂ h₁, integral_const_mul] at hFTC
  simp only [ofReal_zero, zero_add, neg_zero, exp_zero, one_mul, zero_sub] at hFTC
  rw [hfun]
  refine ((hasDerivAt_neg z).cexp.mul hI).congr_deriv ?_
  linear_combination cexp (-z) * hFTC

/-- **DLMF 8.8.13** for `deriv`: on the slit plane, `∂Γ(a, z)/∂z = −z^{a−1} e^{−z}`. -/
@[simp]
theorem deriv_upperIncompleteGamma {z : ℂ} (hz : z ∈ slitPlane) (a : ℂ) :
    deriv (upperIncompleteGamma a) z = -(z ^ (a - 1) * cexp (-z)) :=
  (hasDerivAt_upperIncompleteGamma hz a).deriv

/-- `Γ(a, ·)` is analytic on the slit plane. -/
theorem analyticOnNhd_upperIncompleteGamma (a : ℂ) :
    AnalyticOnNhd ℂ (upperIncompleteGamma a) slitPlane :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (hasDerivAt_upperIncompleteGamma hz a).differentiableAt.differentiableWithinAt)
    isOpen_slitPlane

/-! ### Holomorphy in the parameter -/

/-- `Γ(·, z)` is entire for `z` in the slit plane. -/
theorem differentiable_upperIncompleteGamma_left {z : ℂ} (hz : z ∈ slitPlane) :
    Differentiable ℂ fun a => upperIncompleteGamma a z := by
  intro a₀
  have hmem (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : z + t ∈ slitPlane := by
    rw [add_comm]
    exact TauCeti.ofReal_add_mem_slitPlane hz (le_of_lt ht)
  -- on the unit ball about `a₀` the integrand is dominated by `K (‖t + z‖^p₁ + ‖t + z‖^p₂) e^{−t}`
  set K := Real.exp (Real.pi * (|(a₀ - 1).im| + 1))
  set p₁ := (a₀ - 1).re - 1
  set p₂ := (a₀ - 1).re + 1
  -- the integrand of the defining ray integral: that of `upperIncompleteGamma_eq_integral` times
  -- the constant `e^z`
  have hint (b : ℂ) : IntegrableOn (fun t : ℝ => (z + t) ^ (b - 1) * cexp (-(t : ℂ))) (Ioi 0) := by
    refine IntegrableOn.congr_fun
      ((integrableOn_upperIncompleteGamma_integrand b hz).const_mul (cexp z))
      (fun t _ => ?_) measurableSet_Ioi
    rw [neg_add, exp_add, exp_neg z]
    field_simp
  -- the weights `‖t + z‖ ^ p e^{−t}` are the norms of the ray integrands at `a = p + 1`
  have hnorm (p : ℝ) : IntegrableOn (fun t : ℝ => ‖(t : ℂ) + z‖ ^ p * Real.exp (-t)) (Ioi 0) := by
    have h : IntegrableOn (fun t : ℝ => ‖(z + t) ^ ((p : ℂ) + 1 - 1) * cexp (-(t : ℂ))‖)
        (Ioi 0) := (hint ((p : ℂ) + 1)).norm
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    dsimp only
    rw [norm_mul, add_sub_cancel_right, norm_cpow_real, add_comm z, ← ofReal_neg,
      norm_exp_ofReal]
  have hB := ((hnorm p₁).add (hnorm p₂)).const_mul K
  have key := TauCeti.hasDerivAt_integral_of_dominated_of_differentiableOn
    (μ := volume.restrict (Ioi 0))
    (F := fun (b : ℂ) (t : ℝ) => (z + t) ^ (b - 1) * cexp (-(t : ℂ))) (U := Metric.ball a₀ 1)
    (w₀ := a₀) (bound := fun t : ℝ =>
      K * (‖(t : ℂ) + z‖ ^ p₁ * Real.exp (-t) + ‖(t : ℂ) + z‖ ^ p₂ * Real.exp (-t)))
    Metric.isOpen_ball (Metric.mem_ball_self one_pos)
    (fun b _ => (hint b).aestronglyMeasurable)
    ?_ hB ?_
  · exact (key.differentiableAt.const_mul (cexp (-z))).congr_of_eventuallyEq
      (.of_forall fun b => upperIncompleteGamma_def b z)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht b hb
    have hb' : b - 1 ∈ Metric.closedBall (a₀ - 1) 1 := by
      rw [Metric.mem_closedBall, dist_sub_right]
      exact (Metric.mem_ball.mp hb).le
    have h := norm_cpow_le_of_mem_closedBall (slitPlane_ne_zero (hmem t ht)) hb'
    rw [norm_mul _ (cexp _), ← ofReal_neg, norm_exp_ofReal, add_comm z]
    rw [add_comm z] at h
    calc ‖((t : ℂ) + z) ^ (b - 1)‖ * Real.exp (-t)
        ≤ K * (‖(t : ℂ) + z‖ ^ p₁ + ‖(t : ℂ) + z‖ ^ p₂) * Real.exp (-t) := by gcongr
      _ = K * (‖(t : ℂ) + z‖ ^ p₁ * Real.exp (-t) + ‖(t : ℂ) + z‖ ^ p₂ * Real.exp (-t)) := by
        ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact fun b _ => ((((differentiableAt_id.sub_const 1).const_cpow
      (Or.inl (slitPlane_ne_zero (hmem t ht)))).mul_const _)).differentiableWithinAt

/-! ### The limit at the origin along the positive axis -/

/-- For `0 < Re a`, `x ↦ Γ(a, x)` is continuous on the closed positive real axis. -/
theorem continuousOn_upperIncompleteGamma_ofReal (a : ℂ) (ha : 0 < a.re) :
    ContinuousOn (fun x : ℝ => upperIncompleteGamma a x) (Ici 0) := by
  have hf : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * cexp (-(t : ℂ))) (Ioi 0) := by
    simpa only [ofReal_exp, ofReal_neg, mul_comm] using GammaIntegral_convergent ha
  simpa only [upperIncompleteGamma_ofReal] using hf.continuousOn_Ici_primitive_Ioi

/-- `Γ(a, x) → Γ(a)` as `x → 0+` along the positive real axis, for `0 < Re a`. -/
theorem tendsto_upperIncompleteGamma_ofReal_nhdsGT_zero (a : ℂ) (ha : 0 < a.re) :
    Tendsto (fun x : ℝ => upperIncompleteGamma a x) (𝓝[>] 0) (𝓝 (Gamma a)) := by
  have h := continuousOn_upperIncompleteGamma_ofReal a ha 0 (mem_Ici.mpr le_rfl)
  rw [ContinuousWithinAt, ofReal_zero, upperIncompleteGamma_zero_right ha] at h
  exact h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)

/-! ### Differential equations -/

/-- **DLMF 8.2.12** for `Γ`: on the slit plane, `w = Γ(a, ·)` satisfies
`w'' + (1 + (1 − a)/z) w' = 0`. -/
theorem upperIncompleteGamma_ode (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (deriv (upperIncompleteGamma a)) z +
      (1 + (1 - a) / z) * deriv (upperIncompleteGamma a) z = 0 := by
  have hd : deriv (upperIncompleteGamma a) =ᶠ[𝓝 z] fun w => -(w ^ (a - 1) * cexp (-w)) :=
    eventually_of_mem (isOpen_slitPlane.mem_nhds hz) fun w hw => deriv_upperIncompleteGamma hw a
  have h0 := hasDerivAt_add_cpow_mul_exp_mul (a - 1) 0 (-1) (by rwa [add_zero])
  simp only [add_zero, neg_one_mul] at h0
  have h : HasDerivAt (fun w => -(w ^ (a - 1) * cexp (-w)))
      (-(((a - 1) / z + -1) * (z ^ (a - 1) * cexp (-z)))) z := h0.neg
  rw [hd.deriv_eq, deriv_upperIncompleteGamma hz a, h.deriv]
  ring

/-- On the slit plane, `w(z) = e^z z^{1−a} Γ(a, z)` has derivative `(1 + (1 − a)/z) w(z) − 1`. -/
theorem hasDerivAt_exp_mul_cpow_one_sub_mul_upperIncompleteGamma (a : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    HasDerivAt (fun w => cexp w * w ^ (1 - a) * upperIncompleteGamma a w)
      ((1 + (1 - a) / z) * (cexp z * z ^ (1 - a) * upperIncompleteGamma a z) - 1) z := by
  have hz0 := slitPlane_ne_zero hz
  have h2 : z ^ (1 - a) * z ^ (a - 1) = 1 := by
    rw [← cpow_add _ _ hz0, sub_add_sub_cancel', sub_self, cpow_zero]
  have h3 : cexp z * cexp (-z) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  have h4 : cexp z * z ^ (1 - a) * -(z ^ (a - 1) * cexp (-z)) = -1 := by
    calc cexp z * z ^ (1 - a) * -(z ^ (a - 1) * cexp (-z))
        = -((z ^ (1 - a) * z ^ (a - 1)) * (cexp z * cexp (-z))) := by ring
      _ = -1 := by rw [h2, h3, one_mul]
  have hprod : HasDerivAt (fun w => cexp w * w ^ (1 - a))
      (cexp z * z ^ (1 - a) + cexp z * ((1 - a) * z ^ (1 - a - 1) * 1)) z :=
    (hasDerivAt_exp z).mul ((hasDerivAt_id z).cpow_const hz)
  refine (hprod.mul (hasDerivAt_upperIncompleteGamma hz a)).congr_deriv ?_
  rw [h4, cpow_sub (1 - a) 1 hz0, cpow_one]
  field_simp
  ring

/-- On the slit plane, the derivative of `w(z) = e^z z^{1−a} Γ(a, z)` is
`(1 + (1 − a)/z) w(z) − 1`. -/
@[simp]
theorem deriv_exp_mul_cpow_one_sub_mul_upperIncompleteGamma (a : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    deriv (fun w => cexp w * w ^ (1 - a) * upperIncompleteGamma a w) z =
      (1 + (1 - a) / z) * (cexp z * z ^ (1 - a) * upperIncompleteGamma a z) - 1 :=
  (hasDerivAt_exp_mul_cpow_one_sub_mul_upperIncompleteGamma a hz).deriv

/-- **DLMF 8.2.13**: on the slit plane, `w(z) = e^z z^{1−a} Γ(a, z)` satisfies
`w'' − (1 + (1 − a)/z) w' + ((1 − a)/z²) w = 0`. -/
theorem exp_mul_cpow_one_sub_mul_upperIncompleteGamma_ode (a : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    deriv (deriv fun w => cexp w * w ^ (1 - a) * upperIncompleteGamma a w) z -
        (1 + (1 - a) / z) * deriv (fun w => cexp w * w ^ (1 - a) * upperIncompleteGamma a w) z +
      (1 - a) / z ^ 2 * (cexp z * z ^ (1 - a) * upperIncompleteGamma a z) = 0 := by
  have hz0 := slitPlane_ne_zero hz
  have hW := hasDerivAt_exp_mul_cpow_one_sub_mul_upperIncompleteGamma a hz
  have hd : deriv (fun w => cexp w * w ^ (1 - a) * upperIncompleteGamma a w) =ᶠ[𝓝 z]
      fun w => (1 + (1 - a) * w⁻¹) * (cexp w * w ^ (1 - a) * upperIncompleteGamma a w) - 1 :=
    eventually_of_mem (isOpen_slitPlane.mem_nhds hz) fun w hw => by
      rw [deriv_exp_mul_cpow_one_sub_mul_upperIncompleteGamma a hw, div_eq_mul_inv]
  have h : HasDerivAt
      (fun w => (1 + (1 - a) * w⁻¹) * (cexp w * w ^ (1 - a) * upperIncompleteGamma a w) - 1)
      ((1 - a) * -(z ^ 2)⁻¹ * (cexp z * z ^ (1 - a) * upperIncompleteGamma a z) +
        (1 + (1 - a) * z⁻¹) *
          ((1 + (1 - a) / z) * (cexp z * z ^ (1 - a) * upperIncompleteGamma a z) - 1)) z :=
    ((((hasDerivAt_inv hz0).const_mul (1 - a)).const_add 1).mul hW).sub_const 1
  rw [hd.deriv_eq, deriv_exp_mul_cpow_one_sub_mul_upperIncompleteGamma a hz, h.deriv]
  field_simp
  ring

end Complex
