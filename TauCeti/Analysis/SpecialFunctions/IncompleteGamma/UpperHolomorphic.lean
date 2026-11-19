/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Upper
import Mathlib.Analysis.Complex.Liouville
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.Analysis.SpecialFunctions.Pow.ParametricIntegral

/-!
# Holomorphy of the upper incomplete Gamma function

For `z` in the slit plane, the upper incomplete Gamma function `Γ(a, z)`, defined by the integral
along the horizontal ray from `z`, is holomorphic in `z` and entire in `a`. Together with the
identity theorem this yields the complementary relation `γ(a, z) + Γ(a, z) = Γ(a)` and the
differential equations of `Γ(a, ·)` and `γ(a, ·)`.

## Main results

* `Complex.hasDerivAt_upperIncompleteGamma`, `Complex.hasDerivAt_lowerIncompleteGamma`:
  `∂Γ(a, z)/∂z = −z^{a−1} e^{−z}` on the slit plane, and `∂γ(a, z)/∂z = z^{a−1} e^{−z}` there
  for `a ∉ −ℕ` (DLMF 8.8.13);
* `Complex.differentiable_upperIncompleteGamma_left`: `Γ(·, z)` is entire;
* `Complex.regularizedGammaQ_eq_upperIncompleteGamma_div`: `Q(a, z) = Γ(a, z)/Γ(a)` for every
  `a`, with Mathlib's entire reciprocal of `Γ` (DLMF 8.2.4–8.2.5);
* `Complex.upperIncompleteGamma_add_lowerIncompleteGamma`: `Γ(a, z) + γ(a, z) = Γ(a)` for
  `a ∉ −ℕ` (DLMF 8.2.3);
* `Complex.tendsto_upperIncompleteGamma_ofReal_nhdsGT_zero`: `Γ(a, x) → Γ(a)` as `x → 0+`;
* `Complex.upperIncompleteGamma_ode`, `Complex.lowerIncompleteGamma_ode`: DLMF 8.2.12;
* `Complex.exp_mul_cpow_one_sub_mul_upperIncompleteGamma_ode`: DLMF 8.2.13 for
  `e^z z^{1−a} Γ(a, z)`.

## Implementation notes

The derivative in `z` differentiates under the ray integral and integrates the derivative of
`t ↦ e^{−t} (t + z)^{a−1}` along the ray. The derivative in `a` is dominated by the Cauchy
estimate on circles of radius one. DLMF 8.2.3 holds on the positive axis by Mathlib's splitting
of Euler's integral, extends to the slit plane by the identity theorem in `z` for `0 < Re a`, and
then to every `a` in the form `Q(a, z) = Γ(a)⁻¹ Γ(a, z)` by the identity theorem in `a`, both
sides being entire.

## References

* NIST Digital Library of Mathematical Functions, §§8.2, 8.8, <https://dlmf.nist.gov/8.2>.

The proofs are new; the statements follow DLMF.
-/

public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped Topology

namespace Complex

/-- The weighted ray integrand `t ↦ e^{−t} (t + z)^b` is integrable on `(0, ∞)` for `z` in the
slit plane and every exponent `b`. -/
theorem integrableOn_exp_neg_mul_ofReal_add_cpow {z : ℂ} (hz : z ∈ slitPlane) (b : ℂ) :
    IntegrableOn (fun t : ℝ => cexp (-(t : ℂ)) * ((t : ℂ) + z) ^ b) (Ioi 0) := by
  simpa only [add_sub_cancel_right, mul_comm, add_comm] using
    integrableOn_upperIncompleteGamma_integrand (b + 1) hz

/-- **DLMF 8.8.13**: on the slit plane, `Γ(a, ·)` has derivative `−z^{a−1} e^{−z}`. -/
theorem hasDerivAt_upperIncompleteGamma {z : ℂ} (hz : z ∈ slitPlane) (a : ℂ) :
    HasDerivAt (upperIncompleteGamma a) (-(z ^ (a - 1) * cexp (-z))) z := by
  have hfun : upperIncompleteGamma a =
      fun w => cexp (-w) * ∫ t in Ioi (0 : ℝ), cexp (-(t : ℂ)) * ((t : ℂ) + w) ^ (a - 1) := by
    funext w
    rw [upperIncompleteGamma_def]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [add_comm, mul_comm]
  have hI := TauCeti.hasDerivAt_integral_mul_ofReal_add_cpow hz
    (integrableOn_exp_neg_mul_ofReal_add_cpow hz (a - 1))
  -- the integral of the derivative along the ray, by the fundamental theorem of calculus
  have hG (t : ℝ) (ht : t ∈ Ici (0 : ℝ)) :
      HasDerivAt (fun s : ℝ => cexp (-(s : ℂ)) * ((s : ℂ) + z) ^ (a - 1))
        ((a - 1) * (cexp (-(t : ℂ)) * ((t : ℂ) + z) ^ (a - 1 - 1)) -
          cexp (-(t : ℂ)) * ((t : ℂ) + z) ^ (a - 1)) t := by
    have h : HasDerivAt (fun w : ℂ => cexp (-w) * (w + z) ^ (a - 1))
        (cexp (-(t : ℂ)) * -1 * ((t : ℂ) + z) ^ (a - 1) +
          cexp (-(t : ℂ)) * ((a - 1) * ((t : ℂ) + z) ^ (a - 1 - 1) * 1)) t :=
      (hasDerivAt_neg (t : ℂ)).cexp.mul (((hasDerivAt_id' (t : ℂ)).add_const z).cpow_const
        (TauCeti.ofReal_add_mem_slitPlane hz ht))
    exact h.comp_ofReal.congr_deriv (by ring)
  have h₂ := (integrableOn_exp_neg_mul_ofReal_add_cpow hz (a - 1 - 1)).const_mul (a - 1)
  have h₁ := integrableOn_exp_neg_mul_ofReal_add_cpow hz (a - 1)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' hG (h₂.sub h₁)
    (tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun t ht => hG t (mem_Ici_of_Ioi ht))
      (h₂.sub h₁) h₁)
  rw [integral_sub h₂ h₁, integral_const_mul] at hFTC
  simp only [ofReal_zero, zero_add, neg_zero, exp_zero, one_mul, zero_sub] at hFTC
  rw [hfun]
  refine ((hasDerivAt_neg z).cexp.mul hI).congr_deriv ?_
  linear_combination cexp (-z) * hFTC

/-! ### Holomorphy in the parameter -/

/-- A bound on the ray integrand `(z + t)^{b−1} e^{−t}` that is uniform for `b` in the closed
ball of radius `R` about `a₀`. -/
theorem norm_add_cpow_sub_one_mul_exp_neg_le {z : ℂ} {t : ℝ} (hw : z + t ≠ 0) {a₀ b : ℂ}
    {R : ℝ} (hb : b ∈ closedBall a₀ R) :
    ‖(z + t) ^ (b - 1) * cexp (-(t : ℂ))‖ ≤
      Real.exp (Real.pi * (|a₀.im| + R)) *
        ((‖(t : ℂ) + z‖ ^ (a₀.re - 1 - R) + ‖(t : ℂ) + z‖ ^ (a₀.re - 1 + R)) *
          Real.exp (-t)) := by
  rw [add_comm] at hw
  have hb' : ‖b - a₀‖ ≤ R := by rwa [← dist_eq_norm]
  have hre : |b.re - a₀.re| ≤ R := by simpa using (abs_re_le_norm (b - a₀)).trans hb'
  have him : |b.im| ≤ |a₀.im| + R := by
    have := (abs_im_le_norm (b - a₀)).trans hb'
    rw [sub_im] at this
    linarith [abs_sub_abs_le_abs_sub b.im a₀.im]
  have hpow : ‖(t : ℂ) + z‖ ^ (b - 1).re ≤
      ‖(t : ℂ) + z‖ ^ (a₀.re - 1 - R) + ‖(t : ℂ) + z‖ ^ (a₀.re - 1 + R) :=
    Real.rpow_le_rpow_add_rpow_of_mem_Icc (norm_pos_iff.mpr hw)
      ⟨by simp only [sub_re, one_re]; linarith [abs_le.mp hre],
        by simp only [sub_re, one_re]; linarith [abs_le.mp hre]⟩
  have harg : (Real.exp (((t : ℂ) + z).arg * (b - 1).im))⁻¹ ≤
      Real.exp (Real.pi * (|a₀.im| + R)) := by
    refine (inv_exp_arg_mul_le_exp_pi_mul_abs _ _).trans (Real.exp_le_exp.mpr ?_)
    simp only [sub_im, one_im, sub_zero]
    exact mul_le_mul_of_nonneg_left him Real.pi_pos.le
  rw [norm_mul, norm_exp, neg_re, ofReal_re, add_comm z]
  calc ‖((t : ℂ) + z) ^ (b - 1)‖ * Real.exp (-t)
      ≤ ‖(t : ℂ) + z‖ ^ (b - 1).re * (Real.exp (((t : ℂ) + z).arg * (b - 1).im))⁻¹ *
          Real.exp (-t) := by
        rw [← div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (norm_cpow_le _ _) (Real.exp_pos _).le
    _ ≤ _ := by
        rw [mul_comm (_ ^ _), mul_assoc]
        gcongr

/-- The norm `‖t + z‖^p e^{−t}` is integrable on `(0, ∞)` for `z` in the slit plane and every
real `p`. -/
theorem integrableOn_norm_ofReal_add_rpow_mul_exp_neg {z : ℂ} (hz : z ∈ slitPlane) (p : ℝ) :
    IntegrableOn (fun t : ℝ => ‖(t : ℂ) + z‖ ^ p * Real.exp (-t)) (Ioi 0) := by
  refine IntegrableOn.congr_fun (integrableOn_exp_neg_mul_ofReal_add_cpow hz p).norm
    (fun t _ => ?_) measurableSet_Ioi
  rw [norm_mul, norm_cpow_real, norm_exp, neg_re, ofReal_re, mul_comm]

/-- The parameter derivative of the ray integrand: `∂_b ((z + t)^{b−1} e^{−t}) =
(z + t)^{b−1} log (z + t) e^{−t}`. -/
theorem hasDerivAt_add_cpow_sub_one_mul_exp_neg_left {z : ℂ} {t : ℝ} (hw : z + t ≠ 0)
    (b : ℂ) :
    HasDerivAt (fun c => (z + t) ^ (c - 1) * cexp (-(t : ℂ)))
      ((z + t) ^ (b - 1) * log (z + t) * cexp (-(t : ℂ))) b := by
  simpa only [mul_one] using (((hasDerivAt_id' b).sub_const 1).const_cpow (c := z + t)
    (Or.inl hw)).mul_const (cexp (-(t : ℂ)))

/-- The Cauchy estimate on circles of radius one bounds the parameter derivative of the ray
integrand uniformly for `b` in the unit ball about `a₀`. -/
theorem norm_add_cpow_sub_one_mul_log_mul_exp_neg_le {z : ℂ} {t : ℝ} (hw : z + t ≠ 0)
    {a₀ b : ℂ} (hb : b ∈ ball a₀ 1) :
    ‖(z + t) ^ (b - 1) * log (z + t) * cexp (-(t : ℂ))‖ ≤
      Real.exp (Real.pi * (|a₀.im| + 2)) *
        ((‖(t : ℂ) + z‖ ^ (a₀.re - 1 - 2) + ‖(t : ℂ) + z‖ ^ (a₀.re - 1 + 2)) *
          Real.exp (-t)) := by
  rw [← (hasDerivAt_add_cpow_sub_one_mul_exp_neg_left hw b).deriv]
  simpa using norm_deriv_le_of_forall_mem_sphere_norm_le one_pos
    (Differentiable.diffContOnCl fun c =>
      (hasDerivAt_add_cpow_sub_one_mul_exp_neg_left hw c).differentiableAt)
    fun c hc => norm_add_cpow_sub_one_mul_exp_neg_le hw (R := 2) (mem_closedBall.mpr
      (by linarith [dist_triangle c b a₀, mem_sphere.mp hc, mem_ball.mp hb]))

/-- `Γ(·, z)` is entire for `z` in the slit plane. -/
theorem differentiable_upperIncompleteGamma_left {z : ℂ} (hz : z ∈ slitPlane) :
    Differentiable ℂ fun a => upperIncompleteGamma a z := by
  intro a₀
  have hB := IntegrableOn.congr_fun
    (((integrableOn_norm_ofReal_add_rpow_mul_exp_neg hz (a₀.re - 1 - 2)).add
      (integrableOn_norm_ofReal_add_rpow_mul_exp_neg hz (a₀.re - 1 + 2))).const_mul
        (Real.exp (Real.pi * (|a₀.im| + 2))))
    (g := fun t : ℝ => Real.exp (Real.pi * (|a₀.im| + 2)) *
      ((‖(t : ℂ) + z‖ ^ (a₀.re - 1 - 2) + ‖(t : ℂ) + z‖ ^ (a₀.re - 1 + 2)) * Real.exp (-t)))
    (fun t _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi
  have hmem (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : z + t ∈ slitPlane := by
    rw [add_comm]
    exact TauCeti.ofReal_add_mem_slitPlane hz (le_of_lt ht)
  have hpow (b : ℂ) : ContinuousOn (fun t : ℝ => (z + t) ^ b) (Ioi 0) :=
    ContinuousOn.cpow_const (by fun_prop) hmem
  have hlog : ContinuousOn (fun t : ℝ => log (z + t)) (Ioi 0) :=
    ContinuousOn.clog (by fun_prop) hmem
  have hexp : ContinuousOn (fun t : ℝ => cexp (-(t : ℂ))) (Ioi 0) := by fun_prop
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun (b : ℂ) (t : ℝ) => (z + t) ^ (b - 1) * cexp (-(t : ℂ)))
    (F' := fun (b : ℂ) (t : ℝ) => (z + t) ^ (b - 1) * log (z + t) * cexp (-(t : ℂ)))
    (ball_mem_nhds a₀ one_pos)
    (.of_forall fun b => ((hpow _).mul hexp).aestronglyMeasurable measurableSet_Ioi)
    (integrableOn_upperIncompleteGamma_integrand a₀ hz)
    ((((hpow _).mul hlog).mul hexp).aestronglyMeasurable measurableSet_Ioi)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht b hb
        exact norm_add_cpow_sub_one_mul_log_mul_exp_neg_le
          (slitPlane_ne_zero (hmem t ht)) hb) hB
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht b _
        exact hasDerivAt_add_cpow_sub_one_mul_exp_neg_left (slitPlane_ne_zero (hmem t ht)) b)
  exact (key.2.differentiableAt.const_mul (cexp (-z))).congr_of_eventuallyEq
    (.of_forall fun b => upperIncompleteGamma_def b z)

/-! ### The complementary relation -/

/-- On the real axis, `γ(a, x)` is Mathlib's `Complex.partialGamma a x` when `0 < Re a`. -/
theorem lowerIncompleteGamma_ofReal_eq_partialGamma {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    lowerIncompleteGamma a x = partialGamma a x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [partialGamma]
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx
  have hsub := intervalIntegral.integral_comp_mul_left
    (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ (a - 1)) (a := 0) (b := 1) hx
  have hscale : ∫ s in (0 : ℝ)..1, (Real.exp (-(x * s)) : ℂ) * ((x * s : ℝ) : ℂ) ^ (a - 1) =
      (x : ℂ) ^ (a - 1) * ∫ s in (0 : ℝ)..1, (s : ℂ) ^ (a - 1) * cexp (-(x * s)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs0 : 0 ≤ s := by
      rw [uIcc_of_le zero_le_one] at hs
      exact hs.1
    simp only [ofReal_mul, mul_comm (x : ℂ), TauCeti.ofReal_mul_cpow hs0, ofReal_exp, ofReal_neg]
    ring
  simp only [mul_zero, mul_one] at hsub
  rw [hscale] at hsub
  rw [lowerIncompleteGamma_eq_integral ha, partialGamma]
  have hpow : (x : ℂ) ^ a = x * (x : ℂ) ^ (a - 1) := by
    rw [cpow_sub _ _ hx0, cpow_one]
    field_simp
  rw [hpow, mul_assoc, hsub, real_smul, ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]

/-- `γ(a, ·)` is holomorphic on the slit plane. -/
theorem differentiableAt_lowerIncompleteGamma_right (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    DifferentiableAt ℂ (lowerIncompleteGamma a) z := by
  have h := ((((hasDerivAt_id z).cpow_const (c := a) hz).differentiableAt.mul
    (differentiable_tricomiIncompleteGamma a z)).const_mul (Gamma a))
  exact h.congr_of_eventuallyEq (.of_forall fun w => by
    simp [lowerIncompleteGamma_def, regularizedGamma_def])

/-- **DLMF 8.2.4–8.2.5**: `Q(a, z) = Γ(a, z) / Γ(a)` on the slit plane, for every `a`. At
`a ∈ −ℕ` both sides vanish: `Γ(a)⁻¹` is Mathlib's entire reciprocal. -/
theorem regularizedGammaQ_eq_upperIncompleteGamma_div (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    regularizedGammaQ a z = upperIncompleteGamma a z / Gamma a := by
  -- for `0 < Re a`, the relation `Γ(a, z) + γ(a, z) = Γ(a)` holds on the positive axis, hence on
  -- the slit plane by the identity theorem in `z`
  have hpos {b : ℂ} (hb : 0 < b.re) :
      upperIncompleteGamma b z + lowerIncompleteGamma b z = Gamma b := by
    have hU : AnalyticOnNhd ℂ (fun w => upperIncompleteGamma b w + lowerIncompleteGamma b w)
        slitPlane :=
      DifferentiableOn.analyticOnNhd (fun w hw =>
        ((hasDerivAt_upperIncompleteGamma hw b).differentiableAt.add
          (differentiableAt_lowerIncompleteGamma_right b hw)).differentiableWithinAt)
        isOpen_slitPlane
    refine hU.eqOn_slitPlane_of_ofReal_pos_eq analyticOnNhd_const (fun x hx => ?_) hz
    rw [lowerIncompleteGamma_ofReal_eq_partialGamma hb, add_comm,
      partialGamma_add_upperIncompleteGamma hb hx.le]
  -- both sides are entire in `a` and agree on `0 < Re a`
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hQ : AnalyticOnNhd ℂ (fun b => regularizedGammaQ b z) univ := fun b _ =>
    ((differentiable_const 1).sub (differentiable_regularizedGamma_left hz0)).analyticAt b
      |>.congr (.of_forall fun b => (regularizedGammaQ_def b z).symm)
  have hR : AnalyticOnNhd ℂ (fun b => upperIncompleteGamma b z / Gamma b) univ := fun b _ =>
    ((differentiable_upperIncompleteGamma_left hz).mul differentiable_one_div_Gamma).analyticAt b
      |>.congr (.of_forall fun b => (div_eq_mul_inv _ _).symm)
  refine congrFun (hQ.eq_of_eventuallyEq hR (z₀ := 1) ?_) a
  filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
    (by simp : (0 : ℝ) < (1 : ℂ).re)] with b hb
  have hG := Gamma_ne_zero_of_re_pos hb
  have h := hpos hb
  rw [lowerIncompleteGamma_def] at h
  rw [regularizedGammaQ_def, eq_div_iff hG]
  linear_combination -h

/-- **DLMF 8.2.3**: `Γ(a, z) + γ(a, z) = Γ(a)` on the slit plane, for `a ∉ −ℕ`. -/
theorem upperIncompleteGamma_add_lowerIncompleteGamma {a z : ℂ} (ha : ∀ n : ℕ, a ≠ -n)
    (hz : z ∈ slitPlane) :
    upperIncompleteGamma a z + lowerIncompleteGamma a z = Gamma a := by
  have h := regularizedGammaQ_eq_upperIncompleteGamma_div a hz
  rw [regularizedGammaQ_def, eq_div_iff (Gamma_ne_zero ha)] at h
  rw [← h, lowerIncompleteGamma_def]
  ring

/-- `Γ(a, x) → Γ(a)` as `x → 0+` along the positive real axis, for `0 < Re a`. -/
theorem tendsto_upperIncompleteGamma_ofReal_nhdsGT_zero {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun x : ℝ => upperIncompleteGamma a x) (𝓝[>] 0) (𝓝 (Gamma a)) := by
  have hint : IntervalIntegrable (fun t : ℝ => (Real.exp (-t) : ℂ) * (t : ℂ) ^ (a - 1))
      volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      ((GammaIntegral_convergent ha).mono_set Ioc_subset_Ioi_self)
  have hP : Tendsto (fun x : ℝ => partialGamma a x) (𝓝[>] 0) (𝓝 0) := by
    have h := (intervalIntegral.continuousOn_primitive_interval' hint left_mem_uIcc 0
      left_mem_uIcc).tendsto
    rw [intervalIntegral.integral_same] at h
    rw [← nhdsWithin_Ioo_eq_nhdsGT zero_lt_one]
    exact h.mono_left (nhdsWithin_mono _ (Ioo_subset_Icc_self.trans
      (uIcc_of_le zero_le_one).symm.subset))
  have h := (tendsto_const_nhds (x := Gamma a)).sub hP
  rw [sub_zero] at h
  refine h.congr' (eventually_nhdsWithin_of_forall fun x hx => ?_)
  rw [← partialGamma_add_upperIncompleteGamma ha (le_of_lt hx), add_sub_cancel_left]

/-! ### Derivatives and differential equations -/

/-- **DLMF 8.8.13** for `γ`: on the slit plane, `γ(a, ·)` has derivative `z^{a−1} e^{−z}` for
`a ∉ −ℕ`. -/
theorem hasDerivAt_lowerIncompleteGamma {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ}
    (hz : z ∈ slitPlane) :
    HasDerivAt (lowerIncompleteGamma a) (z ^ (a - 1) * cexp (-z)) z := by
  have h : (fun w => Gamma a - upperIncompleteGamma a w) =ᶠ[𝓝 z] lowerIncompleteGamma a :=
    eventually_of_mem (isOpen_slitPlane.mem_nhds hz) fun w hw => by
      rw [← upperIncompleteGamma_add_lowerIncompleteGamma ha hw]
      ring
  simpa using ((hasDerivAt_upperIncompleteGamma hz a).const_sub (Gamma a)).congr_of_eventuallyEq
    h.symm

/-- The derivative of `w ↦ w^{a−1} e^{−w}` on the slit plane is
`−(1 + (1 − a)/z) z^{a−1} e^{−z}`. -/
theorem hasDerivAt_cpow_sub_one_mul_exp_neg (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun w => w ^ (a - 1) * cexp (-w))
      (-(1 + (1 - a) / z) * (z ^ (a - 1) * cexp (-z))) z := by
  have hz0 := slitPlane_ne_zero hz
  have hpow : z ^ (a - 1 - 1) = z ^ (a - 1) / z := by rw [cpow_sub _ _ hz0, cpow_one]
  refine (((hasDerivAt_id z).cpow_const (c := a - 1) hz).mul (hasDerivAt_neg z).cexp).congr_deriv ?_
  simp only [id, hpow]
  field_simp
  ring

/-- **DLMF 8.2.12** for `Γ`: on the slit plane, `w = Γ(a, ·)` satisfies
`w'' + (1 + (1 − a)/z) w' = 0`. -/
theorem upperIncompleteGamma_ode (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (deriv (upperIncompleteGamma a)) z +
      (1 + (1 - a) / z) * deriv (upperIncompleteGamma a) z = 0 := by
  have hd : deriv (upperIncompleteGamma a) =ᶠ[𝓝 z] fun w => -(w ^ (a - 1) * cexp (-w)) :=
    eventually_of_mem (isOpen_slitPlane.mem_nhds hz) fun w hw =>
      (hasDerivAt_upperIncompleteGamma hw a).deriv
  have h : HasDerivAt (fun w => -(w ^ (a - 1) * cexp (-w)))
      (-(-(1 + (1 - a) / z) * (z ^ (a - 1) * cexp (-z)))) z :=
    (hasDerivAt_cpow_sub_one_mul_exp_neg a hz).neg
  rw [hd.deriv_eq, (hasDerivAt_upperIncompleteGamma hz a).deriv, h.deriv]
  ring

/-- **DLMF 8.2.12** for `γ`: on the slit plane, `w = γ(a, ·)` satisfies
`w'' + (1 + (1 − a)/z) w' = 0`. At `a ∈ −ℕ`, `γ(a, ·)` is Mathlib's junk value `0`. -/
theorem lowerIncompleteGamma_ode (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (deriv (lowerIncompleteGamma a)) z +
      (1 + (1 - a) / z) * deriv (lowerIncompleteGamma a) z = 0 := by
  by_cases ha : ∀ n : ℕ, a ≠ -n
  · have hd : deriv (lowerIncompleteGamma a) =ᶠ[𝓝 z] fun w => w ^ (a - 1) * cexp (-w) :=
      eventually_of_mem (isOpen_slitPlane.mem_nhds hz) fun w hw =>
        (hasDerivAt_lowerIncompleteGamma ha hw).deriv
    rw [hd.deriv_eq, (hasDerivAt_lowerIncompleteGamma ha hz).deriv,
      (hasDerivAt_cpow_sub_one_mul_exp_neg a hz).deriv]
    ring
  · push Not at ha
    obtain ⟨n, rfl⟩ := ha
    have h0 : lowerIncompleteGamma (-n) = fun _ => 0 :=
      funext fun w => by simp [lowerIncompleteGamma_def, Gamma_neg_nat_eq_zero]
    simp [h0]

/-- On the slit plane, `w(z) = e^z z^{1−a} Γ(a, z)` has derivative `(1 + (1 − a)/z) w(z) − 1`. -/
theorem hasDerivAt_exp_mul_cpow_one_sub_mul_upperIncompleteGamma (a : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    HasDerivAt (fun w => cexp w * w ^ (1 - a) * upperIncompleteGamma a w)
      ((1 + (1 - a) / z) * (cexp z * z ^ (1 - a) * upperIncompleteGamma a z) - 1) z := by
  have hz0 := slitPlane_ne_zero hz
  have h1 : z ^ (1 - a - 1) = z ^ (1 - a) / z := by rw [cpow_sub _ _ hz0, cpow_one]
  have h2 : z ^ (1 - a) * z ^ (a - 1) = 1 := by
    rw [← cpow_add _ _ hz0]
    ring_nf
    exact cpow_zero z
  have h3 : cexp z * cexp (-z) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  have h4 : cexp z * z ^ (1 - a) * -(z ^ (a - 1) * cexp (-z)) = -1 := by
    calc cexp z * z ^ (1 - a) * -(z ^ (a - 1) * cexp (-z))
        = -((z ^ (1 - a) * z ^ (a - 1)) * (cexp z * cexp (-z))) := by ring
      _ = -1 := by rw [h2, h3, one_mul]
  have hprod : HasDerivAt (fun w => cexp w * w ^ (1 - a))
      (cexp z * z ^ (1 - a) + cexp z * ((1 - a) * z ^ (1 - a - 1) * 1)) z :=
    (hasDerivAt_exp z).mul ((hasDerivAt_id z).cpow_const hz)
  refine (hprod.mul (hasDerivAt_upperIncompleteGamma hz a)).congr_deriv ?_
  rw [h4, h1]
  field_simp
  ring

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
      rw [(hasDerivAt_exp_mul_cpow_one_sub_mul_upperIncompleteGamma a hw).deriv, div_eq_mul_inv]
  have h : HasDerivAt
      (fun w => (1 + (1 - a) * w⁻¹) * (cexp w * w ^ (1 - a) * upperIncompleteGamma a w) - 1)
      ((1 - a) * -(z ^ 2)⁻¹ * (cexp z * z ^ (1 - a) * upperIncompleteGamma a z) +
        (1 + (1 - a) * z⁻¹) *
          ((1 + (1 - a) / z) * (cexp z * z ^ (1 - a) * upperIncompleteGamma a z) - 1)) z :=
    ((((hasDerivAt_inv hz0).const_mul (1 - a)).const_add 1).mul hW).sub_const 1
  rw [hd.deriv_eq, hW.deriv, h.deriv]
  field_simp
  ring

end Complex
