/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Beta.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes

/-!
# Euler's second beta integral with complex parameters

For parameters `a`, `b` with positive real parts and a positive real shift `x`, the
kernel `t ^ (a - 1) * (x + t) ^ (-(a + b))` is absolutely integrable on the positive
half-line. Its integral is `Gamma a * Gamma b / Gamma (a + b) * x ^ (-b)`.
All complex powers use the principal branch. In the beta integrals their bases are positive
real numbers; the Stieltjes section below also takes the principal power `z ^ (-α)` of a
complex `z` in the slit plane.

The unit-shift case is already supplied by `Complex.hasMellin_one_add_cpow_neg`.
Scaling gives the arbitrary positive shift. These formulas supply the model integrals
for expansions of Stieltjes transforms.

For `0 < α < 1` the Stieltjes transform of `t ^ (-α)` is
`∫₀^∞ t ^ (-α) (t + z)⁻¹ dt = π / sin (π α) * z ^ (-α)` for every `z` in the slit plane
(`Complex.integral_cpow_neg_mul_inv_add`). For positive real `z` this is Euler's integral
`B(1 - α, α) = π / sin (π α)` after scaling; both sides are holomorphic in `z` on the slit plane,
so the identity theorem extends it there.

The case `α = 1` diverges at `0`; its model integral over `(c, ∞)`, `c > 0`, is
`∫_c^∞ t⁻¹ (t + z)⁻¹ dt = z⁻¹ (log (c + z) - log c)` (`Complex.integral_Ioi_inv_mul_inv_add`),
with the real case `Real.integral_Ioi_inv_mul_add` for `z = r > 0`.

## References

* NIST Digital Library of Mathematical Functions, §2.6(i), equation (2.6.4),
  <https://dlmf.nist.gov/2.6.E4>.
-/

public section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace Complex

private lemma betaKernel_scale (a b : ℂ) {x t : ℝ} (hx : 0 < x) :
    ((x * t : ℝ) : ℂ) ^ (a - 1) * ((x + x * t : ℝ) : ℂ) ^ (-(a + b)) =
      (x : ℂ) ^ (-b - 1) * ((t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (-(a + b))) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hfactor : x + x * t = x * (1 + t) := by ring
  have harg (z : ℂ) : (x : ℂ).arg + z.arg ∈ Ioc (-Real.pi) Real.pi := by
    simpa only [arg_ofReal_of_nonneg hx.le, zero_add] using
      (mem_Ioc.mpr ⟨neg_pi_lt_arg z, arg_le_pi z⟩)
  rw [hfactor, ofReal_mul, ofReal_mul, mul_cpow (harg _) _, mul_cpow (harg _) _,
    ofReal_add, ofReal_one]
  calc
    _ = ((x : ℂ) ^ (a - 1) * (x : ℂ) ^ (-(a + b))) *
        ((t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (-(a + b))) := by ring
    _ = _ := by
      rw [← cpow_add _ _ hx0]
      congr 2
      ring

/-- The shifted complex beta kernel is absolutely integrable on the positive half-line.
Both endpoint conditions are encoded by the positive real parts of the parameters. -/
theorem integrableOn_cpow_mul_add_cpow {a b : ℂ} {x : ℝ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * ((x + t : ℝ) : ℂ) ^ (-(a + b)))
      (Ioi 0) := by
  have hm := hasMellin_one_add_cpow_neg (s := a) (a := a + b) ha (by simp; linarith)
  have hi : IntegrableOn (fun t : ℝ =>
      (x : ℂ) ^ (-b - 1) * ((t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (-(a + b))))
      (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul, mul_left_comm] using
      hm.1.const_smul ((x : ℂ) ^ (-b - 1))
  have hs := IntegrableOn.congr_fun hi
    (fun t _ => (betaKernel_scale a b hx).symm) measurableSet_Ioi
  simpa only [mul_zero] using
    (integrableOn_Ioi_comp_mul_left_iff _ 0 hx).mp hs

/-- The Beta-type model integral with positive real shift and complex exponents
(DLMF 2.6.4), using principal complex powers. -/
theorem integral_cpow_mul_add_cpow {a b : ℂ} {x : ℝ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (a - 1) * ((x + t : ℝ) : ℂ) ^ (-(a + b))) =
      Gamma a * Gamma b / Gamma (a + b) * (x : ℂ) ^ (-b) := by
  have hscale := integral_comp_mul_left_Ioi'
    (fun t : ℝ => (t : ℂ) ^ (a - 1) * ((x + t : ℝ) : ℂ) ^ (-(a + b))) 0 hx
  rw [mul_zero] at hscale
  rw [← hscale, setIntegral_congr_fun measurableSet_Ioi
    (fun (t : ℝ) _ => betaKernel_scale a b hx (t := t)),
    integral_const_mul, real_smul]
  have hm := (hasMellin_one_add_cpow_neg (s := a) (a := a + b) ha (by simp; linarith)).2
  simp only [mellin, smul_eq_mul, add_sub_cancel_left] at hm
  rw [hm]
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  calc
    _ = (Gamma a * Gamma b / Gamma (a + b)) *
        ((x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (-b - 1)) := by rw [cpow_one]; ring
    _ = _ := by rw [← cpow_add _ _ hx0]; congr 2; ring

-- The elementary and half-integer cases check the normalization and the shift factor.
example {x : ℝ} (hx : 0 < x) :
    (∫ t in Ioi (0 : ℝ), ((x + t : ℝ) : ℂ) ^ (-2 : ℂ)) = (x : ℂ)⁻¹ := by
  convert integral_cpow_mul_add_cpow (a := 1) (b := 1) (by norm_num) (by norm_num) hx using 1 <;>
    norm_num [cpow_neg_one, Gamma_nat_eq_factorial]

example :
    (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (-(1 / 2) : ℂ) * (1 + (t : ℂ))⁻¹) = (Real.pi : ℂ) := by
  have h := integral_cpow_mul_add_cpow (a := 1 / 2) (b := 1 / 2) (x := 1)
    (by norm_num) (by norm_num) zero_lt_one
  norm_num [cpow_neg_one, Gamma_one_half_eq, ← sq] at h
  convert h using 1
  rw [← cpow_nat_mul]
  norm_num

/-! ### The Stieltjes transform of `t ^ (-α)` -/

section Stieltjes

variable {α : ℝ}

/-- For `0 < α < 1` and `z` in the slit plane, `t ↦ t ^ (-α) (t + z)⁻¹` is integrable on the
positive half-line. -/
theorem integrableOn_cpow_neg_mul_inv_add (hα₀ : 0 < α) (hα₁ : α < 1) {z : ℂ}
    (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (-(α : ℂ)) * ((t : ℂ) + z)⁻¹) (Ioi 0) := by
  obtain ⟨c, hc, hcz⟩ := TauCeti.exists_pos_mul_one_add_le_norm_ofReal_add hz
  refine ((TauCeti.integrableOn_rpow_neg_div_add α 1 hα₀ hα₁ one_pos).const_mul c⁻¹).mono' ?_ ?_
  · exact (by fun_prop : Measurable fun t : ℝ ↦
      (t : ℂ) ^ (-(α : ℂ)) * ((t : ℂ) + z)⁻¹).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
    rw [norm_mul, norm_inv, norm_cpow_eq_rpow_re_of_pos ht, neg_re, ofReal_re]
    calc t ^ (-α) * ‖(t : ℂ) + z‖⁻¹ ≤ t ^ (-α) * (c * (1 + t))⁻¹ := by
          gcongr
          exact hcz t ht.le
      _ = c⁻¹ * (t ^ (-α) / (t + 1)) := by
          field_simp
          ring

/-- The integral `∫₀^∞ t ^ (-α) (t + z)⁻¹ dt` is holomorphic in `z` on the slit plane. -/
private theorem differentiableOn_integral_cpow_neg_mul_inv_add (hα₀ : 0 < α) (hα₁ : α < 1) :
    DifferentiableOn ℂ (fun z : ℂ ↦ ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (-(α : ℂ)) * ((t : ℂ) + z)⁻¹)
      slitPlane := by
  intro z₀ hz₀
  -- on a ball around `z₀`, `‖t + w‖ ≥ c (1 + t)` uniformly
  obtain ⟨c, hc, hcz⟩ := TauCeti.exists_pos_forall_mem_ball_mul_one_add_le_norm_add hz₀
  have hlow {w : ℂ} (hw : w ∈ Metric.ball z₀ c) {t : ℝ} (ht : 0 < t) :
      c * (1 + t) ≤ ‖(t : ℂ) + w‖ := by
    have h := hcz w hw ⟨t, ht.le⟩
    rwa [add_comm w] at h
  have hne {w : ℂ} (hw : w ∈ Metric.ball z₀ c) {t : ℝ} (ht : 0 < t) : (t : ℂ) + w ≠ 0 :=
    norm_pos_iff.mp ((mul_pos hc (by linarith)).trans_le (hlow hw ht))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun w t ↦ (t : ℂ) ^ (-(α : ℂ)) * ((t : ℂ) + w)⁻¹)
    (F' := fun w t ↦ (t : ℂ) ^ (-(α : ℂ)) * -(((t : ℂ) + w) ^ 2)⁻¹)
    (bound := fun t ↦ (c ^ 2)⁻¹ * (t ^ (-α) / (t + 1)))
    (Metric.ball_mem_nhds z₀ hc) ?_ (integrableOn_cpow_neg_mul_inv_add hα₀ hα₁ hz₀) ?_ ?_
    ((TauCeti.integrableOn_rpow_neg_div_add α 1 hα₀ hα₁ one_pos).const_mul _)
    ?_).2.differentiableAt.differentiableWithinAt
  · exact Eventually.of_forall fun w ↦ (by fun_prop : Measurable fun t : ℝ ↦
      (t : ℂ) ^ (-(α : ℂ)) * ((t : ℂ) + w)⁻¹).aestronglyMeasurable
  · exact (by fun_prop : Measurable fun t : ℝ ↦
      (t : ℂ) ^ (-(α : ℂ)) * -(((t : ℂ) + z₀) ^ 2)⁻¹).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w hw
    have hl := hlow hw ht
    rw [norm_mul, norm_neg, norm_inv, norm_pow, norm_cpow_eq_rpow_re_of_pos ht, neg_re, ofReal_re]
    have h1 : ((1 + t) ^ 2)⁻¹ ≤ (t + 1)⁻¹ := by
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      nlinarith
    calc t ^ (-α) * (‖(t : ℂ) + w‖ ^ 2)⁻¹ ≤ t ^ (-α) * ((c * (1 + t)) ^ 2)⁻¹ := by
          gcongr
      _ = (c ^ 2)⁻¹ * (t ^ (-α) * ((1 + t) ^ 2)⁻¹) := by rw [mul_pow, mul_inv]; ring
      _ ≤ (c ^ 2)⁻¹ * (t ^ (-α) / (t + 1)) := by
          rw [div_eq_mul_inv]
          gcongr
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) w hw
    exact ((hasDerivAt_id w).const_add (t : ℂ)).inv (hne hw ht) |>.const_mul _ |>.congr_deriv
      (by simp only [id]; ring)

/-- **The Stieltjes transform of `t ^ (-α)`.** For `0 < α < 1` and `z` in the slit plane,
`∫₀^∞ t ^ (-α) (t + z)⁻¹ dt = π / sin (π α) * z ^ (-α)`, with the principal power. -/
theorem integral_cpow_neg_mul_inv_add (hα₀ : 0 < α) (hα₁ : α < 1) {z : ℂ}
    (hz : z ∈ slitPlane) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (-(α : ℂ)) * ((t : ℂ) + z)⁻¹ =
      ((Real.pi / Real.sin (Real.pi * α) : ℝ) : ℂ) * z ^ (-(α : ℂ)) := by
  -- both sides are holomorphic on the slit plane and agree on the positive reals
  have hreal {x : ℝ} (hx : 0 < x) :
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (-(α : ℂ)) * ((t : ℂ) + x)⁻¹ =
        ((Real.pi / Real.sin (Real.pi * α) : ℝ) : ℂ) * (x : ℂ) ^ (-(α : ℂ)) := by
    rw [← ofReal_neg, ← ofReal_cpow hx.le, ← ofReal_mul,
      ← TauCeti.integral_rpow_neg_div_add α x hα₀ hα₁ hx, ← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
    rw [div_eq_mul_inv, ofReal_mul, ofReal_inv, ofReal_add, ofReal_cpow ht.le]
  have hG : DifferentiableOn ℂ
      (fun z : ℂ ↦ ((Real.pi / Real.sin (Real.pi * α) : ℝ) : ℂ) * z ^ (-(α : ℂ))) slitPlane :=
    fun w hw ↦ (differentiableAt_id.cpow_const hw).const_mul _ |>.differentiableWithinAt
  exact ((differentiableOn_integral_cpow_neg_mul_inv_add hα₀ hα₁).analyticOnNhd
    isOpen_slitPlane).eqOn_slitPlane_of_ofReal_pos_eq (hG.analyticOnNhd isOpen_slitPlane)
    (fun x hx ↦ hreal hx) hz

/-- For `c > 0` and `z` in the slit plane, `t ↦ t⁻¹ (t + z)⁻¹` is integrable on `(c, ∞)`. -/
theorem integrableOn_Ioi_inv_mul_inv_add {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : z ∈ slitPlane) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ)⁻¹ * ((t : ℂ) + z)⁻¹) (Ioi c) := by
  obtain ⟨b, hb, hbz⟩ := TauCeti.exists_pos_mul_one_add_le_norm_ofReal_add hz
  refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hc).const_mul b⁻¹).mono' ?_ ?_
  · exact (by fun_prop : Measurable fun t : ℝ ↦
      (t : ℂ)⁻¹ * ((t : ℂ) + z)⁻¹).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : c < t)
    have ht0 : 0 < t := hc.trans ht
    rw [norm_mul, norm_inv, norm_inv, norm_real, Real.norm_of_nonneg ht0.le,
      show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht0.le, Real.rpow_natCast]
    calc t⁻¹ * ‖(t : ℂ) + z‖⁻¹ ≤ t⁻¹ * (b * (1 + t))⁻¹ := by
          gcongr
          exact hbz t ht0.le
      _ = b⁻¹ * (t⁻¹ * (1 + t)⁻¹) := by rw [mul_inv]; ring
      _ ≤ b⁻¹ * (t⁻¹ * t⁻¹) := by gcongr; linarith
      _ = b⁻¹ * (t ^ 2)⁻¹ := by rw [sq, mul_inv]

/-- **The Stieltjes transform of `t⁻¹` on `(c, ∞)`.** For `c > 0` and `z` in the slit plane,
`∫_c^∞ t⁻¹ (t + z)⁻¹ dt = z⁻¹ (log (c + z) - log c)`, with the principal logarithm. -/
theorem integral_Ioi_inv_mul_inv_add {c : ℝ} (hc : 0 < c) {z : ℂ} (hz : z ∈ slitPlane) :
    ∫ t in Ioi c, (t : ℂ)⁻¹ * ((t : ℂ) + z)⁻¹ = z⁻¹ * (log (c + z) - log c) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hmem {t : ℝ} (ht : 0 ≤ t) : (t : ℂ) + z ∈ slitPlane :=
    TauCeti.ofReal_add_mem_slitPlane hz ht
  -- the antiderivative `z⁻¹ (log t - log (t + z))` tends to `0` at `+∞`
  have hderiv : ∀ t ∈ Ici c, HasDerivAt (fun t : ℝ ↦ z⁻¹ * (log (t : ℂ) - log ((t : ℂ) + z)))
      ((t : ℂ)⁻¹ * ((t : ℂ) + z)⁻¹) t := by
    intro t (ht : c ≤ t)
    have ht0 : 0 < t := hc.trans_le ht
    have hid : HasDerivAt (fun t : ℝ ↦ (t : ℂ)) 1 t := by
      simpa using (hasDerivAt_id' t).ofReal_comp
    have h₁ := HasDerivAt.clog_real hid (ofReal_mem_slitPlane.mpr ht0)
    have h₂ := HasDerivAt.clog_real (hid.add_const z) (hmem ht0.le)
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have htz : (t : ℂ) + z ≠ 0 := slitPlane_ne_zero (hmem ht0.le)
    refine ((h₁.sub h₂).const_mul z⁻¹).congr_deriv ?_
    field_simp
    ring
  have hlog : ∀ᶠ t : ℝ in atTop, z⁻¹ * (log (t : ℂ) - log ((t : ℂ) + z)) =
      z⁻¹ * -log (1 + z * ((t⁻¹ : ℝ) : ℂ)) := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have hfac : (t : ℂ) + z = t * (1 + z * ((t⁻¹ : ℝ) : ℂ)) := by
      rw [ofReal_inv]
      field_simp
    have hne : 1 + z * ((t⁻¹ : ℝ) : ℂ) ≠ 0 := by
      intro h
      exact slitPlane_ne_zero (hmem ht.le) (by rw [hfac, h, mul_zero])
    rw [hfac, log_ofReal_mul ht hne, ofReal_log ht.le]
    ring
  have hlim : Tendsto (fun t : ℝ ↦ z⁻¹ * (log (t : ℂ) - log ((t : ℂ) + z))) atTop (𝓝 0) := by
    refine Tendsto.congr' (EventuallyEq.symm hlog) ?_
    have h₁ : Tendsto (fun t : ℝ ↦ 1 + z * ((t⁻¹ : ℝ) : ℂ)) atTop (𝓝 1) := by
      simpa using (((continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero).const_mul
        z).const_add 1
    simpa using ((((continuousAt_clog one_mem_slitPlane).tendsto.comp h₁).neg).const_mul z⁻¹)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_Ioi_inv_mul_inv_add hc hz)
    hlim]
  ring

end Stieltjes

end Complex

namespace Real

/-- For `c, r > 0`, `t ↦ (t (t + r))⁻¹` is integrable on `(c, ∞)`. -/
theorem integrableOn_Ioi_inv_mul_add {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ ↦ (t * (t + r))⁻¹) (Ioi c) := by
  have h := (Complex.integrableOn_Ioi_inv_mul_inv_add hc (ofReal_mem_slitPlane.mpr hr)).re
  refine h.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
  simp only [RCLike.re_to_complex, ← ofReal_add, ← ofReal_inv, ← ofReal_mul, ofReal_re, mul_inv]

/-- The real case of `Complex.integral_Ioi_inv_mul_inv_add`: for `c, r > 0`,
`∫_c^∞ (t (t + r))⁻¹ dt = (log (c + r) - log c) / r`. -/
theorem integral_Ioi_inv_mul_add {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    ∫ t in Ioi c, (t * (t + r))⁻¹ = (Real.log (c + r) - Real.log c) / r := by
  have h := Complex.integral_Ioi_inv_mul_inv_add hc (ofReal_mem_slitPlane.mpr hr)
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ ↦ (((t * (t + r))⁻¹ : ℝ) : ℂ))
      (fun t _ ↦ by push_cast; rw [mul_inv]), integral_complex_ofReal, ← ofReal_add,
    ← ofReal_log hc.le, ← ofReal_log (by positivity), ← ofReal_inv, ← ofReal_sub, ← ofReal_mul,
    ofReal_inj] at h
  rw [h, div_eq_inv_mul]

end Real
