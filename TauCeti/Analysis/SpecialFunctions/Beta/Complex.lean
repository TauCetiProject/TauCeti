/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Calculus.ParametricIntegral
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

end Stieltjes

end Complex
