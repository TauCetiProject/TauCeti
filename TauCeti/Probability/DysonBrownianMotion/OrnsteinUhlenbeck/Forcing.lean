/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import TauCeti.Probability.DysonBrownianMotion.OrnsteinUhlenbeck.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.SpecialFunctions.Exp.Half
import TauCeti.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.Probability.BrownianMotion.Integral.TimeChange

/-!
# The Ornstein–Uhlenbeck time changes of a Brownian forcing

The exponential time change carries Dyson trajectories driven by a forcing path `w` to
Ornstein–Uhlenbeck Dyson trajectories driven by `ouTimeChangeForcing w`, and the logarithmic time
change carries Ornstein–Uhlenbeck Dyson trajectories driven by `w` back to Dyson trajectories
driven by `ouTimeChangeInvForcing w`. This file shows that both transformed forcings of a Brownian
motion are again Brownian motions, coordinate by coordinate
(`TauCeti.Probability.isBrownianReal_ouTimeChangeForcing` and
`TauCeti.Probability.isBrownianReal_ouTimeChangeInvForcing`). So, in both directions, the time
changes relate Dyson and Ornstein–Uhlenbeck Dyson systems whose forcings are coordinatewise
Brownian. Independence of the coordinates of the transformed forcings is not established here.

The pathwise formulas defining the two forcings are the integration by parts forms of the Wiener
integrals `∫₀^{e^t - 1} (1 + r)^{-1/2} dB_r` and `∫₀^{log (1 + s)} e^{u/2} dB_u`
(`ProbabilityTheory.IsPreBrownianReal.wienerIntegral_ae_eq_mul_sub_integral`, after the changes
of variables `r = e^u - 1` and `u = log (1 + r)`). The integrands are normalized by
`∫₀^{e^t - 1} (1 + r)⁻¹ dr = t` and `∫₀^{log (1 + s)} e^u du = s`, so
`ProbabilityTheory.IsBrownianReal.isBrownianReal_of_ae_eq_mul_sub_integral` identifies the
forcings as Brownian motions.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010, §4.3.1.
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.4.A.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}

/-- The negated derivative of `r ↦ (1 + r)^{-1/2}` is continuous on `[0, ∞)`. -/
private theorem continuousOn_inv_sqrt_one_add_div :
    ContinuousOn (fun r : ℝ ↦ (√(1 + r))⁻¹ / (2 * (1 + r))) (Ici 0) := by
  refine ContinuousOn.div (ContinuousOn.inv₀ (by fun_prop) fun r hr ↦ ?_) (by fun_prop)
    fun r hr ↦ ?_
  · exact (Real.sqrt_pos.2 (by linarith [mem_Ici.1 hr])).ne'
  · linarith [mem_Ici.1 hr]

/-- The forcing of the exponential time change is the integration by parts form of the Wiener
integral of `(1 + r)^{-1/2}` up to `e^t - 1`. -/
private theorem ouTimeChangeForcing_eq_mul_sub_integral {w : ℝ≥0 → Fin n → ℝ} {i : Fin n}
    (hw : Continuous fun s ↦ w s i) (t : ℝ≥0) :
    ouTimeChangeForcing w t i =
      (√(1 + ((Real.exp t - 1).toNNReal : ℝ)))⁻¹ * w (Real.exp t - 1).toNNReal i -
        ∫ r in (0 : ℝ)..(Real.exp t - 1).toNNReal,
          -((√(1 + r))⁻¹ / (2 * (1 + r))) * w r.toNNReal i := by
  let g : ℝ → ℝ := fun r ↦ (√(1 + r))⁻¹ / (2 * (1 + r)) * w r.toNNReal i
  have hg : ContinuousOn g (Ici 0) :=
    continuousOn_inv_sqrt_one_add_div.mul (hw.comp continuous_real_toNNReal).continuousOn
  -- Substitute `r = e^u - 1` in `∫₀^{e^t - 1} g`.
  have hsub := intervalIntegral.integral_comp_mul_deriv' (a := 0) (b := t)
    (f := fun u ↦ Real.exp u - 1) (f' := Real.exp) (g := g)
    (fun x _ ↦ (Real.hasDerivAt_exp x).sub_const 1) Real.continuous_exp.continuousOn
    (hg.mono (by
      rintro _ ⟨u, hu, rfl⟩
      rw [uIcc_of_le t.coe_nonneg] at hu
      exact sub_nonneg.2 (Real.one_le_exp hu.1)))
  simp only [Real.exp_zero, sub_self] at hsub
  have hneg : ∫ r in (0 : ℝ)..Real.exp t - 1, -((√(1 + r))⁻¹ / (2 * (1 + r))) * w r.toNNReal i =
      -∫ r in (0 : ℝ)..Real.exp t - 1, g r := by
    rw [← intervalIntegral.integral_neg]
    simp only [g, neg_mul]
  rw [ouTimeChangeForcing_apply, Real.coe_toNNReal_exp_sub_one t.coe_nonneg, hneg, ← hsub,
    sub_neg_eq_add, add_sub_cancel, ← Real.exp_half, ← Real.exp_neg]
  congr 1
  refine intervalIntegral.integral_congr fun u _ ↦ ?_
  simp only [g, Function.comp_apply, add_sub_cancel, ← Real.exp_half]
  rw [← Real.exp_half_mul_exp_half u, Real.exp_neg]
  field_simp

/-- The forcing of the logarithmic time change is the integration by parts form of the Wiener
integral of `e^{u/2}` up to `log (1 + s)`. -/
private theorem ouTimeChangeInvForcing_eq_mul_sub_integral {w : ℝ≥0 → Fin n → ℝ} {i : Fin n}
    (hw : Continuous fun s ↦ w s i) (s : ℝ≥0) :
    ouTimeChangeInvForcing w s i =
      Real.exp (((Real.log (1 + s)).toNNReal : ℝ) / 2) * w (Real.log (1 + s)).toNNReal i -
        ∫ u in (0 : ℝ)..(Real.log (1 + s)).toNNReal,
          Real.exp (u / 2) / 2 * w u.toNNReal i := by
  -- Substitute `u = log (1 + r)` in `∫₀^{log (1 + s)} e^{u/2} w u / 2`.
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := s)
    (f := fun r ↦ Real.log (1 + r)) (f' := fun r ↦ 1 / (1 + r))
    (g := fun u ↦ Real.exp (u / 2) / 2 * w u.toNNReal i)
    (fun x hx ↦ by
      rw [uIcc_of_le s.coe_nonneg] at hx
      simpa using ((hasDerivAt_id' x).const_add 1).log (by linarith [hx.1]))
    (continuousOn_const.div (by fun_prop) fun r hr ↦ by
      rw [uIcc_of_le s.coe_nonneg] at hr
      linarith [hr.1])
    (by fun_prop)
  simp only [add_zero, Real.log_one] at hsub
  rw [ouTimeChangeInvForcing_apply, Real.coe_toNNReal_log_one_add s.coe_nonneg, ← hsub,
    Real.exp_half, Real.exp_log (by positivity)]
  congr 1
  refine intervalIntegral.integral_congr fun r hr ↦ ?_
  rw [uIcc_of_le s.coe_nonneg] at hr
  have hr1 : 0 < 1 + r := by linarith [hr.1]
  simp only [Function.comp_apply, Real.exp_half, Real.exp_log hr1]
  field_simp
  rw [Real.sq_sqrt hr1.le, mul_comm]

/-- **The exponential time change of a Brownian forcing is Brownian.** If the `i`-th coordinate of
`B` is a Brownian motion, then so is the `i`-th coordinate of its exponential time-change forcing
`ouTimeChangeForcing B`, `t ↦ ∫₀^{e^t - 1} (1 + r)^{-1/2} dB_r(i)`. -/
theorem isBrownianReal_ouTimeChangeForcing {B : Fin n → ℝ≥0 → Ω → ℝ} {i : Fin n}
    (hB : IsBrownianReal (B i) P) :
    IsBrownianReal (fun t ω ↦ ouTimeChangeForcing (fun s j ↦ B j s ω) t i) P := by
  have hh' : ContinuousOn (fun r : ℝ ↦ -((√(1 + r))⁻¹ / (2 * (1 + r)))) (Ici 0) :=
    continuousOn_inv_sqrt_one_add_div.neg
  refine hB.isBrownianReal_of_ae_eq_mul_sub_integral (a := fun t ↦ (Real.exp t - 1).toNNReal)
    (h := fun r ↦ (√(1 + r))⁻¹) (ContinuousOn.inv₀ (by fun_prop) fun r hr ↦ (Real.sqrt_pos.2 (by
      linarith [mem_Ici.1 hr])).ne')
    (fun x hx ↦ Real.hasDerivAt_inv_sqrt_one_add (by linarith : (0 : ℝ) < 1 + x).ne')
    (fun t ↦ (hh'.mono (uIcc_of_le (Real.exp t - 1).toNNReal.coe_nonneg ▸
      Icc_subset_Ici_self)).intervalIntegrable) (fun t ↦ ?_)
    (fun t ↦ hB.cont.mono fun ω hω ↦
      ouTimeChangeForcing_eq_mul_sub_integral (w := fun s j ↦ B j s ω) hω t) ?_
  · -- `∫₀^{e^t - 1} (1 + r)⁻¹ dr = log (e^t) = t`.
    rw [Real.coe_toNNReal_exp_sub_one t.coe_nonneg,
      intervalIntegral.integral_congr (g := fun r ↦ (1 + r)⁻¹) fun r hr ↦ ?_,
      intervalIntegral.integral_comp_add_left (fun r ↦ r⁻¹), add_zero, add_sub_cancel,
      integral_inv_of_pos one_pos (Real.exp_pos t), div_one, Real.log_exp]
    rw [uIcc_of_le (sub_nonneg.2 (Real.one_le_exp t.coe_nonneg))] at hr
    simp only [inv_pow, Real.sq_sqrt (by linarith [hr.1] : (0 : ℝ) ≤ 1 + r)]
  · filter_upwards [hB.cont] with ω hω
    have hw : Continuous fun s : ℝ≥0 ↦ fun _ : Fin n ↦ B i s ω := continuous_pi fun _ ↦ hω
    refine ((continuous_apply i).comp (continuous_ouTimeChangeForcing hw)).congr fun t ↦ ?_
    simp only [Function.comp_apply, ouTimeChangeForcing_apply]

/-- **The logarithmic time change of a Brownian forcing is Brownian.** If the `i`-th coordinate of
`B` is a Brownian motion, then so is the `i`-th coordinate of its logarithmic time-change forcing
`ouTimeChangeInvForcing B`, `s ↦ ∫₀^{log (1 + s)} e^{u/2} dB_u(i)`. -/
theorem isBrownianReal_ouTimeChangeInvForcing {B : Fin n → ℝ≥0 → Ω → ℝ} {i : Fin n}
    (hB : IsBrownianReal (B i) P) :
    IsBrownianReal (fun s ω ↦ ouTimeChangeInvForcing (fun r j ↦ B j r ω) s i) P := by
  refine hB.isBrownianReal_of_ae_eq_mul_sub_integral (a := fun s ↦ (Real.log (1 + s)).toNNReal)
    (h := fun u ↦ Real.exp (u / 2)) (h' := fun u ↦ Real.exp (u / 2) / 2) (by fun_prop)
    (fun x _ ↦ ?_) (fun s ↦ (by fun_prop : Continuous _).intervalIntegrable _ _) (fun s ↦ ?_)
    (fun s ↦ hB.cont.mono fun ω hω ↦
      ouTimeChangeInvForcing_eq_mul_sub_integral (w := fun r j ↦ B j r ω) hω s) ?_
  · exact ((hasDerivAt_id' x).div_const 2).exp.congr_deriv (by ring)
  · -- `∫₀^{log (1 + s)} e^u du = s`.
    have hsq (r : ℝ) : Real.exp (r / 2) ^ 2 = Real.exp r := by
      rw [sq, Real.exp_half_mul_exp_half]
    simp only [hsq, Real.coe_toNNReal_log_one_add s.coe_nonneg]
    rw [integral_exp, Real.exp_zero, Real.exp_log (by positivity)]
    ring
  · filter_upwards [hB.cont] with ω hω
    have hw : Continuous fun r : ℝ≥0 ↦ fun _ : Fin n ↦ B i r ω := continuous_pi fun _ ↦ hω
    refine ((continuous_apply i).comp (continuous_ouTimeChangeInvForcing hw)).congr fun s ↦ ?_
    simp only [Function.comp_apply, ouTimeChangeInvForcing_apply]

end TauCeti.Probability
