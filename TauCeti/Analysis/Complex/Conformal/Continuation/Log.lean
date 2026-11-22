/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import TauCeti.Analysis.Complex.Conformal.Continuation.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import TauCeti.Analysis.SpecialFunctions.Exp.Periodic

/-!
# Analytic continuation of the complex logarithm around circles

Continuing the principal complex logarithm `Complex.log` counterclockwise once around the circle
`t ↦ circleMap 0 r (2 * π * t)` of positive radius `r > 0` yields an analytic continuation
whose terminal germ at `r` is shifted by `2 * π * I`.

* `TauCeti.exists_isAnalyticContinuationAlong_log_circleMap`: existence of an analytic continuation
  of `Complex.log` along one positive turn of `circleMap 0 r`, starting at `Complex.log`
  and ending at `fun z => Complex.log z + 2 * π * I`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 8 §1.
* J. B. Conway, *Functions of One Complex Variable I* (GTM 11), Ch. IX §2.
-/

public section

namespace TauCeti

open Filter Metric Set Topology unitInterval

private noncomputable def logCircleCont (t : I) (z : ℂ) : ℂ :=
  Complex.log (z * Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ)))) +
    2 * Real.pi * Complex.I * (t : ℂ)

private theorem logCircleCont_zero : logCircleCont 0 = Complex.log := by
  ext z; simp [logCircleCont]

private theorem logCircleCont_one (z : ℂ) :
    logCircleCont 1 z = Complex.log z + 2 * Real.pi * Complex.I := by
  have h1 : (((1 : I) : ℝ) : ℂ) = 1 := by simp
  rw [logCircleCont, h1, mul_one, Complex.exp_neg, Complex.exp_two_pi_mul_I, inv_one, mul_one]

private theorem exp_logCircleCont (t : I) {z : ℂ} (hz : z ≠ 0) :
    Complex.exp (logCircleCont t z) = z := by
  rw [logCircleCont, Complex.exp_add, Complex.exp_log (mul_ne_zero hz (Complex.exp_ne_zero _)),
    mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

/-- **Analytic continuation of `Complex.log` around a circle of positive radius.** Continuing
`Complex.log` once positively around `t ↦ circleMap 0 r (2 * π * t)` (`0 < r`) produces an
analytic continuation starting at `Complex.log` and ending at `fun z => Complex.log z + 2 * π * I`.
-/
theorem exists_isAnalyticContinuationAlong_log_circleMap {r : ℝ} (hr : 0 < r) :
    ∃ f : I → ℂ → ℂ,
      IsAnalyticContinuationAlong f (fun t => circleMap 0 r (2 * Real.pi * t)) univ ∧
      f 0 = Complex.log ∧
      ∀ z, f 1 z = Complex.log z + 2 * Real.pi * Complex.I := by
  have hrot : ∀ t : I, circleMap 0 r (2 * Real.pi * t) *
      Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) = (r : ℂ) := fun t => by
    rw [circleMap_zero]
    have hexp : Complex.exp (↑(2 * Real.pi * (t : ℝ)) * Complex.I) *
        Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) = 1 := by
      rw [← Complex.exp_add]; convert Complex.exp_zero using 2; push_cast; ring
    rw [mul_assoc, hexp, mul_one]
  have hr_slit : (r : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using hr))
  refine ⟨logCircleCont, ⟨(by fun_prop : Continuous fun t : I =>
      circleMap 0 r (2 * Real.pi * t)).continuousOn, fun t _ => ?_, fun t _ => ?_⟩,
    logCircleCont_zero, logCircleCont_one⟩
  · have hval : circleMap 0 r (2 * Real.pi * t) *
        Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))) ∈ Complex.slitPlane :=
      (hrot t).symm ▸ hr_slit
    exact ((analyticAt_id.mul analyticAt_const).clog hval).add analyticAt_const
  · let rot : I × ℂ → ℂ := fun p => p.2 * Complex.exp (-(2 * Real.pi * Complex.I * ((p.1 : ℝ) : ℂ)))
    have hrot_val : rot (t, circleMap 0 r (2 * Real.pi * t)) ∈ Complex.slitPlane := by
      dsimp only [rot]; exact (hrot t).symm ▸ hr_slit
    have hcont1 : ContinuousAt (fun p : I × ℂ => logCircleCont p.1 p.2)
        (t, circleMap 0 r (2 * Real.pi * t)) :=
      ((by fun_prop : Continuous rot).continuousAt.clog hrot_val).add (by fun_prop)
    have hcont2 : ContinuousAt (fun p : I × ℂ => logCircleCont t p.2)
        (t, circleMap 0 r (2 * Real.pi * t)) :=
      ((continuous_snd.mul continuous_const).continuousAt.clog hrot_val).add continuousAt_const
    have hlt : ∀ᶠ p : I × ℂ in 𝓝 (t, circleMap 0 r (2 * Real.pi * t)),
        ‖logCircleCont p.1 p.2 - logCircleCont t p.2‖ < 1 := by
      simpa using Metric.tendsto_nhds.mp (hcont1.sub hcont2) 1 zero_lt_one
    have hmem : {p : I × ℂ | ‖logCircleCont p.1 p.2 - logCircleCont t p.2‖ < 1 ∧ p.2 ≠ 0} ∈
        𝓝 t ×ˢ 𝓝 (circleMap 0 r (2 * Real.pi * t)) := by
      rw [← nhds_prod_eq]; exact hlt.and (continuous_snd.continuousAt.eventually
        (eventually_ne_nhds (circleMap_ne_center hr.ne')))
    obtain ⟨V, hV, W', hW', hVW'⟩ := Filter.mem_prod_iff.mp hmem
    obtain ⟨ε, hε, hεW⟩ := Metric.mem_nhds_iff.mp hW'
    have hcont_c : Continuous fun t : I => circleMap 0 r (2 * Real.pi * t) := by fun_prop
    filter_upwards [nhdsWithin_le_nhds (Filter.inter_mem hV
      (hcont_c.continuousAt.preimage_mem_nhds
        (isOpen_ball.mem_nhds (mem_ball_self hε))))] with u ⟨huV, huW⟩
    filter_upwards [isOpen_ball.mem_nhds huW] with z hzW
    obtain ⟨hnorm, hz0⟩ := hVW' (mk_mem_prod huV (hεW hzW))
    exact Complex.eq_of_exp_eq_of_norm_sub_lt
      ((exp_logCircleCont u hz0).trans (exp_logCircleCont t hz0).symm)
      (hnorm.trans (by linarith [Real.two_le_pi]))

end TauCeti
