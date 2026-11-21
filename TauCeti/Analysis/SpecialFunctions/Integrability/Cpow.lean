/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Complex powers at a finite interval endpoint

The weight `(1 - t) ^ s` is integrable up to one when `-1 < s.re`. On a positive interval
`[ρ, 1]`, multiplying by an arbitrary complex power of `t` and a continuous kernel preserves
integrability.
-/

public section

open Complex MeasureTheory Set

namespace TauCeti

/-- The right endpoint weight `(1 - t) ^ s` is integrable when `-1 < s.re`. -/
theorem intervalIntegrable_one_sub_ofReal_cpow {s : ℂ} (hs : -1 < s.re) (ρ : ℝ) :
    IntervalIntegrable (fun t : ℝ => (1 - (t : ℂ)) ^ s) volume ρ 1 := by
  simpa only [ofReal_sub, ofReal_one, sub_zero, sub_sub_cancel] using
    ((intervalIntegral.intervalIntegrable_cpow' (a := 0) (b := 1 - ρ) hs).comp_sub_left 1).symm

/-- Between `ρ > 0` and `1`, a complex power of `t` times a continuous kernel preserves
integrability of the endpoint weight `(1 - t) ^ s` when `-1 < s.re`. -/
theorem intervalIntegrable_ofReal_cpow_mul_one_sub_cpow_mul {p s : ℂ} {K : ℝ → ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hs : -1 < s.re) (hK : ContinuousOn K (uIcc ρ 1)) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ p * (1 - (t : ℂ)) ^ s * K t) volume ρ 1 := by
  have hpow : ContinuousOn (fun t : ℝ => (t : ℂ) ^ p) (uIcc ρ 1) := by
    exact continuousOn_of_forall_continuousAt fun t ht =>
      continuous_ofReal.continuousAt.cpow continuousAt_const
        (ofReal_mem_slitPlane.mpr ((lt_min hρ zero_lt_one).trans_le ht.1))
  simpa only [Pi.mul_apply, mul_left_comm, mul_comm, mul_assoc] using
    (intervalIntegrable_one_sub_ofReal_cpow hs ρ).mul_continuousOn (hpow.mul hK)

end TauCeti
