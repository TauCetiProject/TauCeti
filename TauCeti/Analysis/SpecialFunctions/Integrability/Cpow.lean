/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Complex powers on finite intervals

The weight `(1 - t) ^ s` is integrable up to one when `-1 < s.re`. On a positive interval
`[ρ, 1]`, multiplying by an arbitrary complex power of `t` and a continuous kernel preserves
integrability.

A continuous multiplier times a principal power of a continuous nonvanishing base is
integrable on a compact interval, including when the base crosses the branch cut.
-/

public section

open Complex MeasureTheory Set
open scoped Interval

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

/-- On a compact interval, a continuous multiplier times a principal power of a continuous
nonvanishing base is interval-integrable for any locally finite measure. -/
theorem intervalIntegrable_mul_cpow_of_ne_zero {h g : ℝ → ℂ} {α β : ℝ}
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    (hh : ContinuousOn h (uIcc α β)) (hg : ContinuousOn g (uIcc α β))
    (hg0 : ∀ x ∈ uIcc α β, g x ≠ 0) (e : ℂ) :
    IntervalIntegrable (fun x => h x * g x ^ e) μ α β := by
  have hg_meas := (hg.mono uIoc_subset_uIcc).aemeasurable (μ := μ) measurableSet_uIoc
  have hpow : AEMeasurable (fun x => g x ^ e) (μ.restrict (Ι α β)) :=
    (continuous_exp.measurable.comp_aemeasurable
      ((measurable_log.comp_aemeasurable hg_meas).mul_const e)).congr <| by
        filter_upwards [ae_restrict_mem (μ := μ) measurableSet_uIoc] with x hx
        exact (cpow_def_of_ne_zero (hg0 x (uIoc_subset_uIcc hx)) e).symm
  have hdom : ContinuousOn (fun x => ‖h x‖ * (‖g x‖ ^ e.re * Real.exp (Real.pi * |e.im|)))
      (uIcc α β) :=
    hh.norm.mul ((hg.norm.rpow_const
      (fun x hx => Or.inl (norm_ne_zero_iff.mpr (hg0 x hx)))).mul continuousOn_const)
  exact hdom.intervalIntegrable.mono_fun'
    (((hh.mono uIoc_subset_uIcc).aemeasurable measurableSet_uIoc).mul hpow).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_cpow_le_mul_exp _ _) (norm_nonneg _))

end TauCeti
