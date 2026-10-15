/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Endpoint limits from integrable derivatives

A differentiable curve on an open interval with integrable derivative has a limit at its
left endpoint in a complete normed space. Neither the value nor differentiability at the
endpoint is prescribed. This applies to finite-length radial approaches to an isolated
singularity.

The argument uses Mathlib's fundamental theorem of calculus
`intervalIntegral.integral_deriv_eq_sub` and continuity of indefinite integrals
`intervalIntegral.continuousOn_primitive_interval_left`.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A differentiable curve whose derivative is integrable on an open interval has a limit
from the right at the left endpoint. The value of the curve at that endpoint is unrestricted. -/
theorem exists_tendsto_nhdsGT_of_integrableOn_deriv {f : ℝ → E} {a b : ℝ}
    (hab : a < b) (hf : DifferentiableOn ℝ f (Ioo a b))
    (hint : IntegrableOn (deriv f) (Ioo a b)) :
    ∃ q, Tendsto f (𝓝[>] a) (𝓝 q) := by
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  have hIntab : IntegrableOn (deriv f) (Icc a b) := by
    rwa [integrableOn_Icc_iff_integrableOn_Ioo]
  have hInt : IntegrableOn (deriv f) (Icc a c) :=
    hIntab.mono_set (Icc_subset_Icc_right hcb.le)
  have hp : ContinuousOn (fun x ↦ ∫ t in x..c, deriv f t) (Icc a c) := by
    rw [← uIcc_of_le hac.le]
    exact intervalIntegral.continuousOn_primitive_interval_left
      (by simpa only [uIcc_of_le hac.le] using hInt)
  have hlim : Tendsto (fun x ↦ f c - ∫ t in x..c, deriv f t) (𝓝[>] a)
      (𝓝 (f c - ∫ t in a..c, deriv f t)) := by
    have h := (hp a ⟨le_rfl, hac.le⟩).tendsto
    rw [nhdsWithin_Icc_eq_nhdsGE hac] at h
    exact tendsto_const_nhds.sub (h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self))
  refine ⟨_, hlim.congr' ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hac] with x hx
  have hsub : uIcc x c ⊆ Ioo a b := by
    rw [uIcc_of_le hx.2.le]
    exact Icc_subset_Ioo hx.1 hcb
  have hFTC := intervalIntegral.integral_deriv_eq_sub
    (fun y hy ↦ hf.differentiableAt (isOpen_Ioo.mem_nhds (hsub hy)))
    ((hint.mono_set hsub).intervalIntegrable)
  rw [hFTC]
  abel

end TauCeti
