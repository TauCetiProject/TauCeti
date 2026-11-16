/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Endpoint limits from integrable derivatives

A curve in a complete normed space that has an integrable derivative on an interval `(a, c]`
has a limit from the right at `a`, namely `f c - ∫ t in a..c, f' t`. Neither the value nor
differentiability at the endpoint `a` is prescribed. This applies to finite-length radial
approaches to an isolated singularity.

## Main results

* `TauCeti.tendsto_nhdsGT_of_hasDerivAt_of_integrableOn_Ioc`: the limit, with its value.
* `TauCeti.exists_tendsto_nhdsGT_of_hasDerivAt_of_integrableOn_Ioo`: existence of the limit
  for a curve with integrable derivative on an open interval.

These are the finite-endpoint analogues of Mathlib's
`MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi`.
-/

public section

namespace TauCeti

open Filter MeasureTheory Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f f' : ℝ → E} {a b c : ℝ}

/-- A curve with integrable derivative `f'` on `Ioc a c` tends to `f c - ∫ t in a..c, f' t`
from the right at `a`. The value of the curve at `a` is unrestricted. -/
theorem tendsto_nhdsGT_of_hasDerivAt_of_integrableOn_Ioc (hac : a < c)
    (hf : ∀ x ∈ Ioc a c, HasDerivAt f (f' x) x) (hint : IntegrableOn f' (Ioc a c)) :
    Tendsto f (𝓝[>] a) (𝓝 (f c - ∫ t in a..c, f' t)) := by
  have hp : ContinuousOn (fun x ↦ ∫ t in x..c, f' t) (Icc a c) := by
    rw [← uIcc_of_le hac.le]
    exact intervalIntegral.continuousOn_primitive_interval_left
      (by rwa [uIcc_of_le hac.le, integrableOn_Icc_iff_integrableOn_Ioc])
  have h := (hp a (left_mem_Icc.2 hac.le)).tendsto
  rw [nhdsWithin_Icc_eq_nhdsGE hac] at h
  refine (tendsto_const_nhds.sub (h.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self))).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hac] with x hx
  have hsub : uIcc x c ⊆ Ioc a c := by
    rw [uIcc_of_le hx.2.le]
    exact Icc_subset_Ioc_iff hx.2.le |>.2 ⟨hx.1, le_rfl⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy ↦ hf y (hsub hy))
    (hint.mono_set hsub).intervalIntegrable, sub_sub_cancel]

/-- A curve with integrable derivative on an open interval has a limit from the right at the
left endpoint. The value of the curve at that endpoint is unrestricted. -/
theorem exists_tendsto_nhdsGT_of_hasDerivAt_of_integrableOn_Ioo (hab : a < b)
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hint : IntegrableOn f' (Ioo a b)) :
    ∃ q, Tendsto f (𝓝[>] a) (𝓝 q) := by
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  have hsub : Ioc a c ⊆ Ioo a b := Ioc_subset_Ioo_right hcb
  exact ⟨_, tendsto_nhdsGT_of_hasDerivAt_of_integrableOn_Ioc hac (fun x hx ↦ hf x (hsub hx))
    (hint.mono_set hsub)⟩

end TauCeti
