/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.LogUniform.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Endpoint limits of log-uniform quantiles

For valid endpoints `0 < a < b`, the log-uniform quantile is the geometric interpolation
`a * (b / a) ^ u`. This file proves that its one-sided limits at probability levels zero and one
are the support endpoints `a` and `b`, respectively.

The limits are stated in `EReal` to match the endpoint API for distributions whose support may be
unbounded. They only use interior probability levels and therefore do not depend on the totalized
values of the quantile at zero and one.

## Reference

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1, 2nd ed.,
  Wiley (1994), section 15.5.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace TauCeti.Probability

variable {a b : ℝ}

/-- Log-uniform quantiles tend to the lower support endpoint `a` as the probability level tends
to zero from above. -/
theorem tendsto_quantile_logUniformMeasure_nhdsGT_zero (ha : 0 < a) (hab : a < b) :
    Tendsto (fun u ↦ ((logUniformMeasure a b).quantile u : EReal)) (𝓝[>] 0) (𝓝 (a : EReal)) := by
  have hb : 0 < b := ha.trans hab
  have hcontinuous : Continuous (fun u : ℝ ↦ a * (b / a) ^ u) :=
    continuous_const.mul (Real.continuous_const_rpow (div_ne_zero hb.ne' ha.ne'))
  have hlim := (hcontinuous.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  simp only [Real.rpow_zero, mul_one] at hlim
  apply (EReal.tendsto_coe.mpr hlim).congr'
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
  exact congrArg (fun x : ℝ ↦ (x : EReal)) (quantile_logUniformMeasure ha hab hu).symm

/-- Log-uniform quantiles tend to the upper support endpoint `b` as the probability level tends
to one from below. -/
theorem tendsto_quantile_logUniformMeasure_nhdsLT_one (ha : 0 < a) (hab : a < b) :
    Tendsto (fun u ↦ ((logUniformMeasure a b).quantile u : EReal)) (𝓝[<] 1) (𝓝 (b : EReal)) := by
  have hb : 0 < b := ha.trans hab
  have hcontinuous : Continuous (fun u : ℝ ↦ a * (b / a) ^ u) :=
    continuous_const.mul (Real.continuous_const_rpow (div_ne_zero hb.ne' ha.ne'))
  have hlim := (hcontinuous.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio 1))
  have hendpoint : a * (b / a) = b := by field_simp
  rw [Real.rpow_one, hendpoint] at hlim
  apply (EReal.tendsto_coe.mpr hlim).congr'
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
  exact congrArg (fun x : ℝ ↦ (x : EReal)) (quantile_logUniformMeasure ha hab hu).symm

end TauCeti.Probability
