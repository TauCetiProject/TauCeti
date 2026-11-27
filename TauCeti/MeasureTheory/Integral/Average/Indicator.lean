/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average

/-!
# The average of an indicator

The average over a set `t` of the norm of the indicator of a measurable set `s`, with value `1`,
is the proportion `μ (s ∩ t) / μ t` of `t` that `s` covers. No assumption is made on `t`: when
`μ t` is `0` or `∞` both sides follow the conventions of `ENNReal` division.

## Main results

* `TauCeti.setLAverage_enorm_indicator_one`: `⨍⁻_t ‖1_s‖ₑ ∂μ = μ (s ∩ t) / μ t`.
-/

public section

namespace TauCeti

open MeasureTheory

/-- The average over a set `t` of the norm of the indicator of a measurable set `s` is the
proportion of `t` that `s` covers. -/
theorem setLAverage_enorm_indicator_one {X G : Type*} [MeasurableSpace X]
    [SeminormedAddCommGroup G] [One G] [NormOneClass G] {μ : Measure X} {s : Set X}
    (hs : MeasurableSet s) (t : Set X) :
    ⨍⁻ z in t, ‖s.indicator (1 : X → G) z‖ₑ ∂μ = μ (s ∩ t) / μ t := by
  simp_rw [eNorm_indicator_eq_indicator_eNorm, Pi.one_apply, eNorm_one]
  rw [setLAverage_eq, lintegral_indicator_const hs, one_mul, Measure.restrict_apply hs]

end TauCeti
