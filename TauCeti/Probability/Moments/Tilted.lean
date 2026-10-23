/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.Tilted

/-!
# Generating functions of exponentially tilted measures

Tilting a measure `μ` along a real statistic `X` with parameter `t` reweights it by
`exp (t * X) / mgf X μ t`. Its moment-generating function in the variable `s` is therefore the
moment-generating function of `μ` shifted by `t` and renormalized:
`mgf X (μ.tilted (t * X ·)) s = mgf X μ (t + s) / mgf X μ t`. Consequently its
exponential-integrability domain is the domain of `μ` translated by `-t`, and its
cumulant-generating function is `s ↦ cgf X μ (t + s) - cgf X μ t` there.

Mathlib's `ProbabilityTheory.integral_tilted_mul_self` and
`ProbabilityTheory.variance_tilted_mul` give the first two derivatives of the cumulant-generating
function; the results here describe the whole transform.

## Main results

* `TauCeti.mgf_tilted_mul`: the shifted and renormalized moment-generating function;
* `TauCeti.integrableExpSet_tilted_mul`: the translated exponential-integrability domain;
* `TauCeti.cgf_tilted_mul`: the shifted and recentred cumulant-generating function.
-/

public section

open MeasureTheory ProbabilityTheory Real

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {t s : ℝ}

/-- **The moment-generating function of an exponential tilt.** No integrability hypothesis is
needed: when `exp (t * X)` is not integrable both sides vanish. -/
theorem mgf_tilted_mul (X : Ω → ℝ) (μ : Measure Ω) (t s : ℝ) :
    mgf X (μ.tilted (t * X ·)) s = mgf X μ (t + s) / mgf X μ t := by
  simp_rw [mgf, integral_tilted_mul_eq_mgf, smul_eq_mul, div_mul_eq_mul_div, ← exp_add, ← add_mul,
    integral_div, mgf]

/-- The exponential-integrability domain of the tilt `μ.tilted (t * X ·)` is that of `μ`
translated by `-t`. -/
theorem integrableExpSet_tilted_mul (ht : Integrable (fun ω ↦ exp (t * X ω)) μ) :
    integrableExpSet X (μ.tilted (t * X ·)) = (t + ·) ⁻¹' integrableExpSet X μ := by
  ext s
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_preimage,
    integrable_tilted_iff ht, smul_eq_mul, ← exp_add, ← add_mul]

/-- **The cumulant-generating function of an exponential tilt.** When the exponential moments at
`t` and `t + s` are both finite, tilting by `t` shifts the cumulant-generating function by `t` and
recentres it at zero. -/
theorem cgf_tilted_mul [NeZero μ] (ht : Integrable (fun ω ↦ exp (t * X ω)) μ)
    (hts : Integrable (fun ω ↦ exp ((t + s) * X ω)) μ) :
    cgf X (μ.tilted (t * X ·)) s = cgf X μ (t + s) - cgf X μ t := by
  rw [cgf, mgf_tilted_mul, log_div (mgf_pos' (NeZero.ne μ) hts).ne' (mgf_pos' (NeZero.ne μ) ht).ne',
    cgf, cgf]

end TauCeti
