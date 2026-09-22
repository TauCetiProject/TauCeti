/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.IntegrableExpMul

import Mathlib.Probability.Moments.Basic

/-!
# Exponential moments of a statistic that is bounded below

Mathlib's `ProbabilityTheory.integrable_exp_mul_of_le` makes `exp (t * X)` integrable against a
finite measure when `X` is bounded above and the rate `t` is nonnegative. A law carried by a
half-line `[b, ∞)` needs the mirror image: `X` bounded below and `t` nonpositive. Both bounds are
one-sided, so neither statement follows from the two-sided
`ProbabilityTheory.integrable_exp_mul_of_mem_Icc`.

For such a law the remaining question is which positive rates survive, and that is decided by the
tail: if `X` already has an infinite moment of some order, then no positive rate is integrable
either, because an exponential moment on both sides of the origin forces every moment to be
finite. Combining the two statements gives the exponential-moment domain of a heavy-tailed
half-line law, which is `Set.Iic 0`.

## Main results

* `TauCeti.integrable_exp_mul_of_ge` — every nonpositive rate is integrable when `X` is bounded
  below;
* `TauCeti.not_integrable_exp_mul_of_not_integrable_rpow` and
  `TauCeti.not_integrable_exp_mul_of_not_integrable_pow` — no positive rate is integrable once a
  real, respectively natural, moment of `X` fails to exist.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}

/-- **A nonpositive exponential rate is integrable when the statistic is bounded below.** On
`b ≤ X` the integrand `exp (t * X)` is at most `exp (t * b)` for `t ≤ 0`, which a finite measure
integrates. This is the mirror image of `ProbabilityTheory.integrable_exp_mul_of_le`, which bounds
`X` above and asks for a nonnegative rate. -/
theorem integrable_exp_mul_of_ge [IsFiniteMeasure μ] (t b : ℝ) (ht : t ≤ 0)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, b ≤ X ω) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) μ := by
  have h := integrable_exp_mul_of_le (μ := μ) (X := fun ω ↦ -X ω) (-t) (-b)
    (neg_nonneg.mpr ht) hX.neg (hb.mono fun _ hω ↦ neg_le_neg hω)
  simpa only [neg_mul_neg] using h

/-- **A statistic bounded below whose moment of order `q` is infinite has no positive exponential
moment.** The nonpositive rates cost nothing here, so a positive rate would give exponential
integrability on both sides of the origin, and that makes every moment finite. -/
theorem not_integrable_exp_mul_of_not_integrable_rpow [IsFiniteMeasure μ] {b t : ℝ} (q : ℝ)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, b ≤ X ω) (hq : 0 ≤ q)
    (hmom : ¬ Integrable (fun ω ↦ X ω ^ q) μ) (ht : 0 < t) :
    ¬ Integrable (fun ω ↦ Real.exp (t * X ω)) μ := fun hexp ↦
  hmom <| integrable_rpow_of_integrable_exp_mul ht.ne' hexp
    (integrable_exp_mul_of_ge (-t) b (neg_nonpos.mpr ht.le) hX hb) hq

/-- **A statistic bounded below whose `n`-th moment is infinite has no positive exponential
moment**, the natural-power form of
`TauCeti.not_integrable_exp_mul_of_not_integrable_rpow`. -/
theorem not_integrable_exp_mul_of_not_integrable_pow [IsFiniteMeasure μ] {b t : ℝ} (n : ℕ)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, b ≤ X ω)
    (hmom : ¬ Integrable (fun ω ↦ X ω ^ n) μ) (ht : 0 < t) :
    ¬ Integrable (fun ω ↦ Real.exp (t * X ω)) μ := fun hexp ↦
  hmom <| integrable_pow_of_integrable_exp_mul ht.ne' hexp
    (integrable_exp_mul_of_ge (-t) b (neg_nonpos.mpr ht.le) hX hb) n

end TauCeti
