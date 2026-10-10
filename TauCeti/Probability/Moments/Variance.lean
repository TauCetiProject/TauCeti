/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5

Staged for Tau Ceti, roadmap topic T20.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Probability/Moments/Variance.lean`.

Formalized by Claude Fable 5 (claude-fable-5[1m]).
-/
module

public import Mathlib.Probability.Moments.Variance


/-! # Uncentered second-moment Chebyshev inequality

`P {ω | η < Y ω} ≤ ENNReal.ofReal (v / η ^ 2)` from `∫ Y² ≤ v`, for a real
random variable `Y` that need not be centered, nonnegative, or measurable
(integrability of `Y ^ 2` suffices).

Mathlib's `meas_ge_le_variance_div_sq` is the centered version and requires
`MemLp Y 2`; concentration arguments routinely need the raw second-moment form
below, applied to error norms `Y = ‖Xᵢ - μᵢ‖`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Probability.Moments.Variance`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `56f7495`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Fable 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open MeasureTheory

/--
**Uncentered second-moment Chebyshev.**  If `∫ Y² ≤ v` and `0 < η`, then
`P {ω | η < Y ω} ≤ ENNReal.ofReal (v / η ^ 2)`.  No measurability of `Y` is
required beyond integrability of `Y ^ 2`.
-/
theorem meas_gt_le_ofReal_integral_sq_div_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → ℝ}
    (hY_int : Integrable (fun ω => Y ω ^ 2) P)
    {v η : ℝ} (hη : 0 < η) (hmoment : ∫ ω, Y ω ^ 2 ∂P ≤ v) :
    P {ω | η < Y ω} ≤ ENNReal.ofReal (v / η ^ 2) := by
  -- Markov on `Y ^ 2` at level `η ^ 2`.
  have hsq_nonneg : 0 ≤ᵐ[P] fun ω => Y ω ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg (Y ω)
  have hmarkov :
      η ^ 2 * P.real {ω | η ^ 2 ≤ Y ω ^ 2} ≤ ∫ ω, Y ω ^ 2 ∂P :=
    mul_meas_ge_le_integral_of_nonneg hsq_nonneg hY_int (η ^ 2)
  -- The bad set is contained in the squared-threshold set.
  have hsubset : {ω | η < Y ω} ⊆ {ω | η ^ 2 ≤ Y ω ^ 2} := fun ω hω =>
    pow_le_pow_left₀ hη.le (le_of_lt hω) 2
  have hηsq_pos : 0 < η ^ 2 := by positivity
  -- Real-valued bound on `P.real` of the bad set.
  have hbad_real : P.real {ω | η < Y ω} ≤ v / η ^ 2 := by
    have hmono : P.real {ω | η < Y ω} ≤ P.real {ω | η ^ 2 ≤ Y ω ^ 2} :=
      measureReal_mono hsubset
    have h2 : η ^ 2 * P.real {ω | η < Y ω} ≤ v :=
      ((mul_le_mul_of_nonneg_left hmono hηsq_pos.le).trans hmarkov).trans hmoment
    rw [le_div_iff₀ hηsq_pos]
    linarith
  -- Convert to `ENNReal`.
  have hne_top : P {ω | η < Y ω} ≠ ⊤ := measure_ne_top P _
  calc P {ω | η < Y ω}
      = ENNReal.ofReal (P.real {ω | η < Y ω}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal hne_top]
    _ ≤ ENNReal.ofReal (v / η ^ 2) := ENNReal.ofReal_le_ofReal hbad_real

end TauCeti
