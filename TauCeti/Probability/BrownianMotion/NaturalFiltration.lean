/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Measure.Tilted
public import TauCeti.Probability.Process.Filtration.Natural
import TauCeti.Probability.BrownianMotion.ExponentialMartingale

/-!
# The augmented natural filtration under a constant Brownian tilt

Let `Q` be the tilt of `P` by `-κ W_T`, with density
`exp (-κ W_T - κ² T / 2)`. The usual augmented natural filtrations of `W` under `P`
and of `t ↦ W_t + κ t` under `Q` coincide. This identifies the information available
in the two descriptions of a constant-coefficient market, as needed when applying
natural-Brownian martingale representation after a change of measure.

The equality of filtrations holds at every time. The Brownian interpretation of the
translated process is only on the tilting horizon; this file makes no assertion about
its law, or about martingale representation. In particular, the deterministic-translation
argument does not apply to a random market price of risk.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §3.5.
* S. E. Shreve, *Stochastic Calculus for Finance II*, Springer, 2004, §5.2.
-/

public section

noncomputable section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-- Under the constant-drift exponential change of measure, the usual augmented natural
σ-algebra of `W_t + κ t` is the usual augmented natural σ-algebra of `W_t` under the
original measure. The change of measure is constructed here, not assumed equivalent. -/
theorem rightCont_nullAugment_natural_add_drift_tilted (hW : IsPreBrownianReal W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) (κ : ℝ) (T t : ℝ≥0) :
    ((Filtration.natural (fun u ω => W u ω + κ * u)
      (fun u => (hmeas u).add_const (κ * u))).nullAugment
        (P.tilted (fun ω => -κ * W T ω))).rightCont t =
      ((Filtration.natural W hmeas).nullAugment P).rightCont t := by
  exact Filtration.rightCont_nullAugment_natural_add_deterministic W hmeas
    (fun u => κ * u) (absolutelyContinuous_tilted (hW.integrable_exp_mul_eval (-κ) T))
    (tilted_absolutelyContinuous P _) t

end ProbabilityTheory.IsPreBrownianReal
