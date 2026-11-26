/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import TauCeti.Probability.Process.Filtration.Natural
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import TauCeti.MeasureTheory.Function.ConditionalExpectation.Completion
import TauCeti.Probability.BrownianMotion.UsualFiltration

/-!
# Right continuity of the augmented natural Brownian filtration

Adjoining ambient null sets to the natural filtration of Brownian motion already makes it
right-continuous. No right-continuation needs to add further information. This identifies the
completed natural sigma-algebra at each date with that of the usual Brownian filtration,
which is important when representing terminal claims by Brownian stochastic integrals.

The whole future increment process is independent of the right-continuous natural past.
An event in that past is also determined by the original past and the future increments;
conditioning on the original past therefore recovers its indicator. The conclusion concerns
null augmentation on the completed ambient space, not right continuity of the raw filtration.
The usual augmentation therefore has the same `Lᵖ` claims at every time as the natural
filtration, for every exponent and complete normed target space.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §2.7.A.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory.IsBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-- The entire future increment process of Brownian motion is independent of its raw
right-continuous natural past. This is independence of the process, not just of each increment. -/
theorem indep_shift_rightCont_natural (hW : IsBrownianReal W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) (s : ℝ≥0) :
    Indep (MeasurableSpace.comap (fun ω v => W (s + v) ω - W s ω) inferInstance)
      ((Filtration.natural W hmeas).rightCont s) P :=
  (hW.isFilteredPreBrownianReal_natural hmeas).indep_shift_rightCont
    (hW.cont.mono fun _ hω => hω.continuousAt.continuousWithinAt)

/-- Every event of the raw right-continuous natural Brownian filtration has a representative
in the original natural sigma-algebra at the same time. -/
theorem rightCont_natural_le_nullAugment (hW : IsBrownianReal W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) (s : ℝ≥0) :
    (Filtration.natural W hmeas).rightCont s ≤
      (Filtration.natural W hmeas).nullAugment P s := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact Filtration.rightCont_natural_le_nullAugment_of_indep_shift hmeas
    (hW.indep_shift_rightCont_natural hmeas s)

/-- The null-augmented natural filtration of Brownian motion is right-continuous. This uses
the completed ambient space of `Filtration.nullAugment`; no completeness of `P` is assumed. -/
theorem isRightContinuous_nullAugment_natural (hW : IsBrownianReal W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) :
    ((Filtration.natural W hmeas).nullAugment P).IsRightContinuous :=
  Filtration.isRightContinuous_nullAugment_of_rightCont_le_nullAugment
    (hW.rightCont_natural_le_nullAugment hmeas)

/-- The usual augmentation of the natural filtration of a Brownian motion has the same `Lᵖ`
claims at every time as the natural filtration itself, for every exponent and complete normed
target space. -/
theorem lpMeas_rightCont_nullAugment_natural_eq_lpMeas_natural (hW : IsBrownianReal W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) {F 𝕜 : Type*} [RCLike 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] (p : ℝ≥0∞) (T : ℝ≥0) :
    lpMeas F 𝕜 (((Filtration.natural W hmeas).nullAugment P).rightCont T) p P =
      lpMeas F 𝕜 (Filtration.natural W hmeas T) p P := by
  have := hW.isRightContinuous_nullAugment_natural hmeas
  rw [Filtration.IsRightContinuous.eq, Filtration.nullAugment_apply]
  exact TauCeti.MeasureTheory.lpMeas_eventuallyMeasurableSpace p

end ProbabilityTheory.IsBrownianReal
