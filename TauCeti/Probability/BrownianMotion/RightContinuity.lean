/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import TauCeti.Probability.Process.Filtration.Natural
import TauCeti.Probability.Independence.Filtration

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

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §2.7.A.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.IsBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-- The entire future increment process of Brownian motion is independent of its raw
right-continuous natural past. This is independence of the process, not just of each increment. -/
theorem indep_shift_rightCont_natural (hW : IsBrownianReal W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) (s : ℝ≥0) :
    Indep (MeasurableSpace.comap (fun ω v => W (s + v) ω - W s ω) inferInstance)
      ((Filtration.natural W hmeas).rightCont s) P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine (Filtration.stronglyAdapted_natural hmeas).adapted.indep_comap_shift_rightCont
    (fun r t hrt ↦ ?_) (fun r ↦ ?_) s
  · have hfull : Indep (MeasurableSpace.comap
        (fun ω v => W (r + v) ω - W r ω) inferInstance) (Filtration.natural W hmeas r) P := by
      rw [Filtration.natural_eq_comap]
      exact (IndepFun_iff_Indep ..).1 (hW.indepFun_shift r)
    refine indep_of_indep_of_le_left hfull ?_
    have hproj := MeasurableSpace.comap_le_comap_pi
      (g := fun v ω => W (r + v) ω - W r ω) (t - r)
    simpa only [add_tsub_cancel_of_le hrt, Pi.sub_def] using hproj
  · obtain ⟨u, -, hu, hlim⟩ := exists_seq_strictAnti_tendsto r
    refine ⟨u, hu, hlim, ?_⟩
    filter_upwards [hW.cont] with ω hω
    exact hω.continuousAt.tendsto.comp hlim

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

end ProbabilityTheory.IsBrownianReal
