/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.Process.Filtration.NullAugmentation
import TauCeti.Probability.HasLaw
import TauCeti.Probability.Independence.Completion
import TauCeti.Probability.Independence.Limit
import Mathlib.Topology.Order.IsLUB

/-!
# Brownian motion on the usual augmentation

A Brownian motion relative to a filtration remains Brownian after adjoining ambient null
sets and making the filtration right-continuous. The completed measure is explicit: no
completeness assumption on the original probability space is needed. Applied to the natural
filtration, this supplies the usual augmented Brownian filtration used in continuous-time
markets.

For right-continuation, increments starting strictly after `s` are independent of every
right-continuous event at `s`. Taking their almost sure limit as their starting times decrease
to `s` gives independence of the increment starting at `s`. Only right continuity of paths
at the starting time is needed, and its exceptional set may depend on that time.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §2.7.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- A filtered pre-Brownian motion whose paths are almost surely right-continuous at each
fixed time remains filtered pre-Brownian on the right-continuation of its filtration. -/
theorem rightCont (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ s, ∀ᵐ ω ∂P, ContinuousWithinAt (W · ω) (Ioi s) s) :
    IsFilteredPreBrownianReal ℱ.rightCont W P := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine ⟨hW.toIsPreBrownianReal,
    fun t => (hW.adapted t).mono (ℱ.le_rightCont t) le_rfl, ?_⟩
  intro s t hst
  apply Indep.symm
  rcases hst.eq_or_lt with rfl | hst
  · have hzero : W s - W s = fun _ => (0 : ℝ) := funext fun ω => sub_self _
    rw [hzero, MeasurableSpace.comap_const]
    exact indep_bot_right (ℱ.rightCont s)
  obtain ⟨u, -, hu, hlim⟩ := exists_seq_strictAnti_tendsto' hst
  have hind (n : ℕ) : Indep (ℱ.rightCont s) (.comap (W t - W (u n)) inferInstance) P := by
    have hle : ℱ.rightCont s ≤ ℱ (u n) := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le (u n) (hu n).1
    exact indep_of_indep_of_le_left (hW.indep_sub (hu n).2.le).symm hle
  refine indep_comap_of_ae_tendsto (ℱ.rightCont.le s)
    (fun n => (hW.adapted.measurable.sub hW.adapted.measurable).aemeasurable)
    (hW.adapted.measurable.sub hW.adapted.measurable).aemeasurable hind ?_
  filter_upwards [hcont s] with ω hω
  have hu' : Tendsto u atTop (nhdsWithin s (Ioi s)) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => (hu n).1⟩
  exact tendsto_const_nhds.sub (hω.tendsto.comp hu')

/-- Completing the probability space and adjoining all ambient null events to the
filtration preserves the filtered pre-Brownian property. -/
theorem nullAugment (hW : IsFilteredPreBrownianReal ℱ W P) :
    @IsFilteredPreBrownianReal (NullMeasurableSpace Ω P) inferInstance (ℱ.nullAugment P)
      (fun t (ω : NullMeasurableSpace Ω P) => W t ω) P.completion where
  toIsPreBrownianReal.hasLaw I := (hW.hasLaw I).completion
  adapted t := (hW.adapted t).mono (ℱ.le_nullAugment P t) le_rfl
  indep_sub s t hst := by
    have hind : Indep (.comap (W t - W s) inferInstance) (ℱ.nullAugment P s) P := by
      rw [Filtration.nullAugment_apply]
      exact (hW.indep_sub hst).eventuallyMeasurableSpace_right
    -- `NullMeasurableSpace` changes only the source sigma-algebra, not the increment function.
    change @Indep (NullMeasurableSpace Ω P) (.comap (W t - W s) inferInstance)
      (ℱ.nullAugment P s) inferInstance P.completion
    exact indep_completion_iff.mpr hind

/-- On the completed space, a filtered pre-Brownian motion with almost surely
right-continuous paths at each fixed time is filtered pre-Brownian on the usual augmentation. -/
theorem rightCont_nullAugment (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ s, ∀ᵐ ω ∂P, ContinuousWithinAt (W · ω) (Ioi s) s) :
    @IsFilteredPreBrownianReal (NullMeasurableSpace Ω P) inferInstance (ℱ.nullAugment P).rightCont
      (fun t (ω : NullMeasurableSpace Ω P) => W t ω) P.completion :=
  hW.nullAugment.rightCont hcont

end TauCeti.Probability.IsFilteredPreBrownianReal

namespace ProbabilityTheory.IsBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

/-- A Brownian motion with measurable coordinates is Brownian relative to its usual
augmented natural filtration, with increment independence relative to that filtration. -/
theorem isFilteredPreBrownianReal_rightCont_nullAugment_natural (hW : IsBrownianReal W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) :
    @TauCeti.Probability.IsFilteredPreBrownianReal (NullMeasurableSpace Ω P) inferInstance
      ((Filtration.natural W hmeas).nullAugment P).rightCont
      (fun t (ω : NullMeasurableSpace Ω P) => W t ω) P.completion := by
  apply (hW.toIsPreBrownianReal.isFilteredPreBrownianReal_natural hmeas).rightCont_nullAugment
  intro s
  exact hW.cont.mono fun ω hω => hω.continuousAt.continuousWithinAt

end ProbabilityTheory.IsBrownianReal
