/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.UsualFiltration

/-!
# Usual-augmentation invariance of the Brownian Itô integral

Completing the ambient probability space and passing to the usual null and right-continuous
augmentations preserves `TauCeti.Probability.IsItoIntegral`
(`TauCeti.Probability.IsItoIntegral.mono_completion`,
`TauCeti.Probability.IsItoIntegral.nullAugment`,
`TauCeti.Probability.IsItoIntegral.rightCont_nullAugment`). Consequently, against a filtered
pre-Brownian motion whose paths are almost surely right-continuous at each fixed time, any raw
Itô integral is indistinguishable on the completed space from any Itô integral constructed on
the usual right-continuous null augmentation
(`TauCeti.Probability.isItoIntegral_indist_rightCont_nullAugment`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open MeasureTheory Filter Set ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  {W H I : ℝ≥0 → Ω → ℝ}

/-- Transporting `IsItoIntegral` to a larger filtration on the completed ambient space
`(NullMeasurableSpace Ω P, P.completion)`. -/
theorem IsItoIntegral.mono_completion (hI : IsItoIntegral ℱ P W H I)
    {𝒢 : Filtration ℝ≥0 (eventuallyMeasurableSpace mΩ (ae P))}
    (hFG : ∀ t, ℱ t ≤ 𝒢 t) :
    @IsItoIntegral (NullMeasurableSpace Ω P) inferInstance 𝒢 P.completion
      (fun t (ω : NullMeasurableSpace Ω P) ↦ W t ω)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ H t ω)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ I t ω) where
  isStronglyPredictable := hI.isStronglyPredictable.mono
    (measurableSpace_le_predictable_of_measurableSet
      (fun _ hA ↦ measurableSet_predictable_singleton_bot_prod (hFG ⊥ _ hA))
      (fun i _ hA ↦ measurableSet_predictable_Ioi_prod (i := i) (hFG i _ hA)))
  ae_continuous := hI.ae_continuous.filter_mono P.ae_completion.le
  exists_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hen, hg⟩ := hI.exists_approx t
    refine ⟨n, τ, a, hτ, fun k j hj ↦ (ha k j hj).mono (hFG _), fun ε hε ↦ ?_, fun ε hε ↦ ?_⟩
    · exact (hen ε hε).congr fun k ↦ (Measure.completion_apply P _).symm
    · exact (hg ε hε).congr fun k ↦ (Measure.completion_apply P _).symm

/-- Completing the ambient space and adjoining all ambient null sets to the filtration preserves
`IsItoIntegral`. -/
theorem IsItoIntegral.nullAugment (hI : IsItoIntegral ℱ P W H I) :
    @IsItoIntegral (NullMeasurableSpace Ω P) inferInstance (ℱ.nullAugment P) P.completion
      (fun t (ω : NullMeasurableSpace Ω P) ↦ W t ω)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ H t ω)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ I t ω) :=
  hI.mono_completion (ℱ.le_nullAugment P)

/-- Passing to the usual right-continuous null augmentation preserves `IsItoIntegral`. -/
theorem IsItoIntegral.rightCont_nullAugment (hI : IsItoIntegral ℱ P W H I) :
    @IsItoIntegral (NullMeasurableSpace Ω P) inferInstance (ℱ.nullAugment P).rightCont P.completion
      (fun t (ω : NullMeasurableSpace Ω P) ↦ W t ω)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ H t ω)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ I t ω) :=
  @IsItoIntegral.mono (NullMeasurableSpace Ω P) inferInstance (ℱ.nullAugment P) P.completion _ _ _
    (ℱ.nullAugment P).rightCont hI.nullAugment ((ℱ.nullAugment P).le_rightCont)

/-- Against a filtered pre-Brownian motion with paths almost surely right-continuous at each
fixed time, any raw Itô integral is indistinguishable from any Itô integral constructed on the
usual right-continuous null augmentation `(ℱ.nullAugment P).rightCont`. -/
theorem isItoIntegral_indist_rightCont_nullAugment
    (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ s, ∀ᵐ ω ∂P, ContinuousWithinAt (W · ω) (Ioi s) s)
    (hI : IsItoIntegral ℱ P W H I)
    {J : ℝ≥0 → NullMeasurableSpace Ω P → ℝ}
    (hJ : @IsItoIntegral (NullMeasurableSpace Ω P) inferInstance
      (ℱ.nullAugment P).rightCont P.completion
      (fun t (ω : NullMeasurableSpace Ω P) ↦ W t ω)
      (fun t (ω : NullMeasurableSpace Ω P) ↦ H t ω) J) :
    (fun t (ω : NullMeasurableSpace Ω P) ↦ I t ω) ≡ᵐ[P.completion] J :=
  @isItoIntegral_unique (NullMeasurableSpace Ω P) inferInstance
    (ℱ.nullAugment P).rightCont P.completion
    (fun t (ω : NullMeasurableSpace Ω P) ↦ W t ω)
    (fun t (ω : NullMeasurableSpace Ω P) ↦ H t ω)
    (fun t (ω : NullMeasurableSpace Ω P) ↦ I t ω) J
    (hW.rightCont_nullAugment hcont) hI.rightCont_nullAugment hJ

end TauCeti.Probability
