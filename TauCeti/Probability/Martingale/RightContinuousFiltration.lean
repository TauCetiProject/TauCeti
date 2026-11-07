/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.LocalProperty
import TauCeti.Probability.Process.StoppedProcess
import TauCeti.Probability.Martingale.Convergence
import Mathlib.Topology.Order.IsLUB

/-!
# Martingales on the right-continuous hull of a filtration

A real martingale whose paths are almost surely right-continuous at each deterministic time
remains a martingale after replacing its filtration by its right-continuous hull. Neither
completeness nor right continuity of the original filtration is required. The exceptional
null set for path right continuity may depend on the time.

The same result holds for native local martingales with almost surely continuous paths,
using exactly the original localizing sequence and its initial-time indicators. It requires
no literal adaptation or initial integrability of the original local process.

These are lifting steps used when passing from a raw stochastic basis to its usual
augmentation. They do not adjoin null sets or complete the ambient measure.

The proof uses Lévy's downward theorem for conditional expectations along times decreasing
to the conditioning time. In particular it does not assume that almost sure path convergence
alone permits passing a conditional expectation through a limit.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991,
  Chapter 1, §2.
-/

public section

open Filter Set
open scoped Topology

namespace MeasureTheory.Martingale

variable {ι Ω : Type*} [LinearOrder ι] [DenselyOrdered ι]
  [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
  {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {ℱ : Filtration ι mΩ} {M : ι → Ω → ℝ}

/-- A martingale with almost surely right-continuous paths at each fixed time remains a
martingale on the right-continuous hull of its filtration. No common exceptional null set,
completion, or right-continuity assumption on the filtration is needed. -/
theorem rightCont (hM : Martingale M ℱ μ)
    (hcont : ∀ s, ∀ᵐ ω ∂μ, ContinuousWithinAt (M · ω) (Ioi s) s) :
    Martingale M ℱ.rightCont μ := by
  refine ⟨fun t => (hM.stronglyAdapted t).mono (ℱ.le_rightCont t), ?_⟩
  intro s t hst
  rcases hst.eq_or_lt with rfl | hst
  · exact (condExp_of_stronglyMeasurable (ℱ.rightCont.le s)
      ((hM.stronglyAdapted s).mono (ℱ.le_rightCont s)) (hM.integrable s)).eventuallyEq
  obtain ⟨u, hanti, hu, hlim⟩ := exists_seq_strictAnti_tendsto' hst
  have hle : ℱ.rightCont s ≤ ⨅ n, ℱ (u n) := by
    refine le_iInf fun n => ?_
    rw [Filtration.rightCont_eq_of_not_isMax ℱ (not_isMax_of_lt hst)]
    exact iInf₂_le (u n) (hu n).1
  have hseq := tendsto_ae_condExp_iInf (μ := μ)
    (fun i j hij => ℱ.mono (hanti.antitone hij))
    (ℱ.le (u 0)) (M t)
  have heq : μ[M t | ⨅ n, ℱ (u n)] =ᵐ[μ] M s := by
    have hversions : ∀ᵐ ω ∂μ, ∀ n, (μ[M t | ℱ (u n)]) ω = M (u n) ω :=
      ae_all_iff.2 fun n => hM.condExp_ae_eq (hu n).2.le
    filter_upwards [hseq, hversions, hcont s] with ω hseq hversions hcont
    have hu' : Tendsto u atTop (𝓝[>] s) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => (hu n).1⟩
    exact tendsto_nhds_unique (hseq.congr hversions) (hcont.tendsto.comp hu')
  have htower := condExp_condExp_of_le hle ((iInf_le _ 0).trans (ℱ.le (u 0)))
    (f := M t) (μ := μ)
  exact htower.symm.trans ((condExp_congr_ae heq).trans
    (condExp_of_stronglyMeasurable (ℱ.rightCont.le s)
      ((hM.stronglyAdapted s).mono (ℱ.le_rightCont s)) (hM.integrable s)).eventuallyEq)

end MeasureTheory.Martingale

namespace ProbabilityTheory.Locally

open MeasureTheory

/-- An almost surely continuous native local martingale remains local for the
right-continuous hull, with its original raw localizing sequence. Literal adaptation of the
original process and integrability of its initial value are not required. -/
theorem martingale_rightCont {ι Ω : Type*} [LinearOrder ι] [OrderBot ι]
    [DenselyOrdered ι] [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ι mΩ} {M : ι → Ω → ℝ}
    (hM : Locally (fun Y => Martingale Y ℱ μ) ℱ M μ)
    (hcont : ∀ᵐ ω ∂μ, Continuous (M · ω)) :
    Locally (fun Y => Martingale Y ℱ.rightCont μ) ℱ.rightCont M μ := by
  refine ⟨hM.localSeq, ?_, fun n => (hM.stoppedProcess_localSeq n).rightCont ?_⟩
  · exact
      { isStoppingTime := fun n t => ℱ.le_rightCont t _
          ((hM.isLocalizingSequence_localSeq.isStoppingTime n).measurableSet_le t)
        tendsto_top := hM.isLocalizingSequence_localSeq.tendsto_top
        mono := hM.isLocalizingSequence_localSeq.mono }
  · intro s
    filter_upwards [hcont] with ω hω
    have hpath : Continuous
        (fun t => {ω | ⊥ < hM.localSeq n ω}.indicator (M t) ω) := by
      by_cases hω' : ⊥ < hM.localSeq n ω
      · simpa [hω'] using hω
      · simpa [hω'] using (continuous_const (y := (0 : ℝ)))
    exact hpath.stoppedProcess.continuousAt.continuousWithinAt

end ProbabilityTheory.Locally
