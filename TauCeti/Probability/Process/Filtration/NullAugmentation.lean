/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Filtration
public import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
public import Mathlib.MeasureTheory.MeasurableSpace.EventuallyMeasurable
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.Order.IsLUB

/-!
# Augmenting a filtration by ambient null sets

`MeasureTheory.Filtration.nullAugment` adjoins all ambient null sets at every time,
not just the null sets of the measure restricted to that time's σ-algebra.
Its events are exactly those equal almost everywhere to an event of the original filtration.
Taking its `Filtration.rightCont` gives the usual right-continuous augmentation. On a densely
ordered first-countable time axis without a last time, this commutes with null augmentation
(`MeasureTheory.Filtration.rightCont_nullAugment_apply`).

Equivalent measures give the same augmented σ-algebras, including after right-continuation.
This allows a change of probability measure without changing the information available to a
trading strategy. The ambient measurable space is completed explicitly; completeness of the
original space is not assumed.
-/

public section

noncomputable section

open Filter

namespace MeasureTheory.Filtration

variable {Ω ι : Type*} {m : MeasurableSpace Ω}

section Preorder

variable [Preorder ι]

/-- Adjoin all ambient `P`-null sets to each σ-algebra of `ℱ`. The resulting filtration
lives on the completion of the ambient measurable space. -/
def nullAugment (ℱ : Filtration ι m) (P : Measure Ω) :
    Filtration ι (eventuallyMeasurableSpace m (ae P)) where
  seq i := eventuallyMeasurableSpace (ℱ i) (ae P)
  mono' i j hij s := by
    rintro ⟨t, ht, hst⟩
    exact ⟨t, ℱ.mono hij t ht, hst⟩
  le' i s := by
    rintro ⟨t, ht, hst⟩
    exact ⟨t, ℱ.le i t ht, hst⟩

@[simp]
theorem nullAugment_apply (ℱ : Filtration ι m) (P : Measure Ω) (i : ι) :
    ℱ.nullAugment P i = eventuallyMeasurableSpace (ℱ i) (ae P) :=
  (rfl)

/-- An augmented event has a representative measurable at the original time. -/
theorem measurableSet_nullAugment_iff (ℱ : Filtration ι m) (P : Measure Ω)
    (i : ι) (s : Set Ω) :
    MeasurableSet[ℱ.nullAugment P i] s ↔
      ∃ t, MeasurableSet[ℱ i] t ∧ s =ᵐ[P] t :=
  Iff.rfl

/-- Original events remain measurable after null augmentation. -/
theorem le_nullAugment (ℱ : Filtration ι m) (P : Measure Ω) (i : ι) :
    ℱ i ≤ ℱ.nullAugment P i :=
  le_eventuallyMeasurableSpace

/-- Every ambient null set, including nonmeasurable subsets of null sets, is known
at every time after augmentation. -/
theorem measurableSet_nullAugment_of_null (ℱ : Filtration ι m) (P : Measure Ω)
    (i : ι) {s : Set Ω} (hs : P s = 0) :
    MeasurableSet[ℱ.nullAugment P i] s := by
  rw [measurableSet_nullAugment_iff]
  refine ⟨∅, @MeasurableSet.empty Ω (ℱ i), ?_⟩
  exact ae_eq_empty.mpr hs

/-- Null augmentation is the smallest enlargement containing the original events
and closed under equality modulo ambient null sets. -/
theorem nullAugment_le_iff (ℱ : Filtration ι m) (P : Measure Ω)
    (𝒢 : Filtration ι (eventuallyMeasurableSpace m (ae P)))
    (h𝒢 : ∀ i (s t : Set Ω), MeasurableSet[𝒢 i] t → s =ᵐ[P] t →
      MeasurableSet[𝒢 i] s) :
    ℱ.nullAugment P ≤ 𝒢 ↔ ∀ i, ℱ i ≤ 𝒢 i := by
  constructor
  · exact fun h i => (ℱ.le_nullAugment P i).trans (h i)
  · intro h i s hs
    rcases hs with ⟨t, ht, hst⟩
    exact h𝒢 i s t (h i t ht) hst

/-- Equivalent measures yield identical null-augmented σ-algebras. Equality is stated
at each time so no identification of the two ambient completions is required. -/
theorem nullAugment_apply_eq_of_absolutelyContinuous (ℱ : Filtration ι m)
    {P Q : Measure Ω} (hPQ : P ≪ Q) (hQP : Q ≪ P) (i : ι) :
    ℱ.nullAugment P i = ℱ.nullAugment Q i := by
  apply le_antisymm
  · rintro s ⟨t, ht, hst⟩
    exact ⟨t, ht, hQP.ae_eq hst⟩
  · rintro s ⟨t, ht, hst⟩
    exact ⟨t, ht, hPQ.ae_eq hst⟩

end Preorder

/-- The usual right-continuous augmentations agree under equivalent measures. -/
theorem rightCont_nullAugment_apply_eq_of_absolutelyContinuous
    [PartialOrder ι] (ℱ : Filtration ι m)
    {P Q : Measure Ω} (hPQ : P ≪ Q) (hQP : Q ≪ P) (i : ι) :
    (ℱ.nullAugment P).rightCont i = (ℱ.nullAugment Q).rightCont i := by
  let := Preorder.topology ι
  have : OrderTopology ι := ⟨rfl⟩
  simp only [rightCont_apply, ℱ.nullAugment_apply_eq_of_absolutelyContinuous hPQ hQP]

/-- On a densely ordered first-countable time axis with no last time, null augmentation
commutes with right-continuation. The completion uses ambient null sets in both orders. -/
theorem rightCont_nullAugment_apply [LinearOrder ι] [DenselyOrdered ι] [NoMaxOrder ι]
    [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
    (ℱ : Filtration ι m) (P : Measure Ω) (i : ι) :
    (ℱ.nullAugment P).rightCont i = ℱ.rightCont.nullAugment P i := by
  classical
  apply le_antisymm
  · intro A hA
    obtain ⟨u, -, hu, hlim⟩ := exists_seq_strictAnti_tendsto i
    have hAn (n : ℕ) : MeasurableSet[ℱ.nullAugment P (u n)] A := by
      have hle : (ℱ.nullAugment P).rightCont i ≤ ℱ.nullAugment P (u n) := by
        rw [(ℱ.nullAugment P).rightCont_eq]
        exact iInf₂_le (u n) (hu n)
      exact hle A hA
    choose B hB hAB using hAn
    refine ⟨Filter.limsup B Filter.atTop, ?_,
      (limsup_ae_eq_of_forall_ae_eq B (fun n => (hAB n).symm)).symm⟩
    rw [ℱ.rightCont_eq]
    simp only [MeasurableSpace.measurableSet_iInf]
    intro j hij
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hlim.eventually (gt_mem_nhds hij))
    have htail : Filter.limsup B Filter.atTop =
        Filter.limsup (fun n => if N ≤ n then B n else ∅) Filter.atTop :=
      Filter.limsup_congr ((Filter.eventually_ge_atTop N).mono fun n hn => by simp [hn])
    rw [htail]
    let : MeasurableSpace Ω := ℱ j
    exact MeasurableSet.measurableSet_limsup fun n => by
      split_ifs with hn
      · exact ℱ.mono (hN n hn).le _ (hB n)
      · exact MeasurableSet.empty
  · rintro A ⟨B, hB, hAB⟩
    rw [(ℱ.nullAugment P).rightCont_eq]
    simp only [MeasurableSpace.measurableSet_iInf]
    intro j hij
    have hle : ℱ.rightCont i ≤ ℱ j := by
      rw [ℱ.rightCont_eq]
      exact iInf₂_le j hij
    exact ⟨B, hle _ hB, hAB⟩

end MeasureTheory.Filtration
