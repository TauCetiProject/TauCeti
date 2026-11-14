/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Filtration.NullAugmentation
public import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.Order.IsLUB

/-!
# Null augmentation without completing the ambient space

`MeasureTheory.Filtration.ambientNullAugmentation` adjoins the ambient-measurable null
sets to a filtration, while retaining the original ambient measurable space and measure.
An event belongs to the augmented filtration exactly when it is ambient-measurable and
agrees almost everywhere with an event of the original filtration. This is the least
filtration containing the original information and all ambient-measurable null events.

Unlike `Filtration.nullAugment`, this construction does not adjoin nonmeasurable subsets
of null sets. Completing its sigma-algebras afterwards recovers `Filtration.nullAugment`.
Equivalent measures give the same augmentation. Ambient-measurable versions of adapted
processes become adapted after this augmentation; no path regularity is needed for that
fixed-time assertion. On a first-countable linearly ordered time axis with the order topology,
original-space null augmentation commutes with right-continuation
(`MeasureTheory.Filtration.rightCont_ambientNullAugmentation`).

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §2.7.A.
-/

public section

open Filter MeasurableSpace
open scoped symmDiff

namespace MeasureTheory.Filtration

variable {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι]

/-- Adjoin every ambient-measurable null event at every time, without changing the
ambient measurable space. -/
def ambientNullAugmentation (ℱ : Filtration ι m) (P : Measure Ω) : Filtration ι m where
  seq i := m ⊓ ℱ.nullAugment P i
  mono' _ _ hij := inf_le_inf_left m ((ℱ.nullAugment P).mono hij)
  le' _ := inf_le_left

/-- The original-space augmentation is the ambient-measurable part of the completed
augmentation. -/
@[simp]
theorem ambientNullAugmentation_apply (ℱ : Filtration ι m) (P : Measure Ω) (i : ι) :
    ℱ.ambientNullAugmentation P i = m ⊓ ℱ.nullAugment P i :=
  (rfl)

/-- Augmented events are precisely the ambient-measurable events having an original
filtration-measurable representative modulo null sets. -/
theorem measurableSet_ambientNullAugmentation_iff (ℱ : Filtration ι m) (P : Measure Ω)
    (i : ι) (s : Set Ω) :
    MeasurableSet[ℱ.ambientNullAugmentation P i] s ↔
      MeasurableSet s ∧ ∃ t, MeasurableSet[ℱ i] t ∧ s =ᵐ[P] t := by
  rw [ambientNullAugmentation_apply, measurableSet_inf, measurableSet_nullAugment_iff]

/-- Original information is retained. -/
theorem le_ambientNullAugmentation (ℱ : Filtration ι m) (P : Measure Ω) :
    ℱ ≤ ℱ.ambientNullAugmentation P :=
  fun i ↦ le_inf (ℱ.le i) (ℱ.le_nullAugment P i)

/-- All ambient-measurable null events are known at every time. -/
theorem measurableSet_ambientNullAugmentation_of_null (ℱ : Filtration ι m) (P : Measure Ω)
    (i : ι) {s : Set Ω} (hs : MeasurableSet s) (hP : P s = 0) :
    MeasurableSet[ℱ.ambientNullAugmentation P i] s :=
  measurableSet_inf.mpr ⟨hs, ℱ.measurableSet_nullAugment_of_null P i hP⟩

/-- The augmentation is closed under ambient-measurable changes on null sets. -/
theorem measurableSet_ambientNullAugmentation_congr (ℱ : Filtration ι m) (P : Measure Ω)
    (i : ι) {s t : Set Ω} (hs : MeasurableSet s)
    (ht : MeasurableSet[ℱ.ambientNullAugmentation P i] t) (hst : s =ᵐ[P] t) :
    MeasurableSet[ℱ.ambientNullAugmentation P i] s := by
  obtain ⟨_, u, hu, htu⟩ := (ℱ.measurableSet_ambientNullAugmentation_iff P i t).mp ht
  exact (ℱ.measurableSet_ambientNullAugmentation_iff P i s).mpr ⟨hs, u, hu, hst.trans htu⟩

/-- Leastness among filtrations on the original space containing all ambient-measurable
null events. -/
theorem ambientNullAugmentation_le_iff (ℱ 𝒢 : Filtration ι m) (P : Measure Ω)
    (h𝒢 : ∀ i (s : Set Ω), MeasurableSet s → P s = 0 → MeasurableSet[𝒢 i] s) :
    ℱ.ambientNullAugmentation P ≤ 𝒢 ↔ ℱ ≤ 𝒢 := by
  refine ⟨fun h ↦ (ℱ.le_ambientNullAugmentation P).trans h, fun h i s hs ↦ ?_⟩
  obtain ⟨hs, t, ht, hst⟩ := (ℱ.measurableSet_ambientNullAugmentation_iff P i s).mp hs
  have hdiff := h𝒢 i (s ∆ t) (hs.symmDiff (ℱ.le i t ht))
    (measure_symmDiff_eq_zero_iff.mpr hst)
  simpa using hdiff.symmDiff (h i t ht)

/-- A filtration already containing the ambient-measurable null events is unchanged. -/
theorem ambientNullAugmentation_eq_self (ℱ : Filtration ι m) (P : Measure Ω)
    (hℱ : ∀ i (s : Set Ω), MeasurableSet s → P s = 0 → MeasurableSet[ℱ i] s) :
    ℱ.ambientNullAugmentation P = ℱ :=
  le_antisymm ((ℱ.ambientNullAugmentation_le_iff ℱ P hℱ).mpr le_rfl)
    (ℱ.le_ambientNullAugmentation P)

/-- Null augmentation is monotone in the original filtration. -/
theorem ambientNullAugmentation_mono {ℱ 𝒢 : Filtration ι m} (h : ℱ ≤ 𝒢) (P : Measure Ω) :
    ℱ.ambientNullAugmentation P ≤ 𝒢.ambientNullAugmentation P :=
  (ℱ.ambientNullAugmentation_le_iff _ P
    (fun i _ hs hP ↦ 𝒢.measurableSet_ambientNullAugmentation_of_null P i hs hP)).mpr
      (h.trans (𝒢.le_ambientNullAugmentation P))

/-- Applying original-space null augmentation twice adds no information. -/
@[simp]
theorem ambientNullAugmentation_idem (ℱ : Filtration ι m) (P : Measure Ω) :
    (ℱ.ambientNullAugmentation P).ambientNullAugmentation P = ℱ.ambientNullAugmentation P :=
  ambientNullAugmentation_eq_self _ P
    (fun i _ hs hP ↦ ℱ.measurableSet_ambientNullAugmentation_of_null P i hs hP)

/-- If the only ambient-measurable null event is empty, every filtration is unchanged.
This applies, for example, to a finite discrete space charging every point. -/
theorem ambientNullAugmentation_eq_self_of_forall_measure_eq_zero_eq_empty
    (ℱ : Filtration ι m) (P : Measure Ω)
    (hP : ∀ s : Set Ω, MeasurableSet s → P s = 0 → s = ∅) :
    ℱ.ambientNullAugmentation P = ℱ := by
  apply ℱ.ambientNullAugmentation_eq_self P
  intro i s hs hnull
  exact (hP s hs hnull).symm ▸ @MeasurableSet.empty Ω (ℱ i)

/-- Equivalent measures give the same original-space augmentation. -/
theorem ambientNullAugmentation_eq_of_absolutelyContinuous (ℱ : Filtration ι m)
    {P Q : Measure Ω} (hPQ : P ≪ Q) (hQP : Q ≪ P) :
    ℱ.ambientNullAugmentation P = ℱ.ambientNullAugmentation Q := by
  apply Filtration.ext
  funext i
  simp only [ambientNullAugmentation_apply,
    ℱ.nullAugment_apply_eq_of_absolutelyContinuous hPQ hQP]

/-- Completing after original-space null augmentation gives the same completed filtration
as completing directly. Equality is stated at each time to keep the ambient spaces explicit.
Use this lemma by rewriting: simplification expands the filtration evaluations first. -/
theorem nullAugment_ambientNullAugmentation_apply (ℱ : Filtration ι m) (P : Measure Ω) (i : ι) :
    (ℱ.ambientNullAugmentation P).nullAugment P i = ℱ.nullAugment P i := by
  apply le_antisymm
  · intro s hs
    obtain ⟨t, ht, hst⟩ :=
      ((ℱ.ambientNullAugmentation P).measurableSet_nullAugment_iff P i s).mp hs
    obtain ⟨_, u, hu, htu⟩ := (ℱ.measurableSet_ambientNullAugmentation_iff P i t).mp ht
    exact (ℱ.measurableSet_nullAugment_iff P i s).mpr ⟨u, hu, hst.trans htu⟩
  · intro s hs
    obtain ⟨t, ht, hst⟩ := (ℱ.measurableSet_nullAugment_iff P i s).mp hs
    exact ((ℱ.ambientNullAugmentation P).measurableSet_nullAugment_iff P i s).mpr
      ⟨t, ℱ.le_ambientNullAugmentation P i t ht, hst⟩

end MeasureTheory.Filtration

namespace MeasureTheory.Filtration

/-- On a first-countable linearly ordered time axis with the order topology, original-space null
augmentation commutes with right-continuation. Neither density nor absence of a maximum time is
required. -/
theorem rightCont_ambientNullAugmentation {Ω ι : Type*} {m : MeasurableSpace Ω}
    [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [FirstCountableTopology ι]
    (ℱ : Filtration ι m) (P : Measure Ω) :
    (ℱ.ambientNullAugmentation P).rightCont = ℱ.rightCont.ambientNullAugmentation P := by
  classical
  apply Filtration.ext
  funext i
  by_cases hne : (nhdsWithin i (Set.Ioi i)).NeBot
  · apply le_antisymm
    · intro A hA
      have hmA : MeasurableSet A := (ℱ.ambientNullAugmentation P).rightCont.le i A hA
      have hglb : IsGLB (Set.Ioi i) i := ⟨fun _ hx ↦ hx.le, fun b hb ↦ le_of_not_gt fun hib ↦ by
        obtain ⟨c, hc⟩ := hne.nonempty_of_mem (Ioo_mem_nhdsGT hib)
        exact hc.2.not_ge (hb hc.1)⟩
      obtain ⟨u, -, hu, hlim, -⟩ := hglb.exists_seq_strictAnti_tendsto_of_notMem
        (Set.notMem_Ioi.mpr le_rfl) (hne.nonempty_of_mem self_mem_nhdsWithin)
      have hAn (n : ℕ) : ∃ B, MeasurableSet[ℱ (u n)] B ∧ A =ᵐ[P] B :=
        ((ℱ.measurableSet_ambientNullAugmentation_iff P (u n) A).mp
          ((ℱ.ambientNullAugmentation P).rightCont_le_of_lt (hu n) A hA)).2
      choose B hB hAB using hAn
      refine (ℱ.rightCont.measurableSet_ambientNullAugmentation_iff P i A).mpr
        ⟨hmA, Filter.limsup B Filter.atTop, ?_,
          (MeasureTheory.limsup_ae_eq_of_forall_ae_eq B fun n ↦ (hAB n).symm).symm⟩
      rw [ℱ.rightCont_eq_of_neBot_nhdsGT i]
      simp only [MeasurableSpace.measurableSet_iInf]
      intro j hij
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hlim.eventually (gt_mem_nhds hij))
      have htail : Filter.limsup B Filter.atTop =
          Filter.limsup (fun n ↦ if N ≤ n then B n else ∅) Filter.atTop :=
        Filter.limsup_congr ((Filter.eventually_ge_atTop N).mono fun n hn ↦ by simp [hn])
      rw [htail]
      let : MeasurableSpace Ω := ℱ j
      exact MeasurableSet.measurableSet_limsup fun n ↦ by
        split_ifs with hn
        · exact ℱ.mono (hN n hn).le _ (hB n)
        · exact MeasurableSet.empty
    · intro A hA
      obtain ⟨hmA, B, hB, hAB⟩ :=
        (ℱ.rightCont.measurableSet_ambientNullAugmentation_iff P i A).mp hA
      rw [(ℱ.ambientNullAugmentation P).rightCont_eq_of_neBot_nhdsGT i]
      simp only [MeasurableSpace.measurableSet_iInf]
      intro j hij
      exact (ℱ.measurableSet_ambientNullAugmentation_iff P j A).mpr
        ⟨hmA, B, ℱ.rightCont_le_of_lt hij B hB, hAB⟩
  · have hbot : nhdsWithin i (Set.Ioi i) = ⊥ := Filter.not_neBot.mp hne
    simp [(ℱ.ambientNullAugmentation P).rightCont_eq_of_nhdsGT_eq_bot hbot,
      ℱ.rightCont_eq_of_nhdsGT_eq_bot hbot]

end MeasureTheory.Filtration

namespace MeasureTheory.Adapted

variable {Ω ι : Type*} {m : MeasurableSpace Ω} [Preorder ι]
  {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
  {ℱ : Filtration ι m} {P : Measure Ω} {X Y : (i : ι) → Ω → β i}

/-- An ambient-measurable version of an adapted process is adapted on the original-space
null augmentation. Equality is required only at each fixed time, not simultaneously. -/
theorem ambientNullAugmentation_of_ae_eq (hX : Adapted ℱ X)
    (hY : ∀ i, Measurable (Y i)) (hXY : ∀ i, X i =ᵐ[P] Y i) :
    Adapted (ℱ.ambientNullAugmentation P) Y := by
  intro i s hs
  exact (ℱ.measurableSet_ambientNullAugmentation_iff P i _).mpr
    ⟨hY i hs, X i ⁻¹' s, hX i hs, (hXY i).symm.preimage s⟩

end MeasureTheory.Adapted
