/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import TauCeti.Probability.Process.Filtration.Natural
import TauCeti.Probability.Independence.CondExp
import TauCeti.Probability.Independence.Limit

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
  classical
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let ℱ := Filtration.natural W hmeas
  obtain ⟨u, -, hu, hlim⟩ := exists_seq_strictAnti_tendsto s
  have hfinite (I : Finset ℝ≥0) :
      Indep (MeasurableSpace.comap (fun ω (v : I) => W (s + v) ω - W s ω) inferInstance)
        (ℱ.rightCont s) P := by
    apply Indep.symm
    refine indep_comap_of_ae_tendsto (X := fun n ω (v : I) =>
        W (u n + v) ω - W (u n) ω) (ℱ.rightCont.le s)
      (fun n => (measurable_pi_iff.2 fun (v : I) =>
        (hmeas (u n + v)).measurable.sub (hmeas (u n)).measurable).aemeasurable)
      (measurable_pi_iff.2 fun (v : I) =>
        (hmeas (s + v)).measurable.sub (hmeas s).measurable).aemeasurable ?_ ?_
    · intro n
      have hfull : Indep (MeasurableSpace.comap
          (fun ω v => W (u n + v) ω - W (u n) ω) inferInstance) (ℱ (u n)) P := by
        rw [Filtration.natural_eq_comap]
        exact (IndepFun_iff_Indep ..).1 (hW.indepFun_shift (u n))
      refine (indep_of_indep_of_le_right
        (indep_of_indep_of_le_left hfull ?_) (ℱ.rightCont_le_of_lt (hu n))).symm
      simp only [MeasurableSpace.comap_process_pi]
      exact iSup_le fun v => le_iSup (fun a : ℝ≥0 =>
        MeasurableSpace.comap (fun ω => W (u n + a) ω - W (u n) ω) inferInstance) v.val
    · filter_upwards [hW.cont] with ω hω
      exact tendsto_pi_nhds.2 fun v =>
        (hω.continuousAt.tendsto.comp (hlim.add_const v.val)).sub
          (hω.continuousAt.tendsto.comp hlim)
  rw [MeasurableSpace.comap_process_pi, iSup_eq_iSup_finset]
  apply indep_iSup_of_monotone
  · intro I
    simpa only [MeasurableSpace.comap_process_pi, iSup_subtype'] using hfinite I
  · intro I
    exact iSup₂_le fun v _ => ((hmeas (s + v)).measurable.sub (hmeas s).measurable).comap_le
  · exact ℱ.rightCont.le s
  · exact fun I J hIJ => iSup_le_iSup_of_subset hIJ

/-- Every event of the raw right-continuous natural Brownian filtration has a representative
in the original natural sigma-algebra at the same time. -/
theorem rightCont_natural_le_nullAugment (hW : IsBrownianReal W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) (s : ℝ≥0) :
    (Filtration.natural W hmeas).rightCont s ≤
      (Filtration.natural W hmeas).nullAugment P s := by
  classical
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  let ℱ := Filtration.natural W hmeas
  let mFuture := MeasurableSpace.comap (fun ω v => W (s + v) ω - W s ω) inferInstance
  let : MeasurableSpace Ω := mΩ
  have hfuture : mFuture ≤ mΩ :=
    (measurable_pi_iff.2 fun v => (hmeas (s + v)).measurable.sub (hmeas s).measurable).comap_le
  have hle : ℱ.rightCont s ≤ ℱ s ⊔ mFuture :=
    (ℱ.rightCont_le_of_lt (lt_add_one s)).trans
      (Filtration.natural_le_sup_comap_shift W hmeas s (s + 1))
  intro A hA
  rw [Filtration.measurableSet_nullAugment_iff]
  have hAi : Integrable (A.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator (ℱ.rightCont.le s A hA)
  have hcond := (hW.indep_shift_rightCont_natural hmeas s).symm
    |>.condExp_eq_of_le_of_stronglyMeasurable_sup (ℱ.le_rightCont s) (ℱ.rightCont.le s)
      hfuture ((stronglyMeasurable_const.indicator hA).mono hle) hAi
  have heq : P[A.indicator (fun _ => (1 : ℝ)) | ℱ s] =ᵐ[P]
      A.indicator (fun _ => (1 : ℝ)) :=
    hcond.symm.trans (Filter.EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable (ℱ.rightCont.le s)
        (stronglyMeasurable_const.indicator hA) hAi))
  refine ⟨{ω | 1 / 2 < P[A.indicator (fun _ => (1 : ℝ)) | ℱ s] ω},
    measurableSet_lt measurable_const stronglyMeasurable_condExp.measurable, ?_⟩
  filter_upwards [heq] with ω hω
  simp only [hω]
  by_cases hωA : ω ∈ A <;> norm_num [hωA]

/-- The null-augmented natural filtration of Brownian motion is right-continuous. This uses
the completed ambient space of `Filtration.nullAugment`; no completeness of `P` is assumed. -/
theorem isRightContinuous_nullAugment_natural (hW : IsBrownianReal W P)
    (hmeas : ∀ t, StronglyMeasurable (W t)) :
    ((Filtration.natural W hmeas).nullAugment P).IsRightContinuous := by
  constructor
  intro s
  rw [Filtration.rightCont_nullAugment_apply]
  intro A hA
  rw [Filtration.measurableSet_nullAugment_iff] at hA ⊢
  obtain ⟨B, hB, hAB⟩ := hA
  obtain ⟨C, hC, hBC⟩ := (Filtration.measurableSet_nullAugment_iff _ P s B).mp
    (hW.rightCont_natural_le_nullAugment hmeas s B hB)
  exact ⟨C, hC, hAB.trans hBC⟩

end ProbabilityTheory.IsBrownianReal
