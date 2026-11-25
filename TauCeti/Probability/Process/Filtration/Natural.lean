/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Probability.Process.Filtration.NullAugmentation
import TauCeti.Probability.Independence.CondExp

/-!
# Natural filtrations, deterministic translation and future increments

The natural filtration is the smallest filtration to which a process is adapted.
Adding a deterministic function to a real-valued process leaves this filtration unchanged:
the original process is recovered by subtracting the same function. No continuity of the
deterministic function, or probability law of the process, is needed. The past up to a fixed
date together with the whole future increment process determines every later observation
(`MeasureTheory.Filtration.natural_le_sup_comap_shift`). When that future increment process is
independent of the raw right-continuous natural past at `s`, conditioning recovers every
right-continuous past indicator up to a null set
(`MeasureTheory.Filtration.rightCont_natural_le_nullAugment_of_indep_shift`).

Consequently the usual augmented natural filtrations also agree after deterministic
translation and an equivalent change of measure. The null sets adjoined here are those of
the ambient measure, not just those already visible at a given time.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §2.7.A.
* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter I, §4, Theorem 31.
-/

public section

noncomputable section

open ProbabilityTheory TopologicalSpace
open scoped NNReal

namespace TauCeti

/-- Coordinatewise measurability makes the whole future-increment process measurable.
No probability law or path regularity is required. -/
theorem measurable_shift_sub {Ω ι E : Type*} [MeasurableSpace Ω] [Add ι]
    [MeasurableSpace E] [Sub E] [MeasurableSub₂ E] {W : ι → Ω → E}
    (hmeas : ∀ t, Measurable (W t)) (s : ι) :
    Measurable (fun ω v => W (s + v) ω - W s ω) :=
  measurable_pi_iff.2 fun v => (hmeas (s + v)).sub (hmeas s)

end TauCeti

namespace MeasureTheory.Filtration

variable {Ω ι : Type*} {m : MeasurableSpace Ω}

section Preorder

variable [Preorder ι]

/-- The natural filtration is the smallest filtration making a process adapted. -/
theorem natural_le_iff {β : ι → Type*} [∀ i, TopologicalSpace (β i)]
    [∀ i, MetrizableSpace (β i)] [∀ i, MeasurableSpace (β i)] [∀ i, BorelSpace (β i)]
    (u : (i : ι) → Ω → β i) (hu : ∀ i, StronglyMeasurable (u i)) (ℱ : Filtration ι m) :
    natural u hu ≤ ℱ ↔ Adapted ℱ u := by
  constructor
  · intro h i
    exact ((stronglyAdapted_natural hu i).mono (h i)).measurable
  · intro h i
    exact iSup₂_le fun j hji =>
      (measurable_iff_comap_le.mp (h j)).trans (ℱ.mono hji)

/-- A deterministic additive translation does not change the natural filtration. -/
theorem natural_add_deterministic (W : ι → Ω → ℝ)
    (hW : ∀ i, StronglyMeasurable (W i)) (d : ι → ℝ) :
    natural (fun i ω => W i ω + d i) (fun i => (hW i).add_const (d i)) =
      natural W hW := by
  apply le_antisymm
  · apply (natural_le_iff _ _ _).mpr
    exact fun i => (stronglyAdapted_natural hW i).measurable.add_const (d i)
  · apply (natural_le_iff _ _ _).mpr
    intro i
    have h := (stronglyAdapted_natural (fun j => (hW j).add_const (d j)) i).measurable
    simpa only [add_sub_cancel_right] using h.sub_const (d i)

/-- Adding deterministic drift and changing to an equivalent measure preserve the
null-augmented natural σ-algebra at every time. -/
theorem nullAugment_natural_add_deterministic (W : ι → Ω → ℝ)
    (hW : ∀ i, StronglyMeasurable (W i)) (d : ι → ℝ) {P Q : Measure Ω}
    (hPQ : P ≪ Q) (hQP : Q ≪ P) (i : ι) :
    (natural (fun j ω => W j ω + d j) (fun j => (hW j).add_const (d j))).nullAugment Q i =
      (natural W hW).nullAugment P i := by
  rw [natural_add_deterministic]
  exact (natural W hW).nullAugment_apply_eq_of_absolutelyContinuous hQP hPQ i

/-- Adding a measurable initial random variable `ξ` on the left preserves adaptedness once `ℱ` is
enlarged by the constant filtration `σ(ξ)`. -/
theorem _root_.MeasureTheory.Adapted.add_left_sup_comap {E : Type*} [Add E] [MeasurableSpace E]
    [MeasurableAdd₂ E] {ℱ : Filtration ι m} {W : ι → Ω → E} (hW : Adapted ℱ W) {ξ : Ω → E}
    (hξ : Measurable ξ) :
    Adapted (ℱ ⊔ const ι (.comap ξ inferInstance) hξ.comap_le) (fun t ω ↦ ξ ω + W t ω) :=
  fun t ↦ ((comap_measurable ξ).mono le_sup_right le_rfl).add ((hW t).mono le_sup_left le_rfl)

/-- `t ↦ ξ + W t` is adapted to `Filtration.natural W` enlarged by `σ(ξ)`. -/
theorem adapted_add_left_natural_sup_comap {E : Type*} [TopologicalSpace E] [MetrizableSpace E]
    [Add E] [MeasurableSpace E] [BorelSpace E] [MeasurableAdd₂ E] {W : ι → Ω → E}
    (hmeas : ∀ t, StronglyMeasurable (W t)) {ξ : Ω → E} (hξ : Measurable ξ) :
    Adapted (natural W hmeas ⊔ const ι (.comap ξ inferInstance) hξ.comap_le)
      (fun t ω ↦ ξ ω + W t ω) :=
  (stronglyAdapted_natural hmeas).adapted.add_left_sup_comap hξ

end Preorder

/-- The usual augmented natural filtrations of a process and its deterministic
translation agree under equivalent measures. This does not apply to a random drift. -/
theorem rightCont_nullAugment_natural_add_deterministic
    [PartialOrder ι]
    (W : ι → Ω → ℝ) (hW : ∀ i, StronglyMeasurable (W i)) (d : ι → ℝ)
    {P Q : Measure Ω} (hPQ : P ≪ Q) (hQP : Q ≪ P) (i : ι) :
    ((natural (fun j ω => W j ω + d j)
      (fun j => (hW j).add_const (d j))).nullAugment Q).rightCont i =
      ((natural W hW).nullAugment P).rightCont i := by
  rw [natural_add_deterministic]
  exact (natural W hW).rightCont_nullAugment_apply_eq_of_absolutelyContinuous hQP hPQ i

/-- The observations of a real process up to any date are determined by its past at `s`
and its whole path of increments after `s`. No law or path regularity is required. -/
theorem natural_le_sup_comap_shift (W : ℝ≥0 → Ω → ℝ)
    (hW : ∀ t, StronglyMeasurable (W t)) (s t : ℝ≥0) :
    natural W hW t ≤ natural W hW s ⊔
      MeasurableSpace.comap (fun ω u => W (s + u) ω - W s ω) inferInstance := by
  refine iSup₂_le fun u _ => ?_
  by_cases hus : u ≤ s
  · exact (((stronglyAdapted_natural hW u).measurable).mono
      ((natural W hW).mono hus) le_rfl).comap_le.trans le_sup_left
  · have hinc : Measurable[
        natural W hW s ⊔ MeasurableSpace.comap
          (fun ω v => W (s + v) ω - W s ω) inferInstance]
        (fun ω => W (s + (u - s)) ω - W s ω) :=
      (comap_measurable _).mono
        ((MeasurableSpace.comap_le_comap_pi
          (g := fun v ω => W (s + v) ω - W s ω) (u - s)).trans le_sup_right) le_rfl
    have hstart : Measurable[
        natural W hW s ⊔ MeasurableSpace.comap
          (fun ω v => W (s + v) ω - W s ω) inferInstance] (W s) :=
      ((stronglyAdapted_natural hW s).measurable).mono le_sup_left le_rfl
    have h := hinc.add hstart
    simp only [add_tsub_cancel_of_le (le_of_not_ge hus), Pi.add_def, sub_add_cancel] at h
    exact h.comap_le

/-- **Blumenthal inclusion for natural filtrations.** If the future increment process
`(W (s + v) - W s)_v` is independent of `(Filtration.natural W hW).rightCont s` under a probability
measure `P`, then every event of `(Filtration.natural W hW).rightCont s` agrees `P`-almost
everywhere with an event of `Filtration.natural W hW s`. -/
theorem rightCont_natural_le_nullAugment_of_indep_shift {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → ℝ} (hW : ∀ t, StronglyMeasurable (W t)) {s : ℝ≥0}
    (hindep : Indep (MeasurableSpace.comap (fun ω v => W (s + v) ω - W s ω) inferInstance)
      ((natural W hW).rightCont s) P) :
    (natural W hW).rightCont s ≤ (natural W hW).nullAugment P s := by
  classical
  let ℱ := natural W hW
  let mFuture := MeasurableSpace.comap (fun ω v => W (s + v) ω - W s ω) inferInstance
  -- Restore the ambient instance: `mFuture` is also eligible for measurable-space synthesis.
  let : MeasurableSpace Ω := m
  have hfuture : mFuture ≤ m :=
    (TauCeti.measurable_shift_sub (fun t => (hW t).measurable) s).comap_le
  have hle : ℱ.rightCont s ≤ ℱ s ⊔ mFuture :=
    (ℱ.rightCont_le_of_lt (lt_add_one s)).trans (natural_le_sup_comap_shift W hW s (s + 1))
  intro A hA
  rw [measurableSet_nullAugment_iff]
  have hAi : Integrable (A.indicator fun _ => (1 : ℝ)) P :=
    (integrable_const 1).indicator (ℱ.rightCont.le s A hA)
  have hcond := hindep.symm.condExp_eq_of_le_of_stronglyMeasurable_sup
    (ℱ.le_rightCont s) (ℱ.rightCont.le s) hfuture
    ((stronglyMeasurable_const.indicator hA).mono hle) hAi
  have heq : P[A.indicator (fun _ => (1 : ℝ)) | ℱ s] =ᵐ[P] A.indicator fun _ => (1 : ℝ) :=
    hcond.symm.trans (Filter.EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable (ℱ.rightCont.le s)
        (stronglyMeasurable_const.indicator hA) hAi))
  refine ⟨{ω | 1 / 2 < P[A.indicator (fun _ => (1 : ℝ)) | ℱ s] ω},
    measurableSet_lt measurable_const stronglyMeasurable_condExp.measurable, ?_⟩
  filter_upwards [heq] with ω hω
  simp only [hω]
  by_cases hωA : ω ∈ A <;> norm_num [hωA]

end MeasureTheory.Filtration
