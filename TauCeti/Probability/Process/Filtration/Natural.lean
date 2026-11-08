/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import TauCeti.Probability.Process.Filtration.NullAugmentation

/-!
# Natural filtrations, deterministic translation and future increments

The natural filtration is the smallest filtration to which a process is adapted.
Adding a deterministic function to a real-valued process leaves this filtration unchanged:
the original process is recovered by subtracting the same function. No continuity of the
deterministic function, or probability law of the process, is needed. The past up to a fixed
date together with the whole future increment process determines every later observation
(`MeasureTheory.Filtration.natural_le_sup_comap_shift`).

Consequently the usual augmented natural filtrations also agree after deterministic
translation and an equivalent change of measure. The null sets adjoined here are those of
the ambient measure, not just those already visible at a given time.
-/

public section

noncomputable section

open TopologicalSpace
open scoped NNReal

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

end MeasureTheory.Filtration
