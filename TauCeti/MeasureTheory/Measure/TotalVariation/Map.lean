/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Trim
public import TauCeti.MeasureTheory.Measure.TotalVariation.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Contraction and invariance of total variation under measurable maps

Pushing two measures forward along a measurable map cannot increase their largest eventwise excess
`⨆ (A) (_ : MeasurableSet A), μ A - ν A`, because every measurable event in the codomain pulls back
to a measurable event in the domain with the same pushed-forward masses. Summing the two
one-sided excesses gives the **data processing inequality** for extended and real-valued total
variation distance (`MeasureTheory.etvDist_map_le`, `MeasureTheory.tvDist_map_le`), as well as
contraction under restriction to a sub-σ-algebra (`MeasureTheory.etvDist_trim_le`,
`MeasureTheory.tvDist_trim_le`).

All contraction statements hold in full generality without finiteness assumptions on `μ` or `ν`,
and require only almost-everywhere measurability of `f` with respect to each measure
(`AEMeasurable f μ` and `AEMeasurable f ν`). Almost-everywhere measurability cannot be dropped:
when `f` is not `μ`-almost-everywhere measurable and `μ ≠ 0`, `Measure.map` returns a unit Dirac
mass, which increases excess and `etvDist` when `μ Set.univ < 1` (comparing with `0`), and increases
`tvDist` from `0` to `1` when `μ` is infinite. Under `AEMeasurable f μ` and `AEMeasurable f ν`,
finiteness of `μ.map f` and `ν.map f` is equivalent to finiteness of `μ` and `ν`, so both finite
and infinite cases are preserved.

When `f` is a measurable embedding, every measurable event `A` in the domain is the preimage of
its measurable image `f '' A`, so eventwise excess, `etvDist`, and `tvDist` are preserved with
equality (`MeasurableEmbedding.iSup_measure_map_sub`, `MeasurableEmbedding.etvDist_map`,
`MeasurableEmbedding.tvDist_map`), and in particular under measurable equivalences.

## Main statements

* `MeasureTheory.iSup_measure_map_sub_le`, `MeasureTheory.iSup_measure_map_sub_le_of_aemeasurable`:
  eventwise excess contracts under measurable and almost-everywhere measurable pushforwards;
* `MeasureTheory.etvDist_map_le`, `MeasureTheory.tvDist_map_le`: data processing inequalities for
  extended and real total variation distance;
* `MeasureTheory.iSup_measure_trim_sub_le`, `MeasureTheory.etvDist_trim_le`,
  `MeasureTheory.tvDist_trim_le`: contraction under restriction to a sub-σ-algebra;
* `MeasurableEmbedding.iSup_measure_map_sub`, `MeasurableEmbedding.etvDist_map`,
  `MeasurableEmbedding.tvDist_map`: invariance under measurable embeddings;
* `MeasurableEquiv.iSup_measure_map_sub`, `MeasurableEquiv.etvDist_map`,
  `MeasurableEquiv.tvDist_map`: invariance under measurable equivalences.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

section Map

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Pushing two measures forward along a map that is almost everywhere measurable for each measure
contracts their largest eventwise excess. No finiteness assumption on `μ` or `ν` is needed. -/
theorem iSup_measure_map_sub_le_of_aemeasurable {μ ν : Measure α} {f : α → β}
    (hμ : AEMeasurable f μ) (hν : AEMeasurable f ν) :
    (⨆ (B : Set β) (_ : MeasurableSet B), μ.map f B - ν.map f B) ≤
      ⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A := by
  have hf : AEMeasurable f (μ + ν) := hμ.add_measure hν
  obtain ⟨hμg, hνg⟩ := ae_add_measure_iff.mp hf.ae_eq_mk
  rw [Measure.map_congr hμg, Measure.map_congr hνg]
  refine iSup₂_le fun B hB => ?_
  rw [Measure.map_apply hf.measurable_mk hB, Measure.map_apply hf.measurable_mk hB]
  exact le_iSup₂ (f := fun (A : Set α) (_ : MeasurableSet A) => μ A - ν A)
    (hf.mk f ⁻¹' B) (hf.measurable_mk hB)

/-- **Data processing inequality for eventwise excess.** Pushing two measures forward along a
measurable map contracts their largest eventwise excess. -/
theorem iSup_measure_map_sub_le (μ ν : Measure α) {f : α → β} (hf : Measurable f) :
    (⨆ (B : Set β) (_ : MeasurableSet B), μ.map f B - ν.map f B) ≤
      ⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A :=
  iSup_measure_map_sub_le_of_aemeasurable hf.aemeasurable hf.aemeasurable

/-- Pushing two measures forward along a map that is almost everywhere measurable for each measure
contracts their extended total variation distance. -/
theorem etvDist_map_le_of_aemeasurable {μ ν : Measure α} {f : α → β}
    (hμ : AEMeasurable f μ) (hν : AEMeasurable f ν) :
    etvDist (μ.map f) (ν.map f) ≤ etvDist μ ν := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν
  · obtain ⟨_, _⟩ := h
    rw [etvDist_eq_iSup_sub_add_iSup_sub, etvDist_eq_iSup_sub_add_iSup_sub]
    exact add_le_add (iSup_measure_map_sub_le_of_aemeasurable hμ hν)
      (iSup_measure_map_sub_le_of_aemeasurable hν hμ)
  · simp [etvDist_of_not_isFiniteMeasure h]

/-- **Data processing inequality** for extended total variation distance and measurable maps. -/
theorem etvDist_map_le (μ ν : Measure α) {f : α → β} (hf : Measurable f) :
    etvDist (μ.map f) (ν.map f) ≤ etvDist μ ν :=
  etvDist_map_le_of_aemeasurable hf.aemeasurable hf.aemeasurable

/-- Pushing two measures forward along a map that is almost everywhere measurable for each measure
contracts their real-valued total variation distance. -/
theorem tvDist_map_le_of_aemeasurable {μ ν : Measure α} {f : α → β}
    (hμ : AEMeasurable f μ) (hν : AEMeasurable f ν) :
    tvDist (μ.map f) (ν.map f) ≤ tvDist μ ν := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν
  · obtain ⟨_, _⟩ := h
    exact ENNReal.toReal_mono (etvDist_ne_top μ ν) (etvDist_map_le_of_aemeasurable hμ hν)
  · rw [tvDist_of_not_isFiniteMeasure h, tvDist_of_not_isFiniteMeasure]
    rwa [Measure.isFiniteMeasure_map_iff hμ, Measure.isFiniteMeasure_map_iff hν]

/-- **Data processing inequality** for real-valued total variation distance and measurable maps. -/
theorem tvDist_map_le (μ ν : Measure α) {f : α → β} (hf : Measurable f) :
    tvDist (μ.map f) (ν.map f) ≤ tvDist μ ν :=
  tvDist_map_le_of_aemeasurable hf.aemeasurable hf.aemeasurable

end Map

section Trim

variable {α : Type*} {m m₀ : MeasurableSpace α}

/-- Restricting two measures to a sub-σ-algebra contracts their largest eventwise excess. -/
theorem iSup_measure_trim_sub_le (μ ν : Measure[m₀] α) (hm : m ≤ m₀) :
    (⨆ (A : Set α) (_ : MeasurableSet[m] A), μ.trim hm A - ν.trim hm A) ≤
      ⨆ (A : Set α) (_ : MeasurableSet[m₀] A), μ A - ν A := by
  simp_rw [trim_eq_map]
  exact @iSup_measure_map_sub_le α α m₀ m μ ν id (measurable_id'' hm)

/-- **Data processing inequality** for extended total variation distance and sub-σ-algebras. -/
theorem etvDist_trim_le (μ ν : Measure[m₀] α) (hm : m ≤ m₀) :
    etvDist (μ.trim hm) (ν.trim hm) ≤ etvDist μ ν := by
  simp_rw [trim_eq_map]
  exact @etvDist_map_le α α m₀ m μ ν id (measurable_id'' hm)

/-- **Data processing inequality** for real-valued total variation distance and sub-σ-algebras. -/
theorem tvDist_trim_le (μ ν : Measure[m₀] α) (hm : m ≤ m₀) :
    tvDist (μ.trim hm) (ν.trim hm) ≤ tvDist μ ν := by
  simp_rw [trim_eq_map]
  exact @tvDist_map_le α α m₀ m μ ν id (measurable_id'' hm)

end Trim

end MeasureTheory

namespace MeasurableEmbedding

open MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}

/-- Pushing two measures forward along a measurable embedding preserves their largest eventwise
excess. -/
theorem iSup_measure_map_sub (hf : MeasurableEmbedding f) (μ ν : Measure α) :
    (⨆ (B : Set β) (_ : MeasurableSet B), μ.map f B - ν.map f B) =
      ⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A := by
  refine le_antisymm (iSup_measure_map_sub_le μ ν hf.measurable) (iSup₂_le fun A hA => ?_)
  simpa only [hf.map_apply, hf.injective.preimage_image] using
    le_iSup₂ (f := fun (B : Set β) (_ : MeasurableSet B) => μ.map f B - ν.map f B)
      (f '' A) (hf.measurableSet_image' hA)

/-- Pushing two measures forward along a measurable embedding preserves their extended total
variation distance. -/
theorem etvDist_map (hf : MeasurableEmbedding f) (μ ν : Measure α) :
    etvDist (μ.map f) (ν.map f) = etvDist μ ν := by
  by_cases h : IsFiniteMeasure μ ∧ IsFiniteMeasure ν
  · obtain ⟨_, _⟩ := h
    rw [etvDist_eq_iSup_sub_add_iSup_sub, etvDist_eq_iSup_sub_add_iSup_sub,
      hf.iSup_measure_map_sub, hf.iSup_measure_map_sub]
  · rw [etvDist_of_not_isFiniteMeasure h, etvDist_of_not_isFiniteMeasure]
    rwa [Measure.isFiniteMeasure_map_iff hf.measurable.aemeasurable,
      Measure.isFiniteMeasure_map_iff hf.measurable.aemeasurable]

/-- Pushing two measures forward along a measurable embedding preserves their real-valued total
variation distance. -/
theorem tvDist_map (hf : MeasurableEmbedding f) (μ ν : Measure α) :
    tvDist (μ.map f) (ν.map f) = tvDist μ ν := by
  simp only [tvDist, hf.etvDist_map]

end MeasurableEmbedding

namespace MeasurableEquiv

open MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Pushing two measures forward along a measurable equivalence preserves their largest eventwise
excess. -/
theorem iSup_measure_map_sub (e : α ≃ᵐ β) (μ ν : Measure α) :
    (⨆ (B : Set β) (_ : MeasurableSet B), μ.map e B - ν.map e B) =
      ⨆ (A : Set α) (_ : MeasurableSet A), μ A - ν A :=
  e.measurableEmbedding.iSup_measure_map_sub μ ν

/-- Pushing two measures forward along a measurable equivalence preserves their extended total
variation distance. -/
@[simp]
theorem etvDist_map (e : α ≃ᵐ β) (μ ν : Measure α) :
    etvDist (μ.map e) (ν.map e) = etvDist μ ν :=
  e.measurableEmbedding.etvDist_map μ ν

/-- Pushing two measures forward along a measurable equivalence preserves their real-valued total
variation distance. -/
@[simp]
theorem tvDist_map (e : α ≃ᵐ β) (μ ν : Measure α) :
    tvDist (μ.map e) (ν.map e) = tvDist μ ν :=
  e.measurableEmbedding.tvDist_map μ ν

end MeasurableEquiv
