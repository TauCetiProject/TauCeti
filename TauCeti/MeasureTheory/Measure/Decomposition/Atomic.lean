/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Atomic/diffuse decomposition of an s-finite measure

For an s-finite measure with measurable singletons, the points of positive singleton mass form a
countable, hence measurable, set. Restricting the measure to this set preserves every point mass;
restricting it to the complement gives a measure with zero mass on every singleton.
-/

public section

noncomputable section

open MeasureTheory Set

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

/-- The set of points carrying positive singleton mass. -/
def positiveSingletons (μ : Measure X) : Set X := {x | μ {x} ≠ 0}

omit [MeasurableSingletonClass X] in
/-- Membership in `positiveSingletons` means that the singleton has nonzero mass. -/
@[simp]
theorem mem_positiveSingletons_iff (μ : Measure X) (x : X) :
    x ∈ positiveSingletons μ ↔ μ {x} ≠ 0 := Iff.rfl

/-- A s-finite measure has at most countably many positive-mass singleton sets. -/
theorem countable_positiveSingletons (μ : Measure X) [SFinite μ] :
    (positiveSingletons μ).Countable := by
  simpa [positiveSingletons, pos_iff_ne_zero] using
    (Measure.countable_meas_level_set_pos (μ := μ) (g := id) measurable_id)

/-- The positive-mass singleton points form a measurable set for an s-finite measure. -/
theorem measurableSet_positiveSingletons (μ : Measure X) [SFinite μ] :
    MeasurableSet (positiveSingletons μ) :=
  (countable_positiveSingletons μ).measurableSet

/-- The restriction of a measure to all of its positive-mass singleton points. -/
def atomicPart (μ : Measure X) : Measure X := μ.restrict (positiveSingletons μ)

omit [MeasurableSingletonClass X] in
/-- Evaluate the atomic part on a measurable set. -/
@[simp]
theorem atomicPart_apply (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    atomicPart μ s = μ (s ∩ positiveSingletons μ) := by
  rw [atomicPart, restrict_apply hs]

/-- The atomic part preserves the mass of every singleton. -/
theorem atomicPart_apply_singleton (μ : Measure X) (x : X) :
    atomicPart μ {x} = μ {x} := by
  rw [atomicPart, restrict_apply (measurableSet_singleton x)]
  by_cases hx : μ {x} = 0
  · have hx' : x ∉ positiveSingletons μ := by
      intro hmem
      exact ((mem_positiveSingletons_iff μ x).1 hmem) hx
    simpa [hx'] using hx.symm
  · have hx' : x ∈ positiveSingletons μ := (mem_positiveSingletons_iff μ x).2 hx
    simp [hx']

private theorem atomicPart_eq_sum_dirac_of_countable (μ : Measure X)
    [Countable (positiveSingletons μ)] :
    atomicPart μ = Measure.sum fun x : positiveSingletons μ ↦
      μ {(x : X)} • Measure.dirac (x : X) := by
  calc
    atomicPart μ = μ.restrict (positiveSingletons μ) := rfl
    _ = μ.restrict (⋃ x : positiveSingletons μ, ({(x : X)} : Set X)) := by
      congr 1
      ext y
      simp
    _ = Measure.sum fun x : positiveSingletons μ ↦ μ.restrict ({(x : X)} : Set X) :=
      Measure.restrict_iUnion
        (fun x y hxy ↦ disjoint_singleton.2 (fun h ↦ hxy (Subtype.ext h)))
        (fun x ↦ measurableSet_singleton (x : X))
    _ = Measure.sum fun x : positiveSingletons μ ↦
        μ {(x : X)} • Measure.dirac (x : X) := by
      congr 1
      funext x
      exact Measure.restrict_singleton μ (x : X)

/-- The atomic part is the sum of the point masses at its supporting points. -/
theorem atomicPart_eq_sum_dirac (μ : Measure X) [SFinite μ] :
    atomicPart μ = Measure.sum fun x : positiveSingletons μ ↦
      μ {(x : X)} • Measure.dirac (x : X) :=
  @atomicPart_eq_sum_dirac_of_countable X _ _ μ (countable_positiveSingletons μ).to_subtype

/-- The complementary restriction to the points with zero singleton mass. -/
def diffusePart (μ : Measure X) : Measure X := μ.restrict (positiveSingletons μ)ᶜ

omit [MeasurableSingletonClass X] in
/-- Evaluate the diffuse part on a measurable set. -/
@[simp]
theorem diffusePart_apply (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    diffusePart μ s = μ (s ∩ (positiveSingletons μ)ᶜ) := by
  rw [diffusePart, restrict_apply hs]

/-- The diffuse part gives zero mass to every singleton. -/
theorem diffusePart_apply_singleton (μ : Measure X) (x : X) :
    diffusePart μ {x} = 0 := by
  rw [diffusePart, restrict_apply (measurableSet_singleton x)]
  by_cases hx : x ∈ positiveSingletons μ
  · simp [hx]
  · have hzero : μ {x} = 0 := by
      by_contra hne
      exact hx ((mem_positiveSingletons_iff μ x).2 hne)
    simp [hx, hzero]

/-- The atomic part vanishes on the complement of its supporting points. -/
@[simp]
theorem atomicPart_apply_compl (μ : Measure X) [SFinite μ] :
    atomicPart μ (positiveSingletons μ)ᶜ = 0 := by
  rw [atomicPart_apply μ _ (measurableSet_positiveSingletons μ).compl]
  simp

omit [MeasurableSingletonClass X] in
/-- Restricting to the positive-mass points does not increase a measure. -/
theorem atomicPart_le (μ : Measure X) : atomicPart μ ≤ μ := by
  simpa only [atomicPart] using (Measure.restrict_le_self : μ.restrict (positiveSingletons μ) ≤ μ)

omit [MeasurableSingletonClass X] in
/-- Restricting to the zero-mass points does not increase a measure. -/
theorem diffusePart_le (μ : Measure X) : diffusePart μ ≤ μ := by
  simpa only [diffusePart] using
    (Measure.restrict_le_self : μ.restrict (positiveSingletons μ)ᶜ ≤ μ)

omit [MeasurableSingletonClass X] in
/-- The atomic part is absolutely continuous with respect to the original measure. -/
theorem atomicPart_absolutelyContinuous (μ : Measure X) : atomicPart μ ≪ μ :=
  atomicPart_le μ |>.absolutelyContinuous

omit [MeasurableSingletonClass X] in
/-- The diffuse part is absolutely continuous with respect to the original measure. -/
theorem diffusePart_absolutelyContinuous (μ : Measure X) : diffusePart μ ≪ μ :=
  diffusePart_le μ |>.absolutelyContinuous

/-- The atomic part of a finite measure is finite. -/
instance atomicPart_isFiniteMeasure (μ : Measure X) [IsFiniteMeasure μ] :
    IsFiniteMeasure (atomicPart μ) := by
  unfold atomicPart
  infer_instance

/-- The diffuse part of a finite measure is finite. -/
instance diffusePart_isFiniteMeasure (μ : Measure X) [IsFiniteMeasure μ] :
    IsFiniteMeasure (diffusePart μ) := by
  unfold diffusePart
  infer_instance

/-- The point-mass part and the diffuse remainder sum to the original s-finite measure. -/
theorem atomicPart_add_diffusePart (μ : Measure X) [SFinite μ] :
    atomicPart μ + diffusePart μ = μ := by
  rw [atomicPart, diffusePart, restrict_add_restrict_compl (measurableSet_positiveSingletons μ)]

/-- The diffuse remainder has zero mass on every singleton. -/
instance diffusePart_nullSingletonClass (μ : Measure X) :
    NullSingletonClass (diffusePart μ) :=
  ⟨diffusePart_apply_singleton μ⟩

end MeasureTheory.Measure

end
