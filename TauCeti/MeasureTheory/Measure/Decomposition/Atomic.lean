/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Atomic/diffuse decomposition of an s-finite measure

For an s-finite measure with measurable singletons, the points of positive singleton mass form a
countable, hence measurable, set. Restricting the measure to this set preserves every point mass;
restricting it to the complement gives a measure with zero mass on every singleton.

## Main definitions

* `MeasureTheory.Measure.positiveSingletons`: the set of points with nonzero singleton measure.
* `MeasureTheory.Measure.atomicPart`: the restriction of a measure to `positiveSingletons`.
* `MeasureTheory.Measure.diffusePart`: the restriction of a measure to `(positiveSingletons μ)ᶜ`.

## Main results

* `MeasureTheory.Measure.countable_positiveSingletons`: an s-finite measure has at most countably
  many positive-mass singletons.
* `MeasureTheory.Measure.atomicPart_apply_singleton`,
  `MeasureTheory.Measure.diffusePart_apply_singleton`: singleton evaluations of the two parts.
* `MeasureTheory.Measure.atomicPart_eq_sum_dirac`: the atomic part as a sum of weighted Dirac
  measures.
* `MeasureTheory.Measure.atomicPart_add_diffusePart`: `atomicPart μ + diffusePart μ = μ`.
-/

public section

noncomputable section

open MeasureTheory Set

namespace MeasureTheory.Measure

variable {X : Type*} [MeasurableSpace X]

/-- The set of points carrying positive singleton mass. -/
def positiveSingletons (μ : Measure X) : Set X := {x | μ {x} ≠ 0}

/-- Membership in `positiveSingletons` means that the singleton has nonzero mass. -/
@[simp]
theorem mem_positiveSingletons_iff (μ : Measure X) (x : X) :
    x ∈ positiveSingletons μ ↔ μ {x} ≠ 0 := Iff.rfl

/-- The restriction of a measure to all of its positive-mass singleton points. -/
def atomicPart (μ : Measure X) : Measure X := μ.restrict (positiveSingletons μ)

/-- The atomic part is the restriction to the positive-mass singleton points. -/
theorem atomicPart_def (μ : Measure X) :
    atomicPart μ = μ.restrict (positiveSingletons μ) := (rfl)

/-- Evaluate the atomic part on a measurable set. -/
@[simp]
theorem atomicPart_apply (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    atomicPart μ s = μ (s ∩ positiveSingletons μ) := by
  rw [atomicPart, restrict_apply hs]

/-- The complementary restriction to the points with zero singleton mass. -/
def diffusePart (μ : Measure X) : Measure X := μ.restrict (positiveSingletons μ)ᶜ

/-- The diffuse part is the restriction to the zero-mass singleton points. -/
theorem diffusePart_def (μ : Measure X) :
    diffusePart μ = μ.restrict (positiveSingletons μ)ᶜ := (rfl)

/-- Evaluate the diffuse part on a measurable set. -/
@[simp]
theorem diffusePart_apply (μ : Measure X) (s : Set X) (hs : MeasurableSet s) :
    diffusePart μ s = μ (s ∩ (positiveSingletons μ)ᶜ) := by
  rw [diffusePart, restrict_apply hs]

/-- Restricting to the positive-mass points does not increase a measure. -/
theorem atomicPart_le (μ : Measure X) : atomicPart μ ≤ μ := by
  rw [atomicPart]
  exact Measure.restrict_le_self

/-- Restricting to the zero-mass points does not increase a measure. -/
theorem diffusePart_le (μ : Measure X) : diffusePart μ ≤ μ := by
  rw [diffusePart]
  exact Measure.restrict_le_self

/-- The atomic part is absolutely continuous with respect to the original measure. -/
theorem atomicPart_absolutelyContinuous (μ : Measure X) : atomicPart μ ≪ μ :=
  atomicPart_le μ |>.absolutelyContinuous

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

variable [MeasurableSingletonClass X]

/-- An s-finite measure has at most countably many positive-mass singleton sets. -/
theorem countable_positiveSingletons (μ : Measure X) [SFinite μ] :
    (positiveSingletons μ).Countable := by
  simpa [positiveSingletons, pos_iff_ne_zero] using
    (Measure.countable_meas_level_set_pos (μ := μ) (g := id) measurable_id)

/-- The positive-mass singleton points form a measurable set for an s-finite measure. -/
theorem measurableSet_positiveSingletons (μ : Measure X) [SFinite μ] :
    MeasurableSet (positiveSingletons μ) :=
  (countable_positiveSingletons μ).measurableSet

omit [MeasurableSingletonClass X] in
/-- The atomic part preserves the mass of every singleton. -/
theorem atomicPart_apply_singleton (μ : Measure X) (x : X) :
    atomicPart μ {x} = μ {x} := by
  by_cases hx : μ {x} = 0
  · exact le_antisymm (restrict_apply_le _ _) (by simp [hx])
  · exact restrict_eq_self μ (singleton_subset_iff.2 hx)

/-- The atomic part is the sum of the point masses at its supporting points. -/
theorem atomicPart_eq_sum_dirac (μ : Measure X) :
    atomicPart μ = Measure.sum fun x : positiveSingletons μ ↦
      μ {(x : X)} • Measure.dirac (x : X) := by
  ext s hs
  rw [atomicPart, restrict_apply hs, Measure.sum_apply _ hs]
  set A := s ∩ positiveSingletons μ with hA
  have hsum : ∑' x : positiveSingletons μ, (μ {(x : X)} • Measure.dirac (x : X)) s =
      ∑' x : X, A.indicator (fun y ↦ μ {y}) x := by
    simp only [smul_apply, Measure.dirac_apply' _ hs, smul_eq_mul]
    rw [tsum_subtype (positiveSingletons μ) fun x ↦ μ {x} * s.indicator 1 x]
    congr 1
    ext x
    by_cases hxs : x ∈ s <;> by_cases hxP : x ∈ positiveSingletons μ <;>
      simp [Set.indicator, hA, hxs, hxP]
  rw [hsum]
  by_cases hc : A.Countable
  · have := hc.to_subtype
    rw [← tsum_subtype A fun y ↦ μ {y}, ← measure_iUnion
      (fun x y hxy ↦ disjoint_singleton.2 (fun h ↦ hxy (Subtype.ext h)))
      (fun x ↦ measurableSet_singleton (x : X))]
    congr 1
    ext y
    simp
  · have htop : ∑' x : X, A.indicator (fun y ↦ μ {y}) x = ⊤ := by
      by_contra h
      refine hc ((Summable.countable_support_ennreal h).mono fun y hy ↦ ?_)
      simp only [Function.mem_support, Set.indicator_apply_ne_zero]
      exact ⟨hy, hy.2⟩
    have hμ : μ A = ⊤ := by
      by_contra h
      have hU : (⋃ x : A, ({(x : X)} : Set X)) = A := by
        ext y
        simp
      refine hc (Set.countable_coe_iff.1 (Set.countable_univ_iff.1 ?_))
      refine (countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top μ
        (As := fun x : A ↦ ({(x : X)} : Set X)) (fun x ↦ measurableSet_singleton (x : X))
        (fun x y hxy ↦ disjoint_singleton.2 (fun h ↦ hxy (Subtype.ext h)))
        (by rw [hU]; exact h)).mono ?_
      intro x _
      exact pos_iff_ne_zero.2 x.2.2
    rw [htop, hμ]

/-- The diffuse part gives zero mass to every singleton. -/
theorem diffusePart_apply_singleton (μ : Measure X) (x : X) :
    diffusePart μ {x} = 0 := by
  rw [diffusePart, restrict_apply (measurableSet_singleton x)]
  by_cases hx : μ {x} = 0 <;> simp [hx]

/-- The atomic part vanishes on the complement of its supporting points. -/
@[simp]
theorem atomicPart_apply_compl (μ : Measure X) [SFinite μ] :
    atomicPart μ (positiveSingletons μ)ᶜ = 0 := by
  rw [atomicPart_apply μ _ (measurableSet_positiveSingletons μ).compl]
  simp

/-- The point-mass part and the diffuse remainder sum to the original s-finite measure. -/
theorem atomicPart_add_diffusePart (μ : Measure X) [SFinite μ] :
    atomicPart μ + diffusePart μ = μ := by
  rw [atomicPart, diffusePart, restrict_add_restrict_compl (measurableSet_positiveSingletons μ)]

/-- The diffuse remainder has zero mass on every singleton. -/
instance diffusePart_nullSingletonClass (μ : Measure X) :
    NullSingletonClass (diffusePart μ) :=
  ⟨diffusePart_apply_singleton μ⟩

end MeasureTheory.Measure

namespace TauCeti

open MeasureTheory.Measure

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSingletonClass X] {μ : Measure X} [SFinite μ]

omit [SFinite μ] in
/-- A measurable map sends the atomic part to the sum of the images of its point masses. -/
theorem map_atomicPart_eq_sum_dirac {T : X → Y} (hT : Measurable T) :
    (atomicPart μ).map T = Measure.sum fun x : positiveSingletons μ ↦
      μ {(x : X)} • Measure.dirac (T x) := by
  rw [atomicPart_eq_sum_dirac, Measure.map_sum hT.aemeasurable]
  simp only [Measure.map_smul _ hT.aemeasurable, Measure.map_dirac' hT]

/-- The diffuse part vanishes on the positive-mass singleton points. -/
@[simp]
theorem diffusePart_apply_positiveSingletons : diffusePart μ (positiveSingletons μ) = 0 := by
  rw [diffusePart_apply μ _ (measurableSet_positiveSingletons μ)]
  simp

end TauCeti

end
