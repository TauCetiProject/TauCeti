/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import TauCeti.MeasureTheory.MeasurableSpace.Option

/-!
# The Borel structure on the one-point compactification

This file equips the Alexandroff one-point compactification `OnePoint X` with the disjoint-union
measurable structure inherited from `Option X` (`Option.instMeasurableSpace`), records
measurability of the canonical inclusion `(↑) : X → OnePoint X`, `{∞}`, and `OnePoint.elim`, and
establishes `MeasurableSingletonClass (OnePoint X)`, `OpensMeasurableSpace (OnePoint X)`, and
`BorelSpace (OnePoint X)` from the corresponding instances on `X` without separation assumptions on
`X`. This provides the Borel measure theory on compactifications such as the projective line
`OnePoint K`.
-/

public section

open MeasureTheory Set Topology

namespace OnePoint

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The measurable structure on `OnePoint X`, inherited from `Option X`. -/
instance instMeasurableSpace : MeasurableSpace (OnePoint X) :=
  inferInstanceAs (MeasurableSpace (Option X))

/-- The canonical inclusion `X → OnePoint X` is a measurable embedding. -/
theorem measurableEmbedding_coe : MeasurableEmbedding ((↑) : X → OnePoint X) :=
  Option.measurableEmbedding_some

/-- The canonical inclusion `X → OnePoint X` is measurable. -/
@[fun_prop]
theorem measurable_coe : Measurable ((↑) : X → OnePoint X) :=
  Option.measurable_some

/-- The point at infinity is a measurable singleton in `OnePoint X`. -/
@[simp, measurability]
theorem measurableSet_infty : MeasurableSet ({∞} : Set (OnePoint X)) :=
  Option.measurableSet_none

/-- Eliminating on `OnePoint X` with a constant value at `∞` and a measurable branch on `X` is
measurable. -/
@[fun_prop]
theorem measurable_elim (y : Y) {f : X → Y} (hf : Measurable f) :
    Measurable fun x : OnePoint X ↦ x.elim y f :=
  Option.measurable_elim y hf

/-- A map out of `OnePoint X` is measurable if and only if its restriction to `X` is measurable. -/
@[simp]
theorem measurable_iff {f : OnePoint X → Y} :
    Measurable f ↔ Measurable fun x : X ↦ f x :=
  Option.measurable_iff

omit [MeasurableSpace X] in
private theorem eq_image_preimage_union_inter_infty (s : Set (OnePoint X)) :
    s = ((↑) : X → OnePoint X) '' (((↑) : X → OnePoint X) ⁻¹' s) ∪ (s ∩ {∞}) := by
  ext z
  induction z using OnePoint.rec <;> simp

/-- Singletons in `OnePoint X` are measurable when singletons in `X` are measurable. -/
instance instMeasurableSingletonClass [MeasurableSingletonClass X] :
    MeasurableSingletonClass (OnePoint X) where
  measurableSet_singleton z := by
    induction z using OnePoint.rec with
    | infty => exact measurableSet_infty
    | coe x =>
      simpa using measurableEmbedding_coe.measurableSet_image.mpr (measurableSet_singleton x)

/-- Open sets in `OnePoint X` are measurable when open sets in `X` are measurable. -/
instance instOpensMeasurableSpace [TopologicalSpace X] [OpensMeasurableSpace X] :
    OpensMeasurableSpace (OnePoint X) where
  borel_le := by
    refine MeasurableSpace.generateFrom_le fun s hs ↦ ?_
    rw [eq_image_preimage_union_inter_infty s]
    have hpre : MeasurableSet (((↑) : X → OnePoint X) ⁻¹' s) :=
      (isOpenEmbedding_coe.continuous.isOpen_preimage s hs).measurableSet
    have himg : MeasurableSet (((↑) : X → OnePoint X) '' (((↑) : X → OnePoint X) ⁻¹' s)) :=
      measurableEmbedding_coe.measurableSet_image.mpr hpre
    by_cases hinf : ∞ ∈ s
    · have hinter : s ∩ {∞} = {∞} := inter_eq_right.mpr (singleton_subset_iff.mpr hinf)
      rw [hinter]
      exact himg.union measurableSet_infty
    · have hinter : s ∩ {∞} = ∅ := inter_singleton_eq_empty.mpr hinf
      rw [hinter, union_empty]
      exact himg

/-- The disjoint-union measurable structure on `OnePoint X` agrees with the Borel σ-algebra
whenever `X` is a Borel space. -/
instance instBorelSpace [TopologicalSpace X] [BorelSpace X] : BorelSpace (OnePoint X) where
  measurable_eq := by
    refine le_antisymm (fun s hs ↦ ?_) OpensMeasurableSpace.borel_le
    have hpre : MeasurableSet (((↑) : X → OnePoint X) ⁻¹' s) := measurable_coe hs
    let : MeasurableSpace (OnePoint X) := borel (OnePoint X)
    have : BorelSpace (OnePoint X) := ⟨rfl⟩
    have hcoe : MeasurableEmbedding ((↑) : X → OnePoint X) :=
      isOpenEmbedding_coe.measurableEmbedding
    have himg : MeasurableSet (((↑) : X → OnePoint X) '' (((↑) : X → OnePoint X) ⁻¹' s)) :=
      hcoe.measurableSet_image.mpr hpre
    rw [eq_image_preimage_union_inter_infty s]
    by_cases hinf : ∞ ∈ s
    · have hinter : s ∩ {∞} = {∞} := inter_eq_right.mpr (singleton_subset_iff.mpr hinf)
      rw [hinter]
      exact himg.union isClosed_infty.measurableSet
    · have hinter : s ∩ {∞} = ∅ := inter_singleton_eq_empty.mpr hinf
      rw [hinter, union_empty]
      exact himg

end OnePoint
