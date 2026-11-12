/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

/-!
# Measurability and nullity tested on finite-measure sets

For a measure `μ`, a set is locally measurable if its intersection with every measurable set of
finite measure is measurable. These sets form `Measure.locallyMeasurableSpace μ`. A set is
`Measure.IsLocallyNull` if all such intersections are null.

For a σ-finite measure these conventions agree with ordinary measurability and nullity, by
using a countable finite-measure exhaustion. Consequently local measurability of functions and
equality outside a locally null set agree with measurability and almost-everywhere equality.
No topology or completeness of the measure is needed.

For a Borel measure these are the locally Borel and locally null conventions used by Bekka,
de la Harpe and Valette, *Kazhdan's Property (T)*, Section C.5. The comparison explains why their
local conventions agree with the global conventions for σ-finite Haar measures.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [m : MeasurableSpace α] (μ : Measure α)

/-- The σ-algebra of sets whose intersections with measurable sets of finite `μ`-measure are
measurable. For a Borel measure these are the locally Borel sets. -/
@[instance_reducible]
def locallyMeasurableSpace : MeasurableSpace α where
  MeasurableSet' s := ∀ t, MeasurableSet t → μ t < ∞ → MeasurableSet (s ∩ t)
  measurableSet_empty := by simp
  measurableSet_compl s hs t ht hμt := by
    convert ht.diff (hs t ht hμt) using 1
    grind
  measurableSet_iUnion s hs t ht hμt := by
    simpa only [iUnion_inter] using MeasurableSet.iUnion (fun n ↦ hs n t ht hμt)

/-- Membership in the locally measurable σ-algebra is tested on measurable finite-measure sets. -/
theorem measurableSet_locallyMeasurableSpace_iff {s : Set α} :
    MeasurableSet[μ.locallyMeasurableSpace] s ↔
      ∀ t, MeasurableSet t → μ t < ∞ → MeasurableSet (s ∩ t) :=
  Iff.rfl

/-- Every measurable set is locally measurable. -/
theorem le_locallyMeasurableSpace : m ≤ μ.locallyMeasurableSpace :=
  fun _ hs _ ht _ ↦ hs.inter ht

/-- For a σ-finite measure, local measurability is ordinary measurability. -/
@[simp]
theorem locallyMeasurableSpace_eq [SigmaFinite μ] : μ.locallyMeasurableSpace = m := by
  refine le_antisymm (fun s hs ↦ ?_) μ.le_locallyMeasurableSpace
  have hs' := (μ.measurableSet_locallyMeasurableSpace_iff).1 hs
  have h := MeasurableSet.iUnion (fun n ↦
    hs' (spanningSets μ n) (measurableSet_spanningSets μ n) (measure_spanningSets_lt_top μ n))
  simpa only [← inter_iUnion, iUnion_spanningSets, inter_univ] using h

/-- For a σ-finite measure, a function whose measurable preimages are locally measurable is
measurable. This applies in particular to the locally measurable functions of a Borel measure. -/
theorem measurable_locallyMeasurableSpace_iff [MeasurableSpace β] [SigmaFinite μ] {f : α → β} :
    @Measurable α β μ.locallyMeasurableSpace _ f ↔ Measurable f := by
  rw [μ.locallyMeasurableSpace_eq]

/-- A set is locally null if its intersection with every measurable set of finite `μ`-measure
has measure zero. Unlike nullity, this condition need not imply global nullity without
σ-finiteness. -/
def IsLocallyNull (s : Set α) : Prop :=
  ∀ t, MeasurableSet t → μ t < ∞ → μ (s ∩ t) = 0

/-- The defining finite-measure tests for local nullity. -/
theorem isLocallyNull_iff_forall {s : Set α} :
    μ.IsLocallyNull s ↔ ∀ t, MeasurableSet t → μ t < ∞ → μ (s ∩ t) = 0 :=
  Iff.rfl

/-- Every null set is locally null, with no measurability assumption on the set. -/
theorem isLocallyNull_of_measure_eq_zero {s : Set α} (hs : μ s = 0) : μ.IsLocallyNull s :=
  fun t _ _ ↦ measure_inter_null_of_null_left t hs

/-- For a σ-finite measure, locally null sets are exactly null sets, even when the set is not
measurable. -/
@[simp]
theorem isLocallyNull_iff [SigmaFinite μ] {s : Set α} : μ.IsLocallyNull s ↔ μ s = 0 := by
  refine ⟨fun hs ↦ ?_, μ.isLocallyNull_of_measure_eq_zero⟩
  apply (isCountablySpanning_spanningSets μ).null_of_forall_inter_null
  rintro _ ⟨n, rfl⟩
  exact hs _ (measurableSet_spanningSets μ n) (measure_spanningSets_lt_top μ n)

/-- For a σ-finite measure, equality outside a locally null set is precisely almost-everywhere
equality. Thus the local and global quotient conventions identify the same functions. -/
theorem isLocallyNull_setOf_ne_iff [SigmaFinite μ] {f g : α → β} :
    μ.IsLocallyNull {x | f x ≠ g x} ↔ f =ᵐ[μ] g := by
  rw [μ.isLocallyNull_iff, Filter.EventuallyEq, ae_iff]

end MeasureTheory.Measure
