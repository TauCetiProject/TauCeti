/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Group.Pointwise
public import Mathlib.MeasureTheory.Measure.AddContent
public import TauCeti.MeasureTheory.Measure.AddContent
public import TauCeti.MeasureTheory.SetAlgebra

/-!
# Contents on the null-measurable sets of a measure

A finitely additive set function vanishing on the null sets of a measure `μ` cannot distinguish
sets that agree `μ`-almost everywhere (`MeasureTheory.addContent_congr_ae`). Since every
`μ`-null-measurable set agrees almost everywhere with a measurable set, a content `m` on the
measurable sets which vanishes on `μ`-null sets therefore extends uniquely to a content on the
`μ`-null-measurable sets, that is, on the measurable sets of the completion of `μ`, still
vanishing on `μ`-null sets. Its value at a null-measurable set `s` is `m (toMeasurable μ s)`
(`MeasureTheory.AddContent.completion`).

Conversely, a content on a ring of sets restricts to any smaller family of sets
(`MeasureTheory.AddContent.trim`), and restriction to the measurable sets is inverse to the
extension. So contents on the measurable sets and on the null-measurable sets that vanish on null
sets are the same thing. This is the form in which finitely additive set functions on the Borel
sets of a group and on the measurable sets of its completed Haar measure correspond, for instance
to describe the positive functionals on `L∞`. The extension preserves nonnegativity and
invariance under a group action preserving `μ`.

## Main definitions

* `MeasureTheory.AddContent.trim`: the restriction of a content to a smaller family of sets.
* `MeasureTheory.AddContent.completion`: the extension of a content on the measurable sets,
  vanishing on `μ`-null sets, to the `μ`-null-measurable sets.

## Main results

* `MeasureTheory.addContent_congr_ae`: a content vanishing on null sets takes the same value at
  sets that agree almost everywhere.
* `MeasureTheory.AddContent.completion_apply`: the extension takes the value `m t` at a
  null-measurable set that agrees almost everywhere with a measurable set `t`.
* `MeasureTheory.AddContent.completion_unique`, `MeasureTheory.AddContent.completion_trim`: the
  extension is the only content on the null-measurable sets extending `m` and vanishing on null
  sets.
* `MeasureTheory.AddContent.forall_completion_smul_eq_iff`: the extension is invariant under a
  measure-preserving group action exactly when `m` is invariant on measurable sets.
-/

public section

noncomputable section

open Set Filter

open scoped ENNReal Pointwise

namespace MeasureTheory

variable {α G : Type*} {C : Set (Set α)} {s t : Set α}

/-- A content on a ring of sets which vanishes on the null sets of `C` takes the same value at
two sets of `C` that agree almost everywhere. -/
theorem addContent_congr_ae {F : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α] {ν : F}
    [AddCommMonoid G] {m : AddContent G C} (hC : IsSetRing C) (hm : ∀ u ∈ C, ν u = 0 → m u = 0)
    (hs : s ∈ C) (ht : t ∈ C) (hst : s =ᵐ[ν] t) : m s = m t := by
  -- Removing a null difference `u \ v` from `u` does not change the content.
  have key {u v : Set α} (hu : u ∈ C) (hv : v ∈ C) (huv : ν (u \ v) = 0) : m u = m (u ∩ v) := by
    conv_lhs => rw [← inter_union_sdiff u v]
    rw [addContent_union hC (hC.inter_mem hu hv) (hC.sdiff_mem hu hv) disjoint_sdiff_inter.symm,
      hm _ (hC.sdiff_mem hu hv) huv, add_zero]
  rw [key hs ht (ae_eq_set.1 hst).1, key ht hs (ae_eq_set.1 hst).2, inter_comm]

section Trim

variable [AddCommMonoid G] {D : Set (Set α)}

namespace AddContent

/-- The restriction of a content on `C` to a smaller family `D ⊆ C` of sets, with the same
values. -/
def trim (m : AddContent G C) (h : D ⊆ C) : AddContent G D where
  toFun := m
  empty' := addContent_empty
  sUnion' _ hI hdis hU := addContent_sUnion (hI.trans h) hdis (h hU)

@[simp]
theorem trim_apply (m : AddContent G C) (h : D ⊆ C) (s : Set α) : m.trim h s = m s :=
  (rfl)

end AddContent

end Trim

variable [MeasurableSpace α] {μ : Measure α}

/-- The null-measurable sets of a measure form a ring of sets. -/
theorem isSetRing_nullMeasurableSet : IsSetRing {s : Set α | NullMeasurableSet s μ} where
  empty_mem := nullMeasurableSet_empty
  union_mem _ _ hs ht := NullMeasurableSet.union hs ht
  sdiff_mem _ _ hs ht := NullMeasurableSet.diff hs ht

/-- Measurable sets are null-measurable, as a family of sets. -/
theorem setOf_measurableSet_subset_setOf_nullMeasurableSet :
    {s : Set α | MeasurableSet s} ⊆ {s : Set α | NullMeasurableSet s μ} :=
  fun _ hs => MeasurableSet.nullMeasurableSet hs

namespace AddContent

section Completion

variable [AddCommMonoid G] (m : AddContent G {s : Set α | MeasurableSet s})
  {hm : ∀ s, MeasurableSet s → μ s = 0 → m s = 0}

variable (μ) in
open Classical in
/-- The extension of a content `m` on the measurable sets, vanishing on `μ`-null sets, to the
`μ`-null-measurable sets. Its value at a null-measurable set `s` is the value of `m` at the
measurable set `toMeasurable μ s`, which agrees with `s` almost everywhere. Its value at a set
that is not null-measurable is zero. -/
def completion (hm : ∀ s, MeasurableSet s → μ s = 0 → m s = 0) :
    AddContent G {s : Set α | NullMeasurableSet s μ} :=
  isSetRing_nullMeasurableSet.addContent_of_union
    (fun s => if NullMeasurableSet s μ then m (toMeasurable μ s) else 0)
    (by
      rw [ite_eq_left nullMeasurableSet_empty]
      exact hm _ (measurableSet_toMeasurable μ ∅) (by rw [measure_toMeasurable, measure_empty]))
    fun {s t} hs ht hst => by
      rw [mem_ofPred_eq] at hs ht
      have hs' := measurableSet_toMeasurable μ s
      have ht' := measurableSet_toMeasurable μ t
      -- `toMeasurable μ s` and `toMeasurable μ t` meet in a null set, as `s` and `t` are disjoint.
      have hnull : μ (toMeasurable μ s ∩ toMeasurable μ t) = 0 := by
        rw [measure_congr (hs.toMeasurable_ae_eq.inter ht.toMeasurable_ae_eq), hst.inter_eq,
          measure_empty]
      simp only [hs.union ht, hs, ht, ↓reduceIte]
      rw [addContent_congr_ae isSetRing_measurableSet hm (measurableSet_toMeasurable μ _)
          (hs'.union ht') ((hs.union ht).toMeasurable_ae_eq.trans
            (hs.toMeasurable_ae_eq.union ht.toMeasurable_ae_eq).symm),
        ← addContent_union_add_inter isSetRing_measurableSet hs' ht', hm _ (hs'.inter ht') hnull,
        add_zero]

/-- The extension of `m` takes the value `m t` at a null-measurable set that agrees almost
everywhere with a measurable set `t`. -/
theorem completion_apply (hs : NullMeasurableSet s μ) (ht : MeasurableSet t) (hst : s =ᵐ[μ] t) :
    m.completion μ hm s = m t := by
  unfold completion
  exact (ite_eq_left hs).trans <| addContent_congr_ae isSetRing_measurableSet hm
    (measurableSet_toMeasurable μ s) ht (hs.toMeasurable_ae_eq.trans hst)

/-- The extension of `m` agrees with `m` on measurable sets. -/
@[simp]
theorem completion_apply_of_measurableSet (hs : MeasurableSet s) : m.completion μ hm s = m s :=
  m.completion_apply hs.nullMeasurableSet hs EventuallyEq.rfl

/-- The extension of `m` is zero at a set that is not null-measurable, by convention. -/
theorem completion_of_not_nullMeasurableSet (hs : ¬NullMeasurableSet s μ) :
    m.completion μ hm s = 0 := by
  unfold completion
  exact ite_eq_right hs

/-- The extension of `m` vanishes on `μ`-null sets. -/
theorem completion_of_measure_eq_zero (hs : μ s = 0) : m.completion μ hm s = 0 := by
  rw [m.completion_apply (.of_null hs) MeasurableSet.empty (ae_eq_empty.2 hs), addContent_empty]

/-- The extension of `m` is the only content on the null-measurable sets that agrees with `m` on
measurable sets and vanishes on null sets. -/
theorem completion_unique {m' : AddContent G {s : Set α | NullMeasurableSet s μ}}
    (hm' : ∀ s, μ s = 0 → m' s = 0) (h : ∀ s, MeasurableSet s → m' s = m s)
    (hs : NullMeasurableSet s μ) : m.completion μ hm s = m' s := by
  have ht := measurableSet_toMeasurable μ s
  rw [m.completion_apply hs ht hs.toMeasurable_ae_eq.symm, ← h _ ht]
  exact addContent_congr_ae isSetRing_nullMeasurableSet (fun u _ hu => hm' u hu)
    ht.nullMeasurableSet hs hs.toMeasurable_ae_eq

/-- A content on the null-measurable sets vanishing on null sets, and by convention on sets that
are not null-measurable, is the extension of its restriction to the measurable sets. -/
theorem completion_trim (m' : AddContent G {s : Set α | NullMeasurableSet s μ})
    (hm' : ∀ s, μ s = 0 → m' s = 0) (h' : ∀ s, ¬NullMeasurableSet s μ → m' s = 0) :
    (m'.trim setOf_measurableSet_subset_setOf_nullMeasurableSet).completion μ
      (fun s _ hs => (m'.trim_apply _ s).trans (hm' s hs)) = m' := by
  ext s
  by_cases hs : NullMeasurableSet s μ
  · exact completion_unique _ hm' (fun _ _ => (trim_apply ..).symm) hs
  · rw [completion_of_not_nullMeasurableSet _ hs, h' s hs]

/-- The extension of a nonnegative content is nonnegative. -/
theorem completion_nonneg [Preorder G] (h₀ : ∀ s, MeasurableSet s → 0 ≤ m s) (s : Set α) :
    0 ≤ m.completion μ hm s := by
  by_cases hs : NullMeasurableSet s μ
  · have ht := measurableSet_toMeasurable μ s
    rw [m.completion_apply hs ht hs.toMeasurable_ae_eq.symm]
    exact h₀ _ ht
  · rw [m.completion_of_not_nullMeasurableSet hs]

variable {Γ : Type*} [Group Γ] [MulAction Γ α] [MeasurableConstSMul Γ α]
  [SMulInvariantMeasure Γ α μ]

/-- If `m` is invariant on measurable sets under a group action preserving `μ`, then its
extension is invariant on all sets. -/
theorem completion_smul (h : ∀ (g : Γ) s, MeasurableSet s → m (g • s) = m s) (g : Γ)
    (s : Set α) : m.completion μ hm (g • s) = m.completion μ hm s := by
  by_cases hs : NullMeasurableSet s μ
  · have ht := measurableSet_toMeasurable μ s
    rw [m.completion_apply hs ht hs.toMeasurable_ae_eq.symm,
      m.completion_apply (hs.smul g) (ht.const_smul g)
        ((smul_set_ae_eq g).2 hs.toMeasurable_ae_eq.symm), h g _ ht]
  · -- Translating back by `g⁻¹` shows that `g • s` is not null-measurable either.
    have hgs : ¬NullMeasurableSet (g • s) μ := fun hgs => hs (by simpa using hgs.smul g⁻¹)
    rw [m.completion_of_not_nullMeasurableSet hs, m.completion_of_not_nullMeasurableSet hgs]

/-- The extension of `m` is invariant under a group action preserving `μ` exactly when `m` is
invariant on measurable sets. -/
theorem forall_completion_smul_eq_iff :
    (∀ (g : Γ) s, m.completion μ hm (g • s) = m.completion μ hm s) ↔
      ∀ (g : Γ) s, MeasurableSet s → m (g • s) = m s := by
  refine ⟨fun h g s hs => ?_, completion_smul m⟩
  simpa [hs, hs.const_smul g] using h g s

end Completion

end AddContent

end MeasureTheory
