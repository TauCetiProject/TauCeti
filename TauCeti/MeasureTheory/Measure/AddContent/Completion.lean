/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Action
public import Mathlib.MeasureTheory.Group.Pointwise
public import TauCeti.MeasureTheory.Measure.AddContent.Basic
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

Conversely, a content on the null-measurable sets restricts to the measurable sets
(`MeasureTheory.AddContent.map` along `id`), and the extension of this restriction recovers the
content, if it vanishes on null sets and, by convention, on sets that are not null-measurable.
So contents on the measurable sets and on the null-measurable sets that vanish on null
sets are the same thing. This is the form in which finitely additive set functions on the Borel
sets of a group and on the measurable sets of its completed Haar measure correspond, for instance
to describe the positive functionals on `L∞`. The extension preserves nonnegativity and
invariance under a group action preserving `μ`.

## Main definitions

* `MeasureTheory.AddContent.completion`: the extension of a content on the measurable sets,
  vanishing on `μ`-null sets, to the `μ`-null-measurable sets.

## Main results

* `MeasureTheory.AddContent.completion_apply`: the extension takes the value `m t` at a
  null-measurable set that agrees almost everywhere with a measurable set `t`.
* `MeasureTheory.AddContent.completion_unique`, `MeasureTheory.AddContent.completion_eq`:
  any content on the null-measurable sets extending `m` and vanishing on null sets agrees with
  the extension at every null-measurable set, and equals it if it also vanishes, by convention,
  on sets that are not null-measurable. `MeasureTheory.AddContent.completion_map_id` recovers
  such a content as the extension of its restriction to the measurable sets.
* `MeasureTheory.AddContent.forall_completion_smul_eq_iff`: the extension is invariant under a
  measure-preserving group action exactly when `m` is invariant on measurable sets.
-/

public section

noncomputable section

open Set Filter

open scoped ENNReal Pointwise

namespace MeasureTheory

variable {α G : Type*} {s t : Set α}

variable [MeasurableSpace α] {μ : Measure α}

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

open Classical in
/-- The value of the extension of `m`: `m (toMeasurable μ s)` at a null-measurable set `s`, and
zero elsewhere. -/
theorem completion_apply_eq_ite (s : Set α) :
    m.completion μ hm s = if NullMeasurableSet s μ then m (toMeasurable μ s) else 0 :=
  (rfl)

/-- The extension of `m` takes the value `m t` at a null-measurable set that agrees almost
everywhere with a measurable set `t`. -/
theorem completion_apply (hs : NullMeasurableSet s μ) (ht : MeasurableSet t) (hst : s =ᵐ[μ] t) :
    m.completion μ hm s = m t := by
  rw [completion_apply_eq_ite]
  exact (ite_eq_left hs).trans <| addContent_congr_ae isSetRing_measurableSet hm
    (measurableSet_toMeasurable μ s) ht (hs.toMeasurable_ae_eq.trans hst)

/-- The extension of `m` takes the value `m (toMeasurable μ s)` at a null-measurable set `s`. -/
theorem completion_apply_of_nullMeasurableSet (hs : NullMeasurableSet s μ) :
    m.completion μ hm s = m (toMeasurable μ s) :=
  m.completion_apply hs (measurableSet_toMeasurable μ s) hs.toMeasurable_ae_eq.symm

/-- The extension of `m` agrees with `m` on measurable sets. -/
@[simp]
theorem completion_apply_of_measurableSet (hs : MeasurableSet s) : m.completion μ hm s = m s :=
  m.completion_apply hs.nullMeasurableSet hs EventuallyEq.rfl

/-- The extension of `m` is zero at a set that is not null-measurable, by convention. -/
@[simp]
theorem completion_of_not_nullMeasurableSet (hs : ¬NullMeasurableSet s μ) :
    m.completion μ hm s = 0 := by
  rw [completion_apply_eq_ite]
  exact ite_eq_right hs

/-- The extension of `m` vanishes on `μ`-null sets. -/
@[simp]
theorem completion_of_measure_eq_zero (hs : μ s = 0) : m.completion μ hm s = 0 := by
  rw [m.completion_apply (.of_null hs) MeasurableSet.empty (ae_eq_empty.2 hs), addContent_empty]

/-- Any content on the null-measurable sets that agrees with `m` on measurable sets and vanishes
on null sets agrees with the extension of `m` at every null-measurable set. See
`completion_eq` for equality of contents, under the convention that the content vanishes on
sets that are not null-measurable. -/
theorem completion_unique {m' : AddContent G {s : Set α | NullMeasurableSet s μ}}
    (hm' : ∀ s, μ s = 0 → m' s = 0) (h : ∀ s, MeasurableSet s → m' s = m s)
    (hs : NullMeasurableSet s μ) : m.completion μ hm s = m' s := by
  have ht := measurableSet_toMeasurable μ s
  rw [m.completion_apply_of_nullMeasurableSet hs, ← h _ ht]
  exact addContent_congr_ae isSetRing_nullMeasurableSet (fun u _ hu => hm' u hu)
    ht.nullMeasurableSet hs hs.toMeasurable_ae_eq

/-- A content on the null-measurable sets that agrees with `m` on measurable sets and vanishes on
null sets, and by convention on sets that are not null-measurable, is the extension of `m`. -/
theorem completion_eq {m' : AddContent G {s : Set α | NullMeasurableSet s μ}}
    (hm' : ∀ s, μ s = 0 → m' s = 0) (h : ∀ s, MeasurableSet s → m' s = m s)
    (h' : ∀ s, ¬NullMeasurableSet s μ → m' s = 0) : m.completion μ hm = m' := by
  ext s
  by_cases hs : NullMeasurableSet s μ
  · exact m.completion_unique hm' h hs
  · rw [m.completion_of_not_nullMeasurableSet hs, h' s hs]

/-- A content on the null-measurable sets vanishing on null sets, and by convention on sets that
are not null-measurable, is the extension of its restriction to the measurable sets. -/
theorem completion_map_id (m' : AddContent G {s : Set α | NullMeasurableSet s μ})
    (hm' : ∀ s, μ s = 0 → m' s = 0) (h' : ∀ s, ¬NullMeasurableSet s μ → m' s = 0) :
    (m'.map id fun _ hu => MeasurableSet.nullMeasurableSet hu).completion μ
      (fun s _ hs => (map_apply ..).trans (hm' s hs)) = m' :=
  completion_eq _ hm' (fun _ _ => (map_apply ..).symm) h'

/-- The extension of a nonnegative content is nonnegative. -/
theorem completion_nonneg [Preorder G] (h₀ : ∀ s, MeasurableSet s → 0 ≤ m s) (s : Set α) :
    0 ≤ m.completion μ hm s := by
  by_cases hs : NullMeasurableSet s μ
  · rw [m.completion_apply_of_nullMeasurableSet hs]
    exact h₀ _ (measurableSet_toMeasurable μ s)
  · rw [m.completion_of_not_nullMeasurableSet hs]

variable {Γ : Type*} [Group Γ] [MulAction Γ α] [MeasurableConstSMul Γ α]
  [SMulInvariantMeasure Γ α μ]

/-- If `m` is invariant on measurable sets under a group action preserving `μ`, then its
extension is invariant on all sets. -/
theorem completion_smul (h : ∀ (g : Γ) s, MeasurableSet s → m (g • s) = m s) (g : Γ)
    (s : Set α) : m.completion μ hm (g • s) = m.completion μ hm s := by
  by_cases hs : NullMeasurableSet s μ
  · have ht := measurableSet_toMeasurable μ s
    rw [m.completion_apply_of_nullMeasurableSet hs,
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
