/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Common

/-!
# Fibers of a finite monotone value family

This file packages the finite bookkeeping for repeated approximation-number
values.  A value label is one value occurring in a finite family; its fiber
has canonical first and last indices and a canonical enumeration by a finite
type.

Nothing here mentions an operator: the statements are about an arbitrary
`a : Fin n → ℝ`, and the approximation-number reading is supplied by the
caller.  The spectral-selection argument uses the fibers to group equal
approximation numbers into bands, and `finiteValueFiber_card_le_span` is the
counting step that bounds a band by the index interval it occupies.

## Provenance

* Original module: authored for the Davis--Kahan tan-2-theta development, then
  moved here once its dependencies were measured: the statements are about an
  arbitrary `a : Fin n → ℝ` and use nothing but Mathlib.
* Extraction class: **moved and renamespaced.**  Statements and proofs are
  unchanged; only the enclosing namespace and the import list moved.
* Original authors / copyright: Jon Crall, OpenAI GPT-5.6 Thinking;
  Copyright (c) 2026 Kitware, Inc.; Apache 2.0.
* Spectra influence: **none.**
-/

public section

namespace TauCeti
namespace ApproximationNumber

noncomputable section

/-- The finite set of values occurring in `a`. -/
noncomputable def finiteValueSet {n : ℕ} (a : Fin n → ℝ) : Finset ℝ :=
  Finset.univ.image a

/-- A value occurring in the finite family. -/
abbrev FiniteValueLabel {n : ℕ} (a : Fin n → ℝ) :=
  {value : ℝ // value ∈ finiteValueSet a}

/-- The label of a particular index. -/
noncomputable def finiteValueLabel {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    FiniteValueLabel a := by
  refine ⟨a i, Finset.mem_image.mpr ?_⟩
  exact ⟨i, Finset.mem_univ i, rfl⟩

/-- The fiber of one occurring value. -/
noncomputable def finiteValueFiber {n : ℕ} (a : Fin n → ℝ)
    (label : FiniteValueLabel a) : Finset (Fin n) :=
  Finset.univ.filter fun i => a i = label.1

/-- Membership in a fiber is exactly carrying that fiber's value. -/
@[simp]
theorem mem_finiteValueFiber {n : ℕ} (a : Fin n → ℝ)
    (label : FiniteValueLabel a) (i : Fin n) :
    i ∈ finiteValueFiber a label ↔ a i = label.1 := by
  simp [finiteValueFiber]

/-- Every value label has a nonempty fiber. -/
theorem finiteValueFiber_nonempty {n : ℕ} (a : Fin n → ℝ)
    (label : FiniteValueLabel a) : (finiteValueFiber a label).Nonempty := by
  classical
  rcases Finset.mem_image.mp label.2 with ⟨i, _, hi⟩
  refine ⟨i, ?_⟩
  rw [mem_finiteValueFiber]
  exact hi

/-- First index carrying a value. -/
noncomputable def finiteValueFirst {n : ℕ} (a : Fin n → ℝ)
    (label : FiniteValueLabel a) : Fin n :=
  (finiteValueFiber a label).min' (finiteValueFiber_nonempty a label)

/-- Last index carrying a value. -/
noncomputable def finiteValueLast {n : ℕ} (a : Fin n → ℝ)
    (label : FiniteValueLabel a) : Fin n :=
  (finiteValueFiber a label).max' (finiteValueFiber_nonempty a label)

/-- The first fiber index carries the label's value.

Not `@[simp]`: the left-hand side `a (finiteValueFirst a label)` has the family `a`
as head symbol, so simp would try it on every application of every function. -/
theorem finiteValueFirst_value {n : ℕ} (a : Fin n → ℝ)
    (label : FiniteValueLabel a) : a (finiteValueFirst a label) = label.1 := by
  exact (mem_finiteValueFiber a label (finiteValueFirst a label)).mp
    (Finset.min'_mem _ _)

/-- The last fiber index carries the label's value.

Not `@[simp]`, for the same reason as `finiteValueFirst_value`. -/
theorem finiteValueLast_value {n : ℕ} (a : Fin n → ℝ)
    (label : FiniteValueLabel a) : a (finiteValueLast a label) = label.1 := by
  exact (mem_finiteValueFiber a label (finiteValueLast a label)).mp
    (Finset.max'_mem _ _)

/-- The first fiber index is at most every member. -/
theorem finiteValueFirst_le {n : ℕ} (a : Fin n → ℝ)
    (label : FiniteValueLabel a) {i : Fin n}
    (hi : i ∈ finiteValueFiber a label) :
    finiteValueFirst a label ≤ i := by
  exact Finset.min'_le _ _ hi

/-- Every member is at most the last fiber index. -/
theorem le_finiteValueLast {n : ℕ} (a : Fin n → ℝ)
    (label : FiniteValueLabel a) {i : Fin n}
    (hi : i ∈ finiteValueFiber a label) :
    i ≤ finiteValueLast a label := by
  exact Finset.le_max' _ _ hi

/-- Canonical position of an index inside its value fiber. -/
noncomputable def finiteValueFiberIndex {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    Fin (finiteValueFiber a (finiteValueLabel a i)).card :=
  (finiteValueFiber a (finiteValueLabel a i)).equivFin
    -- Unfolding `finiteValueFiber` here beats `mem_finiteValueFiber` to the goal and leaves
    -- a raw `setOf` membership that no longer discharges itself; let the `simp` lemma fire.
    ⟨i, by simp [finiteValueLabel]⟩

/-- The fiber cardinality is bounded by the length of the interval between its
first and last indices. -/
theorem finiteValueFiber_card_le_span {n : ℕ} (a : Fin n → ℝ)
    (label : FiniteValueLabel a) :
    (finiteValueFiber a label).card ≤
      (finiteValueLast a label).val + 1 - (finiteValueFirst a label).val := by
  classical
  let p := (finiteValueFirst a label).val
  let q := (finiteValueLast a label).val
  let e : {i // i ∈ finiteValueFiber a label} →
      Fin (q + 1 - p) := fun i => by
    have hpi : p ≤ i.1.val := by
      exact_mod_cast finiteValueFirst_le a label i.2
    have hiq : i.1.val ≤ q := by
      exact_mod_cast le_finiteValueLast a label i.2
    refine ⟨i.1.val - p, ?_⟩
    omega
  have he : Function.Injective e := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    have hpi : p ≤ i.1.val := by
      exact_mod_cast finiteValueFirst_le a label i.2
    have hpj : p ≤ j.1.val := by
      exact_mod_cast finiteValueFirst_le a label j.2
    have hval := congrArg Fin.val hij
    change i.1.val - p = j.1.val - p at hval
    omega
  have hcard := Fintype.card_le_of_injective e he
  simpa only [Fintype.card_coe, Fintype.card_fin, p, q] using hcard

end

end ApproximationNumber
end TauCeti
