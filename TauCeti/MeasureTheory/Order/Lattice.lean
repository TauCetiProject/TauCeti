/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Order.Lattice

/-!
# Measurability of nonempty finite infima and pointwise suprema

Mathlib's `Mathlib.MeasureTheory.Order.Lattice` proves `Finset.measurable_sup'` for a nonempty
finite supremum in the function lattice `δ → α`, but omits the dual nonempty finite infimum lemma
`Finset.measurable_inf'` and the general pointwise forms `fun x ↦ s.inf' hs fun i ↦ f i x` and
`fun x ↦ s.sup' hs fun i ↦ f i x`. This file supplies those `fun_prop` lemmas under the minimal
semilattice measurability classes `MeasurableInf₂` and `MeasurableSup₂`.
-/

public section

open MeasureTheory

namespace Finset

section SemilatticeInf

variable {δ α : Type*} [MeasurableSpace δ] [MeasurableSpace α] [SemilatticeInf α]
  [MeasurableInf₂ α]

/-- The infimum of a nonempty finite family of measurable functions is measurable. -/
@[fun_prop]
theorem measurable_inf' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → δ → α}
    (hf : ∀ i ∈ s, Measurable (f i)) : Measurable (s.inf' hs f) :=
  s.inf'_induction hs _ (fun _f hf _g hg ↦ hf.inf hg) fun i hi ↦ hf i hi

/-- The pointwise infimum of a nonempty finite family of measurable functions is measurable. -/
@[fun_prop]
theorem measurable_inf'' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → δ → α}
    (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun x ↦ s.inf' hs fun i ↦ f i x := by
  convert s.measurable_inf' hs hf using 1
  ext x
  simp

end SemilatticeInf

section SemilatticeSup

variable {δ α : Type*} [MeasurableSpace δ] [MeasurableSpace α] [SemilatticeSup α]
  [MeasurableSup₂ α]

/-- The pointwise supremum of a nonempty finite family of measurable functions is measurable. -/
@[fun_prop]
theorem measurable_sup'' {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → δ → α}
    (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable fun x ↦ s.sup' hs fun i ↦ f i x := by
  convert s.measurable_sup' hs hf using 1
  ext x
  simp

end SemilatticeSup

end Finset
