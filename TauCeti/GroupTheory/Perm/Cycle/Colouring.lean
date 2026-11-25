/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import TauCeti.GroupTheory.Perm.Basic
public import TauCeti.GroupTheory.Perm.Partition
import Mathlib.Data.Set.Card

/-!
# Colours used by invariant colourings

A colouring fixed by a permutation `π` is the same as a colouring of the cycles of `π`
(`TauCeti.invariantColouringEquiv`). Passing from the cycle labels to the colouring of the
points does not change the set of colours used, and hence the number of colours used. Counting
the colourings of the cycles, a permutation of a finite type fixes `#σ ^ c` colourings with `#σ`
colours, where `c` is its number of cycles, fixed points included.

## Main results

* `Equiv.Perm.range_invariantColouringEquiv`: the colouring and its cycle labels have the same
  set of colours.
* `Equiv.Perm.card_image_invariantColouringEquiv`: on a finite type, the colouring uses as many
  colours as its cycle labels.
* `Equiv.Perm.card_invariantColouring`: there are `#σ ^ c` colourings fixed by `π`, where `c` is
  the number of parts of the full cycle type of `π`.
-/

public section

open TauCeti

namespace Equiv.Perm

variable {α σ : Type*}

/-- Passing from cycle labels to a colouring preserves the set of colours used. -/
@[simp] theorem range_invariantColouringEquiv (π : Perm α)
    (g : Quotient (SameCycle.setoid π) → σ) :
    Set.range (invariantColouringEquiv π g : α → σ) = Set.range g := by
  have h : (invariantColouringEquiv π g : α → σ) = g ∘ Quotient.mk _ :=
    funext (invariantColouringEquiv_apply_coe π g)
  rw [h, Quotient.mk_surjective.range_comp]

/-- The induced colouring and its cycle labels use the same number of colours.
See `Equiv.Perm.range_invariantColouringEquiv` for equality of the colour sets. -/
@[simp] theorem card_image_invariantColouringEquiv [Fintype α] [DecidableEq σ] (π : Perm α)
    (g : Quotient (SameCycle.setoid π) → σ) :
    (Finset.univ.image (invariantColouringEquiv π g).val).card = Nat.card (Set.range g) := by
  rw [← π.range_invariantColouringEquiv, ← Set.image_univ, ← Finset.coe_univ,
    ← Finset.coe_image, Nat.card_coe_set_eq, Set.ncard_coe_finset]

/-- **The number of colourings fixed by a permutation**: there are `Nat.card σ ^ c` colourings with
values in `σ` fixed by `π`, where `c = Multiset.card π.fullCycleType` is the number of cycles of
`π`, fixed points included. -/
theorem card_invariantColouring [Fintype α] [DecidableEq α] (π : Perm α) :
    Nat.card {f : α → σ // f ∘ π = f} = Nat.card σ ^ Multiset.card π.fullCycleType := by
  rw [← Nat.card_congr (invariantColouringEquiv π), Nat.card_fun, card_fullCycleType]

end Equiv.Perm
