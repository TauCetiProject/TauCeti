/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.PosPart
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.PartialSups

/-!
# Eventual positive parts along a filter

A function that is eventually nonnegative along a filter agrees eventually with its positive part
(`Filter.EventuallyLE.posPart_eq`), and if the terminal term `g i` of a family is eventually
nonnegative then the finite running supremum `partialSups (g⁺) i` agrees eventually with
`partialSups g i` (`Filter.EventuallyLE.partialSups_posPart_eq`).
-/

public section

namespace Filter.EventuallyLE

variable {α β : Type*} [Lattice β] [DivInvMonoid β] {l : Filter α} {f : α → β}

/-- A function eventually bounded below by `1` agrees eventually with its `oneLePart`. -/
@[to_additive /-- An eventually nonnegative function agrees eventually with its positive part. -/]
theorem oneLePart_eq (hf : 1 ≤ᶠ[l] f) : f⁺ᵐ =ᶠ[l] f :=
  hf.mono fun _ ↦ oneLePart_eq_self.2

/-- If `g i` is eventually bounded below by `1` along `l`, then `partialSups (g⁺ᵐ) i` agrees
eventually with `partialSups g i`. -/
@[to_additive /-- If `g i` is eventually nonnegative along `l`, then `partialSups (g⁺) i` agrees
eventually with `partialSups g i`. -/]
theorem partialSups_oneLePart_eq {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    {g : ι → α → β} {i : ι} (hg : 1 ≤ᶠ[l] g i) :
    partialSups (g⁺ᵐ) i =ᶠ[l] partialSups g i :=
  map_partialSups (⟨(·⁺ᵐ), fun _ _ ↦ oneLePart_max _ _⟩ : SupHom (α → β) (α → β)) g i ▸
    (hg.trans (.of_forall (le_partialSups g i))).oneLePart_eq

end Filter.EventuallyLE
