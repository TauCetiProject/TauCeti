/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Northcott

import Mathlib.Data.Set.Finite.Lattice

/-!
# Sums and projections of Northcott functions on products

A function `f : α → β` is Northcott (Mathlib's `Northcott`) when each sublevel set
`{a | f a ≤ b}` is finite. If `f : α → β` and `g : γ → β` are Northcott functions into a linearly
ordered additive group, then so is `(a, c) ↦ f a + g c` on `α × γ` (`Northcott.prod_add`).
When `β` is finite, the first projection `Prod.fst : α × β → α` (for `α` locally finite at the
bottom, in particular `α = ℕ`) and any composition `p ↦ f p.1` with a Northcott function `f` are
also Northcott (`Northcott.fst`, `Northcott.comp_fst`).

This is the counting fact behind the spectrum of a sum `A ⊗ 1 + 1 ⊗ B` of two operators with
discrete spectra: if each factor has only finitely many eigenvalues below every bound, then only
finitely many pairs of eigenvalues have sum below every bound.
-/

public section

namespace Northcott

variable {α β γ : Type*}

/-- If `f` is Northcott and `β` is finite, then `p ↦ f p.1` is Northcott on `α × β`. -/
theorem comp_fst [Finite β] [LE γ] (f : α → γ) [Northcott f] :
    Northcott fun p : α × β ↦ f p.1 where
  finite_le b := ((finite_le (h := f) b).prod Set.finite_univ).subset fun _ hp ↦
    ⟨hp, Set.mem_univ _⟩

/-- On a product `α × β` with `α` locally finite at the bottom and `β` finite, the first
projection `Prod.fst` is Northcott. In particular, `Prod.fst : ℕ × β → ℕ` is Northcott. -/
instance fst [Preorder α] [LocallyFiniteOrderBot α] [Finite β] :
    Northcott (Prod.fst : α × β → α) where
  finite_le b := ((Set.finite_Iic b).prod Set.finite_univ).subset fun _ hp ↦
    ⟨hp, Set.mem_univ _⟩

/-- If `f` and `g` are Northcott functions into a linearly ordered additive group, then so is
`(a, c) ↦ f a + g c`: for every `b` only finitely many pairs satisfy `f a + g c ≤ b`. -/
theorem prod_add [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] (f : α → β)
    (g : γ → β) [Northcott f] [Northcott g] : Northcott fun p : α × γ ↦ f p.1 + g p.2 where
  finite_le b := by
    rcases isEmpty_or_nonempty α with hα | ⟨⟨a₀⟩⟩
    · exact Set.finite_empty.subset fun p _ ↦ isEmptyElim p.1
    rcases isEmpty_or_nonempty γ with hγ | ⟨⟨c₀⟩⟩
    · exact Set.finite_empty.subset fun p _ ↦ isEmptyElim p.2
    -- Each factor is bounded below by its minimum, which bounds the other factor above.
    obtain ⟨a₁, -, ha₁⟩ := exists_min_image f Set.univ ⟨a₀, trivial⟩
    obtain ⟨c₁, -, hc₁⟩ := exists_min_image g Set.univ ⟨c₀, trivial⟩
    refine ((finite_le (h := f) (b - g c₁)).prod (finite_le (h := g) (b - f a₁))).subset ?_
    rintro ⟨a, c⟩ (h : f a + g c ≤ b)
    have ha := ha₁ a trivial
    have hc := hc₁ c trivial
    exact ⟨le_sub_iff_add_le.2 ((add_le_add_right hc (f a)).trans h),
      le_sub_iff_add_le'.2 ((add_le_add_left ha (g c)).trans h)⟩

end Northcott
