/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Fundamental domains of integer spans

This file records geometric properties of the standard fundamental domain associated to a basis.
Its convexity makes lattice cells preconnected, so cells crossing the boundary of a set can be
detected by their intersection with the frontier in lattice-point counting arguments.

It also records two basic facts about full lattices: such a lattice is the `ℤ`-span of a basis of
the ambient space, and membership in the pull-back `ZLattice.comap` of a lattice is membership of
the image.

## Main results

* `ZSpan.convex_fundamentalDomain`: the fundamental domain of a real basis is convex.
* `ZSpan.eq_of_sub_mem_fundamentalDomain`: two integer-span translates placing a point in the
  fundamental domain are equal.
* `ZLattice.exists_basis_span_eq`: a full lattice is the `ℤ`-span of a basis of the ambient space.
* `ZLattice.mem_comap`: `x ∈ ZLattice.comap K L e` if and only if `e x ∈ L`.
-/

public section

open Module Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}

/-- The fundamental domain of a basis is convex: it is cut out by the conditions
`b.repr x i ∈ [0, 1)`, one convex condition per coordinate. -/
theorem _root_.ZSpan.convex_fundamentalDomain (β : Basis ι ℝ E) :
    Convex ℝ (ZSpan.fundamentalDomain β) := by
  intro x hx y hy a t ha ht hat
  rw [ZSpan.mem_fundamentalDomain] at hx hy ⊢
  intro i
  simpa using convex_Ico (0 : ℝ) 1 (hx i) (hy i) ha ht hat

/-- Two vectors in the integer span that translate the same point into the fundamental domain
in subtraction form are equal. -/
theorem _root_.ZSpan.eq_of_sub_mem_fundamentalDomain [Finite ι] (β : Basis ι ℝ E)
    {x w₁ w₂ : E} (hw₁ : w₁ ∈ Submodule.span ℤ (Set.range β))
    (hw₂ : w₂ ∈ Submodule.span ℤ (Set.range β))
    (h₁ : x - w₁ ∈ ZSpan.fundamentalDomain β)
    (h₂ : x - w₂ ∈ ZSpan.fundamentalDomain β) : w₁ = w₂ := by
  have hn₁ : -w₁ ∈ Submodule.span ℤ (Set.range β) := neg_mem hw₁
  have hn₂ : -w₂ ∈ Submodule.span ℤ (Set.range β) := neg_mem hw₂
  have subtype_vadd (w : E) (hw : w ∈ Submodule.span ℤ (Set.range β)) :
      (⟨w, hw⟩ : Submodule.span ℤ (Set.range β)) +ᵥ x = w + x := rfl
  have heq : (⟨-w₁, hn₁⟩ : Submodule.span ℤ (Set.range β)) = ⟨-w₂, hn₂⟩ :=
    (ZSpan.exist_unique_vadd_mem_fundamentalDomain β x).unique
      (by rw [subtype_vadd]; simpa only [sub_eq_add_neg, add_comm] using h₁)
      (by rw [subtype_vadd]; simpa only [sub_eq_add_neg, add_comm] using h₂)
  exact neg_injective (congrArg Subtype.val heq)

end TauCeti

universe u

namespace ZLattice

/-- A vector lies in the pull-back of a lattice along a linear map exactly when its image lies in
the lattice. -/
@[simp]
theorem mem_comap (K : Type*) [NormedField K] {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace K E] [NormedAddCommGroup F] [NormedSpace K F] (L : Submodule ℤ E)
    (e : F →ₗ[K] E) {x : F} : x ∈ ZLattice.comap K L e ↔ e x ∈ L :=
  Iff.rfl

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K] [HasSolidNorm K]
  [FloorRing K] {E : Type u} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]
  [ProperSpace E]

/-- A full lattice is the `ℤ`-span of a `K`-basis of the ambient space, indexed by a finite
type. -/
theorem exists_basis_span_eq (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice K L] :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (b : Basis ι K E),
      Submodule.span ℤ (Set.range b) = L :=
  have := module_finite K L
  have := module_free K L
  ⟨_, inferInstance, Classical.decEq _, (Free.chooseBasis ℤ L).ofZLatticeBasis K L,
    (Free.chooseBasis ℤ L).ofZLatticeBasis_span K L⟩

end ZLattice
