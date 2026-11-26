/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Set.Defs

/-!
# The Powers partition property of groups

A group `Γ` has the *Powers partition property* (`TauCeti.HasPowersProperty Γ`) if for every finite
subset `F ⊆ Γ \ {1}` and every `N : ℕ`, there exist a partition `Γ = C ⊔ D` and elements
`γ : Fin N → Γ` such that `f • C` is disjoint from `C` for every `f ∈ F` and the translates
`γ j • D` are pairwise disjoint.

This property is the combinatorial input to Powers's averaging method proving simplicity and
uniqueness of the trace for reduced group C⋆-algebras. Free groups on at least two generators have
the Powers property (`FreeGroup.hasPowersProperty`).

## Main definitions

* `TauCeti.HasPowersProperty`: the Powers partition property of a group `Γ`.

## Main statements

* `TauCeti.hasPowersProperty_def`: unfolding lemma for `HasPowersProperty`.

## References

* R. T. Powers, *Simplicity of the C*-algebra associated with the free group on two generators*,
  Duke Math. J. 42 (1975), 151–156.
* P. de la Harpe, *On simplicity of reduced C*-algebras of groups*, Bull. Lond. Math. Soc. 39
  (2007), 1–26, Definition 9.
-/

public section

namespace TauCeti

/-- **The Powers partition property** of a group `Γ` (de la Harpe, Definition 9): for every finite
set `F ⊆ Γ \ {1}` and every `N : ℕ`, there exist a partition `Γ = C ⊔ D` and elements
`γ : Fin N → Γ` such that `f • C` is disjoint from `C` for every `f ∈ F` and the translates
`γ j • D` are pairwise disjoint. -/
def HasPowersProperty (Γ : Type*) [Group Γ] : Prop :=
  ∀ (F : Finset Γ), (∀ f ∈ F, f ≠ 1) → ∀ N : ℕ,
    ∃ (C D : Set Γ) (γ : Fin N → Γ),
      Disjoint C D ∧ C ∪ D = Set.univ ∧
      (∀ f ∈ F, Disjoint ((fun x : Γ ↦ f * x) '' C) C) ∧
      Pairwise (fun i j : Fin N ↦
        Disjoint ((fun x : Γ ↦ γ i * x) '' D) ((fun x : Γ ↦ γ j * x) '' D))

/-- Unfolding lemma for `HasPowersProperty`. -/
theorem hasPowersProperty_def {Γ : Type*} [Group Γ] :
    HasPowersProperty Γ ↔
      ∀ (F : Finset Γ), (∀ f ∈ F, f ≠ 1) → ∀ N : ℕ,
        ∃ (C D : Set Γ) (γ : Fin N → Γ),
          Disjoint C D ∧ C ∪ D = Set.univ ∧
          (∀ f ∈ F, Disjoint ((fun x : Γ ↦ f * x) '' C) C) ∧
          Pairwise (fun i j : Fin N ↦
            Disjoint ((fun x : Γ ↦ γ i * x) '' D) ((fun x : Γ ↦ γ j * x) '' D)) :=
  Iff.rfl

end TauCeti
