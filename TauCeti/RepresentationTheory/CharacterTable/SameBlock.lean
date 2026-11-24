/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import TauCeti.RepresentationTheory.CharacterTable.CentralCharacter

/-!
# The block congruence of complex characters

Let `M` be an ideal of the algebraic integers `integralClosure ℤ ℂ`. Two functions
`χ ψ : G → ℂ` are in the relation `TauCeti.SameBlock M χ ψ` when, for every `g ∈ G` with conjugacy
class `C`, the number `|C| (χ(g)/χ(1) − ψ(g)/ψ(1))` is an algebraic integer lying in `M`.

For the characters of irreducible complex representations, `|C| χ(g)/χ(1)` is the value
`ω_χ(K_C)` of the central character on the class sum, an algebraic integer, so the relation is the
congruence of central characters modulo `M` (`TauCeti.sameBlock_character_iff`). For `M` maximal
with `p ∈ M` this is the congruence that defines the `p`-blocks of irreducible characters, with the
residue field of a `p`-modular system replaced by the algebraic integers modulo `M`.

The relation is an equivalence relation on all functions `G → ℂ`, for every ideal `M`
(`TauCeti.SameBlock.setoid`), and it is monotone in `M`.

## Main definitions

* `TauCeti.SameBlock M χ ψ`: the block congruence of `χ` and `ψ` modulo `M`.

## Main results

* `TauCeti.SameBlock.setoid`: the block congruence is an equivalence relation.
* `TauCeti.sameBlock_character_iff`: for irreducible complex representations it is the congruence
  of the central characters on the class sums modulo `M`.

## References

* B. Sambale, *Blocks of Finite Groups and Their Invariants*, Lecture Notes in Mathematics 2127,
  Definition 1.6, p. 15.
-/

public section

open scoped MonoidAlgebra

namespace TauCeti

variable {G : Type*} {M N : Ideal (integralClosure ℤ ℂ)} {χ ψ φ : G → ℂ}

section Monoid

variable [Monoid G]

/-- The **block congruence** of complex functions on `G` modulo an ideal `M` of the algebraic
integers: for every `g ∈ G` with conjugacy class `C`, the number `|C| (χ(g)/χ(1) − ψ(g)/ψ(1))` is
(the image of) an element of `M`. For irreducible characters and `M` maximal with `p ∈ M` its
classes are the `p`-blocks. -/
def SameBlock (M : Ideal (integralClosure ℤ ℂ)) (χ ψ : G → ℂ) : Prop :=
  ∀ g : G, ∃ x ∈ M, (x : ℂ) = Nat.card (ConjClasses.mk g).carrier * (χ g / χ 1 - ψ g / ψ 1)

theorem sameBlock_iff : SameBlock M χ ψ ↔ ∀ g : G, ∃ x ∈ M,
    (x : ℂ) = Nat.card (ConjClasses.mk g).carrier * (χ g / χ 1 - ψ g / ψ 1) :=
  Iff.rfl

namespace SameBlock

@[refl]
protected theorem refl (M : Ideal (integralClosure ℤ ℂ)) (χ : G → ℂ) : SameBlock M χ χ :=
  fun _ => ⟨0, M.zero_mem, by simp⟩

@[symm]
protected theorem symm (h : SameBlock M χ ψ) : SameBlock M ψ χ := fun g => by
  obtain ⟨x, hx, hxg⟩ := h g
  exact ⟨-x, M.neg_mem_iff.2 hx, by push_cast; rw [hxg]; ring⟩

@[trans]
protected theorem trans (h₁ : SameBlock M χ ψ) (h₂ : SameBlock M ψ φ) : SameBlock M χ φ :=
  fun g => by
    obtain ⟨x, hx, hxg⟩ := h₁ g
    obtain ⟨y, hy, hyg⟩ := h₂ g
    exact ⟨x + y, M.add_mem hx hy, by push_cast; rw [hxg, hyg]; ring⟩

/-- The block congruence modulo any ideal is an equivalence relation. -/
protected def setoid (G : Type*) [Monoid G] (M : Ideal (integralClosure ℤ ℂ)) : Setoid (G → ℂ) where
  r := SameBlock M
  iseqv := ⟨SameBlock.refl M, SameBlock.symm, SameBlock.trans⟩

/-- The block congruence setoid relates exactly the functions in the block congruence. -/
@[simp]
theorem setoid_apply : SameBlock.setoid G M χ ψ ↔ SameBlock M χ ψ :=
  Iff.rfl

/-- The block congruence is monotone in the ideal. -/
theorem mono (hMN : M ≤ N) (h : SameBlock M χ ψ) : SameBlock N χ ψ := fun g => by
  obtain ⟨x, hx, hxg⟩ := h g
  exact ⟨x, hMN hx, hxg⟩

end SameBlock

end Monoid

section Character

variable [Group G] {V W : Type*} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  (ρ : Representation ℂ G V) (σ : Representation ℂ G W) [ρ.IsIrreducible] [σ.IsIrreducible]

/-- **The block congruence of irreducible characters is the congruence of central characters.**
Two irreducible complex characters are in the block congruence modulo `M` exactly when, on every
class sum `K_C`, the difference `ω_χ(K_C) − ω_ψ(K_C)` of their central characters is (the image of)
an element of `M`. -/
theorem sameBlock_character_iff [Fintype G] [DecidableEq G] :
    SameBlock M ρ.character σ.character ↔ ∀ C : ConjClasses G, ∃ x ∈ M, (x : ℂ) =
      Representation.centralCharacter ρ (classSumCenter C) -
        Representation.centralCharacter σ (classSumCenter C) := by
  have key (g : G) : Nat.card (ConjClasses.mk g).carrier *
      (ρ.character g / ρ.character 1 - σ.character g / σ.character 1) =
      Representation.centralCharacter ρ (classSumCenter (ConjClasses.mk g)) -
        Representation.centralCharacter σ (classSumCenter (ConjClasses.mk g)) := by
    rw [Representation.centralCharacter_classSumCenter ρ rfl
        (by rw [ρ.char_one]; exact Representation.IsIrreducible.natCast_finrank_ne_zero ‹_›),
      Representation.centralCharacter_classSumCenter σ rfl
        (by rw [σ.char_one]; exact Representation.IsIrreducible.natCast_finrank_ne_zero ‹_›)]
    ring
  refine ⟨fun h C => ?_, fun h g => ?_⟩
  · obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective C
    simpa only [key] using h g
  · simpa only [key] using h (ConjClasses.mk g)

end Character

end TauCeti
