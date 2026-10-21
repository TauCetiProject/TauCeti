/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Presentation

/-!
# Potential isomorphism and all back-and-forth levels

Two relational structures are potentially isomorphic exactly when their empty tuples are
back-and-forth equivalent at every ordinal level. More generally, equivalence at every level
is itself closed under matching one-element extensions. The extension argument takes the
supremum of one failure level for each possible match.

This is the all-level characterization in Carol Karp, *Finite-quantifier equivalence* (1965).
The tuple-system formulation follows Cameron Freer's `cameronfreer/infinitary-logic`,
`InfinitaryLogic/Karp/PotentialIso.lean` at checkpoint
`9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`. Here it is connected to the finitely generated
partial-equivalence definition of potential isomorphism through `IsTupleBFSystem`.
-/

public section

universe u v w w'

namespace TauCeti

open FirstOrder Fin

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

namespace BFEquiv

variable {n : ℕ} {a : Fin n → M} {b : Fin n → N}

/-- Tuples equivalent at every ordinal level admit a matching extension for each element of
the first structure. -/
theorem exists_forth_of_all
    (h : ∀ α : Ordinal.{max w w'}, BFEquiv (L := L) α n a b) (x : M) :
    ∃ y : N, ∀ α : Ordinal.{max w w'},
      BFEquiv (L := L) α (n + 1) (snoc a x) (snoc b y) := by
  classical
  by_contra hxy
  push Not at hxy
  let failure : N → Ordinal.{max w w'} := fun y => (hxy y).choose
  have hfailure (y : N) :
      ¬ BFEquiv (L := L) (failure y) (n + 1) (snoc a x) (snoc b y) :=
    (hxy y).choose_spec
  let β : Ordinal.{max w w'} := ⨆ y, failure y
  obtain ⟨_, hforth, _⟩ := (BFEquiv.add_one β a b).mp (h (β + 1))
  obtain ⟨y, hy⟩ := hforth x
  exact hfailure y (hy.mono (Ordinal.le_iSup failure y))

/-- Tuples equivalent at every ordinal level admit a matching extension for each element of
the second structure. -/
theorem exists_back_of_all
    (h : ∀ α : Ordinal.{max w w'}, BFEquiv (L := L) α n a b) (y : N) :
    ∃ x : M, ∀ α : Ordinal.{max w w'},
      BFEquiv (L := L) α (n + 1) (snoc a x) (snoc b y) := by
  obtain ⟨x, hx⟩ := exists_forth_of_all (L := L) (a := b) (b := a)
    (fun α => (h α).symm) y
  exact ⟨x, fun α => (hx α).symm⟩

end BFEquiv

/-- Two relational structures are potentially isomorphic exactly when their empty tuples are
back-and-forth equivalent at every ordinal level in the joint structure universe. -/
theorem potentialIso_iff_bfEquiv_all :
    PotentialIso (L := L) M N ↔
      ∀ α : Ordinal.{max w w'},
        BFEquiv (L := L) α 0 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) := by
  constructor
  · intro h α
    obtain ⟨S, hS⟩ := h.exists_isTupleBFSystem
    exact hS.bfEquiv α hS.empty_mem
  · intro h
    let S : Set (Σ n, (Fin n → M) × (Fin n → N)) :=
      {p | ∀ α : Ordinal.{max w w'}, BFEquiv (L := L) α p.1 p.2.1 p.2.2}
    apply IsTupleBFSystem.potentialIso (S := S)
    refine ⟨h, ?_, ?_, ?_⟩
    · intro n a b hab
      exact (hab 0).sameAtomicType
    · intro n a b hab x
      exact BFEquiv.exists_forth_of_all hab x
    · intro n a b hab y
      exact BFEquiv.exists_back_of_all hab y

end TauCeti
