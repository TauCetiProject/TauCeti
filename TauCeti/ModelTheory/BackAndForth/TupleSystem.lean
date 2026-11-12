/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.BackAndForth.Equivalence

/-!
# Tuple back-and-forth systems

A tuple back-and-forth system is a set of pairs of equally long finite tuples containing the
empty pair, preserving atomic types, and admitting one-element extensions in both directions
within the same set. Every pair in such a system is back-and-forth equivalent at every ordinal,
and every tuple of either structure occurs in some pair of the system.
These systems allow characteristic sentences to produce potential isomorphisms without
requiring every finite partial isomorphism to extend.

This is the tuple presentation of back-and-forth systems used in Carol Karp,
*Finite-quantifier equivalence* (1965). See also Cameron Freer's
`cameronfreer/infinitary-logic`, `InfinitaryLogic/Karp/PotentialIso.lean` at checkpoint
`9f82bd572af2d79a043c6bc3f1b745f14e0bcaa4`. Here the system is an explicit set of tuple pairs.
-/

public section

universe u v w w' o

namespace TauCeti

open FirstOrder Fin

variable {L : Language.{u, v}} [L.IsRelational]
variable {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]

/-- A set of pairs of finite tuples containing the empty pair, preserving atomic types, and
closed under matching one-element extensions in both directions within the set. -/
structure IsTupleBFSystem (S : Set (Σ n, (Fin n → M) × (Fin n → N))) : Prop where
  /-- The empty tuples belong to the system. -/
  empty_mem : ⟨0, Fin.elim0, Fin.elim0⟩ ∈ S
  /-- Every pair in the system agrees on all atomic tests, including nullary relations. -/
  sameAtomicType {n : ℕ} {a : Fin n → M} {b : Fin n → N} :
    ⟨n, a, b⟩ ∈ S → SameAtomicType (L := L) a b
  /-- Every element of the first structure has a matching extension in the system. -/
  forth {n : ℕ} {a : Fin n → M} {b : Fin n → N} :
    ⟨n, a, b⟩ ∈ S → ∀ x : M, ∃ y : N, ⟨n + 1, snoc a x, snoc b y⟩ ∈ S
  /-- Every element of the second structure has a matching extension in the system. -/
  back {n : ℕ} {a : Fin n → M} {b : Fin n → N} :
    ⟨n, a, b⟩ ∈ S → ∀ y : N, ∃ x : M, ⟨n + 1, snoc a x, snoc b y⟩ ∈ S

namespace IsTupleBFSystem

variable {S : Set (Σ n, (Fin n → M) × (Fin n → N))}

/-- Swapping the two tuples of every pair of a tuple back-and-forth system gives a tuple
back-and-forth system in the other direction. -/
theorem symm (h : IsTupleBFSystem (L := L) S) :
    IsTupleBFSystem (L := L) {p : Σ n, (Fin n → N) × (Fin n → M) | ⟨p.1, p.2.2, p.2.1⟩ ∈ S} where
  empty_mem := h.empty_mem
  sameAtomicType hab := (h.sameAtomicType hab).symm
  forth hab x := h.back hab x
  back hab y := h.forth hab y

/-- Pairs in one back-and-forth system agree at every ordinal level. -/
theorem bfEquiv (h : IsTupleBFSystem (L := L) S) (α : Ordinal.{o})
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} (hab : ⟨n, a, b⟩ ∈ S) :
    BFEquiv (L := L) α n a b := by
  induction α using Ordinal.limitRecOn generalizing n with
  | zero => exact BFEquiv.zero.mpr (h.sameAtomicType hab)
  | add_one α ih =>
    refine (BFEquiv.add_one α a b).mpr ⟨ih hab, ?_, ?_⟩
    · intro x
      obtain ⟨y, hy⟩ := h.forth hab x
      exact ⟨y, ih hy⟩
    · intro y
      obtain ⟨x, hx⟩ := h.back hab y
      exact ⟨x, ih hx⟩
  | limit α hα ih =>
    exact (BFEquiv.limit hα a b).mpr fun β hβ => ih β hβ hab

/-- Every tuple of `M` is the first component of some pair in a tuple back-and-forth system:
repeated forth moves extend the empty pair. -/
theorem exists_snd_mem (h : IsTupleBFSystem (L := L) S) {n : ℕ} (a : Fin n → M) :
    ∃ b : Fin n → N, ⟨n, a, b⟩ ∈ S := by
  induction n with
  | zero => exact ⟨finZeroElim, by convert h.empty_mem⟩
  | succ n ih =>
    obtain ⟨b, hb⟩ := ih (init a)
    obtain ⟨y, hy⟩ := h.forth hb (a (last n))
    exact ⟨snoc b y, by rwa [snoc_init_self] at hy⟩

/-- Every tuple of `N` is the second component of some pair in a tuple back-and-forth system:
repeated back moves extend the empty pair. -/
theorem exists_fst_mem (h : IsTupleBFSystem (L := L) S) {n : ℕ} (b : Fin n → N) :
    ∃ a : Fin n → M, ⟨n, a, b⟩ ∈ S := by
  induction n with
  | zero => exact ⟨finZeroElim, by convert h.empty_mem⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih (init b)
    obtain ⟨x, hx⟩ := h.back ha (b (last n))
    exact ⟨snoc a x, by rwa [snoc_init_self] at hx⟩

end IsTupleBFSystem

end TauCeti
