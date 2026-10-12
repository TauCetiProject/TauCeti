/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Primitivity.Defs
public import TauCeti.Combinatorics.PermutationTriple.Decidable

/-!
# Deciding primitivity of a permutation triple

A monodromy action is preprimitive when it is pretransitive and preserves no nontrivial block
of sheets. The finite tests below enumerate every subset of sheets and every element of the
computed monodromy group. Testing just the two generators would be unsound: the condition
that a translate of a block is equal or disjoint need not survive products of generators.

The Boolean tests agree with Mathlib's `MulAction.IsBlock` and
`MulAction.IsPreprimitive`.
-/

public section

namespace TauCeti

namespace PermutationTriple

open Equiv MulAction
open scoped Pointwise

variable {n : ℕ} (t : PermutationTriple n)

/-- Decide whether a set of sheets is a block by testing every monodromy permutation. -/
@[expose] def isBlockBool (B : Finset (Fin n)) : Bool :=
  decide (∀ g ∈ t.monodromyFinset, g • B = B ∨ Disjoint (g • B) B)

/-- The finite block test agrees with Mathlib's block predicate for the monodromy action. -/
@[simp] theorem isBlockBool_eq_true_iff (B : Finset (Fin n)) :
    t.isBlockBool B = true ↔ IsBlock t.monodromyGroup (B : Set (Fin n)) := by
  rw [isBlockBool, decide_eq_true_eq, isBlock_iff_smul_eq_or_disjoint]
  constructor
  · intro h g
    have hg := h g.1 ((t.mem_monodromyFinset).2 g.2)
    simpa only [Subgroup.smul_def, ← Finset.coe_smul_finset,
      ← Finset.disjoint_coe, Finset.coe_inj] using hg
  · intro h g hg
    have hg' := h ⟨g, (t.mem_monodromyFinset).1 hg⟩
    simpa only [Subgroup.smul_def, ← Finset.coe_smul_finset,
      ← Finset.disjoint_coe, Finset.coe_inj] using hg'

/-- Decide primitivity by checking transitivity and every subset of the sheets for a
nontrivial block. -/
@[expose] def isPrimitiveBool : Bool :=
  decide ((∀ i, t.monodromyOrbitFinset i = Finset.univ) ∧
    ∀ B : Finset (Fin n), t.isBlockBool B = true →
    B.card ≤ 1 ∨ B = Finset.univ)

/-- The finite primitivity test agrees with primitivity of the triple. -/
@[simp] theorem isPrimitiveBool_eq_true_iff :
    t.isPrimitiveBool = true ↔ t.IsPrimitive := by
  rw [t.isPrimitive_iff, isPrimitiveBool, decide_eq_true_eq]
  constructor
  · rintro ⟨htrans, hblocks⟩
    have htrans' : IsPretransitive t.monodromyGroup (Fin n) := by
      rw [← t.closure_generators_eq_monodromyGroup]
      exact (Finset.isPretransitive_closure_iff_forall_orbitFinset_eq_univ _).2 htrans
    refine { toIsPretransitive := htrans', isTrivialBlock_of_isBlock := ?_ }
    intro B hB
    classical
    have hfin := hblocks B.toFinset
    have hblock : t.isBlockBool B.toFinset = true :=
      (t.isBlockBool_eq_true_iff _).2 (by simpa using hB)
    rcases hfin hblock with hsmall | hall
    · left
      simpa only [Set.coe_toFinset] using Finset.card_le_one_iff_subsingleton.mp hsmall
    · right
      simpa using hall
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← t.closure_generators_eq_monodromyGroup] at h
      exact (Finset.isPretransitive_closure_iff_forall_orbitFinset_eq_univ _).1
        h.toIsPretransitive
    intro B hB
    have htrivial := h.isTrivialBlock_of_isBlock ((t.isBlockBool_eq_true_iff B).1 hB)
    rcases htrivial with hsmall | hall
    · left
      exact Finset.card_le_one_iff_subsingleton.mpr hsmall
    · right
      exact Finset.coe_inj.mp (hall.trans Finset.coe_univ.symm)

/-- Primitivity of the monodromy action is decidable by the finite block test. -/
instance : Decidable t.IsPrimitive :=
  decidable_of_iff _ t.isPrimitiveBool_eq_true_iff

end PermutationTriple

end TauCeti
