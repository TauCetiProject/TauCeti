/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Decidable
public import TauCeti.Combinatorics.PermutationTriple.Examples

/-!
# Deciding primitivity of a permutation triple

A monodromy action is preprimitive when it is pretransitive and preserves no nontrivial block
of sheets. The finite tests below enumerate every subset of sheets and every element of the
computed monodromy group. Testing just the two generators would be unsound: the condition
that a translate of a block is equal or disjoint need not survive products of generators.

The Boolean tests agree with Mathlib's `MulAction.IsBlock` and
`MulAction.IsPreprimitive`. The torus triple, the degree-three symmetric triple, and the
degree-one triple exercise imprimitive and primitive cases.
-/

public section

namespace TauCeti

namespace PermutationTriple

open Equiv MulAction
open scoped Pointwise

variable {n : ℕ} (t : PermutationTriple n)

/-- Decide whether a set of sheets is a block by testing every monodromy permutation. -/
def isBlockB (B : Finset (Fin n)) : Bool :=
  decide (∀ g ∈ t.monodromyFinset, g • B = B ∨ Disjoint (g • B) B)

/-- The finite block test agrees with Mathlib's block predicate for the monodromy action. -/
@[simp] theorem isBlockB_eq_true_iff (B : Finset (Fin n)) :
    t.isBlockB B = true ↔ IsBlock t.monodromyGroup (B : Set (Fin n)) := by
  rw [isBlockB, decide_eq_true_eq, isBlock_iff_smul_eq_or_disjoint]
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
def isPreprimitiveB : Bool :=
  decide ((∀ i, t.monodromyOrbitFinset i = Finset.univ) ∧
    ∀ B : Finset (Fin n), t.isBlockB B = true →
    B.card ≤ 1 ∨ B = Finset.univ)

/-- The finite primitivity test agrees with Mathlib's preprimitive action predicate. -/
@[simp] theorem isPreprimitiveB_eq_true_iff :
    t.isPreprimitiveB = true ↔ IsPreprimitive t.monodromyGroup (Fin n) := by
  rw [isPreprimitiveB, decide_eq_true_eq]
  constructor
  · rintro ⟨htrans, hblocks⟩
    have htrans' : IsPretransitive t.monodromyGroup (Fin n) := by
      rw [← t.closure_generators_eq_monodromyGroup]
      exact (Finset.isPretransitive_closure_iff_forall_orbitFinset_eq_univ _).2 htrans
    refine { toIsPretransitive := htrans', isTrivialBlock_of_isBlock := ?_ }
    intro B hB
    classical
    have hfin := hblocks B.toFinset
    have hblock : t.isBlockB B.toFinset = true :=
      (t.isBlockB_eq_true_iff _).2 (by simpa using hB)
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
    have htrivial := h.isTrivialBlock_of_isBlock ((t.isBlockB_eq_true_iff B).1 hB)
    rcases htrivial with hsmall | hall
    · left
      exact Finset.card_le_one_iff_subsingleton.mpr hsmall
    · right
      exact Finset.coe_inj.mp (hall.trans Finset.coe_univ.symm)

/-- Primitivity of the monodromy action is decidable by the finite block test. -/
instance : Decidable (IsPreprimitive t.monodromyGroup (Fin n)) :=
  decidable_of_iff _ t.isPreprimitiveB_eq_true_iff

/-- The torus triple is imprimitive: `{0, 2}` is a nontrivial block. -/
theorem isPreprimitiveB_torusTriple : torusTriple.isPreprimitiveB = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact not_isPreprimitive_torusTriple ((isPreprimitiveB_eq_true_iff _).mp h)

/-- The degree-three symmetric triple is primitive. -/
theorem isPreprimitiveB_s3Triple : s3Triple.isPreprimitiveB = true := by
  apply (isPreprimitiveB_eq_true_iff _).mpr
  exact @IsPreprimitive.of_prime_card _ _ _ _ isConnected_s3Triple.isPretransitive
    (by simpa using (by decide : Nat.Prime 3))

/-- The degree-one triple is primitive. -/
theorem isPreprimitiveB_cyclicTriple_one : (cyclicTriple 1).isPreprimitiveB = true := by
  apply (isPreprimitiveB_eq_true_iff _).mpr
  exact IsPreprimitive.of_subsingleton

end PermutationTriple

end TauCeti
