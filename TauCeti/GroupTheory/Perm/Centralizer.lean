/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The centralizer of a transitive group of permutations

A permutation commuting with every element of a transitive group of permutations, and fixing one
letter, is the identity: transitivity carries the fixed letter to any other letter, and the
commutation then makes the permutation fix that letter too. So the centralizer of a transitive
group of permutations, acting on the letters by evaluation, has trivial stabilizers, and on a
finite set of letters its order divides the number of letters.

This bounds the size of the centralizer of a transitive permutation group, which is the
semiregularity step behind the order bound for the automorphism group of a permutation group
action.

## Main results

* `Subgroup.eq_one_of_mem_centralizer_of_apply_eq`: a commuting permutation fixing a letter is the
  identity.
* `Subgroup.centralizer_stabilizer_eq_bot`: the centralizer of a transitive group of permutations
  acts freely on the letters.
* `Subgroup.natCard_centralizer_dvd`: the `Nat.card` of that centralizer divides the `Nat.card`
  of the letters.
* `Subgroup.card_centralizer_dvd`: on a finite set of letters, the order of that centralizer
  divides the number of letters.

The counting step is orbit-stabilizer: a set on which a group acts with trivial stabilizers is in
bijection with the product of its orbit space with the acting group, so the number of letters is
the number of orbits times the order of the centralizer.
-/

public section

namespace TauCeti

open Equiv MulAction

variable {α : Type*}

/-- A permutation commuting with a transitive group of permutations and fixing one letter is the
identity: transitivity moves the fixed letter to any other letter, where commutation forces it to
be fixed as well. -/
theorem _root_.Subgroup.eq_one_of_mem_centralizer_of_apply_eq
    {G : Subgroup (Equiv.Perm α)} (hG : MulAction.IsPretransitive G α)
    {τ : Equiv.Perm α} (hτ : τ ∈ Subgroup.centralizer (G : Set (Equiv.Perm α)))
    {i : α} (hi : τ i = i) : τ = 1 := by
  have hcomm : ∀ g ∈ G, g * τ = τ * g := Subgroup.mem_centralizer_iff.mp hτ
  refine Equiv.ext fun j => ?_
  obtain ⟨g, hg⟩ := hG.exists_smul_eq i j
  have hgj : (g : Equiv.Perm α) i = j := hg
  calc τ j = (τ * (g : Equiv.Perm α)) i := by rw [Equiv.Perm.mul_apply, hgj]
    _ = ((g : Equiv.Perm α) * τ) i := by rw [hcomm _ g.2]
    _ = j := by rw [Equiv.Perm.mul_apply, hi, hgj]
    _ = (1 : Equiv.Perm α) j := by rw [Equiv.Perm.one_apply]

/-- The centralizer of a transitive group of permutations, acting on the letters by evaluation,
has trivial stabilizers. -/
theorem _root_.Subgroup.centralizer_stabilizer_eq_bot
    {G : Subgroup (Equiv.Perm α)} (hG : MulAction.IsPretransitive G α) (i : α) :
    MulAction.stabilizer (Subgroup.centralizer (G : Set (Equiv.Perm α))) i = ⊥ := by
  refine eq_bot_iff.mpr fun τ hτ => ?_
  have hfix : (τ : Equiv.Perm α) i = i := by
    have hτ' : τ • i = i := MulAction.mem_stabilizer_iff.mp hτ
    rwa [Subgroup.smul_def, Equiv.Perm.smul_def] at hτ'
  rw [Subgroup.mem_bot]
  exact Subtype.ext (Subgroup.eq_one_of_mem_centralizer_of_apply_eq hG τ.property hfix)

/-- The cardinality of the centralizer of a transitive group of permutations divides the
cardinality of the letters, the centralizer being free on them and so exhibiting the letters as
the product of their orbit space with the centralizer. Since `Nat.card` is `0` on an infinite
carrier, this bounds the order of the centralizer only on a finite set of letters, where
`TauCeti.Subgroup.card_centralizer_dvd` is the bound. -/
theorem _root_.Subgroup.natCard_centralizer_dvd (G : Subgroup (Equiv.Perm α))
    (hG : MulAction.IsPretransitive G α) :
    Nat.card (Subgroup.centralizer (G : Set (Equiv.Perm α))) ∣ Nat.card α := by
  have hfree : ∀ i : α,
      MulAction.stabilizer (Subgroup.centralizer (G : Set (Equiv.Perm α))) i = ⊥ :=
    Subgroup.centralizer_stabilizer_eq_bot hG
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hfree)
  rw [Nat.card_prod] at hcard
  exact ⟨_, hcard.trans (mul_comm _ _)⟩

/-- **The order of the centralizer of a transitive group of permutations divides the number of
letters**: on a finite set of letters the centralizer is free on them, so its order divides their
number. -/
theorem _root_.Subgroup.card_centralizer_dvd [Fintype α] (G : Subgroup (Equiv.Perm α))
    (hG : MulAction.IsPretransitive G α) :
    Nat.card (Subgroup.centralizer (G : Set (Equiv.Perm α))) ∣ Fintype.card α := by
  have hcard : Nat.card α = Fintype.card α := Nat.card_eq_fintype_card
  exact hcard ▸ Subgroup.natCard_centralizer_dvd G hG

end TauCeti
