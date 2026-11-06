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
group of permutations, acting on the letters by evaluation, acts freely, and its order divides the
number of letters.

This bounds the size of the centralizer of a transitive permutation group, which is the
semiregularity step behind the order bound for the automorphism group of a permutation group
action.

## Main results

* `Subgroup.eq_one_of_mem_centralizer_of_apply_eq`: a commuting permutation fixing a letter is the
  identity.
* `Subgroup.isCancelSMul_centralizer`: the centralizer of a transitive group of permutations acts
  freely on the letters.
* `Subgroup.card_centralizer_dvd`: the `Nat.card` of that centralizer divides the `Nat.card` of
  the letters.

The counting step is orbit-stabilizer: a set on which a group acts freely is in bijection with the
product of its orbit space with the acting group, so the number of letters is the number of orbits
times the order of the centralizer.
-/

public section

namespace TauCeti

variable {α : Type*}

/-- A permutation commuting with a transitive group of permutations and fixing one letter is the
identity: transitivity moves the fixed letter to any other letter, where commutation forces it to
be fixed as well. -/
theorem _root_.Subgroup.eq_one_of_mem_centralizer_of_apply_eq
    {G : Subgroup (Equiv.Perm α)} (hG : MulAction.IsPretransitive G α)
    {τ : Equiv.Perm α} (hτ : τ ∈ Subgroup.centralizer (G : Set (Equiv.Perm α)))
    {i : α} (hi : τ i = i) : τ = 1 := by
  refine Equiv.ext fun j => ?_
  obtain ⟨g, rfl⟩ := hG.exists_smul_eq i j
  simpa [Subgroup.smul_def, Equiv.Perm.smul_def, hi] using
    congr($(Subgroup.mem_centralizer_iff.mp hτ g g.2) i).symm

/-- The centralizer of a transitive group of permutations acts freely on the letters by
evaluation. -/
theorem _root_.Subgroup.isCancelSMul_centralizer
    {G : Subgroup (Equiv.Perm α)} (hG : MulAction.IsPretransitive G α) :
    IsCancelSMul (Subgroup.centralizer (G : Set (Equiv.Perm α))) α :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr fun τ i hi =>
    OneMemClass.coe_eq_one.mp <| Subgroup.eq_one_of_mem_centralizer_of_apply_eq hG τ.2 <| by
      rwa [Subgroup.smul_def, Equiv.Perm.smul_def] at hi

/-- **The order of the centralizer of a transitive group of permutations divides the number of
letters**, the centralizer acting freely on them. Since `Nat.card` is `0` on an infinite type,
this bounds the order of the centralizer only on a finite set of letters. -/
theorem _root_.Subgroup.card_centralizer_dvd
    {G : Subgroup (Equiv.Perm α)} (hG : MulAction.IsPretransitive G α) :
    Nat.card (Subgroup.centralizer (G : Set (Equiv.Perm α))) ∣ Nat.card α := by
  have := Subgroup.isCancelSMul_centralizer hG
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd
    (X := α) (G := Subgroup.centralizer (G : Set (Equiv.Perm α))) IsCancelSMul.stabilizer_eq_bot)
  rw [Nat.card_prod] at hcard
  exact Dvd.intro_left _ hcard.symm

end TauCeti
