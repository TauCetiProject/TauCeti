/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.SetTheory.Cardinal.NatCard
import TauCeti.GroupTheory.GroupAction.Free

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
* `Equiv.Perm.center_eq_bot`: the permutations of at least three letters have trivial centre.

The counting step is `MulAction.natCard_dvd_natCard_of_isCancelSMul`: every orbit of a free action
is a copy of the acting group, so the order of the centralizer divides the number of letters.
-/

public section

namespace Subgroup

variable {α : Type*}

/-- A permutation commuting with a transitive group of permutations and fixing one letter is the
identity: transitivity moves the fixed letter to any other letter, where commutation forces it to
be fixed as well. -/
theorem eq_one_of_mem_centralizer_of_apply_eq
    {G : Subgroup (Equiv.Perm α)} (hG : MulAction.IsPretransitive G α)
    {τ : Equiv.Perm α} (hτ : τ ∈ centralizer (G : Set (Equiv.Perm α)))
    {i : α} (hi : τ i = i) : τ = 1 := by
  refine Equiv.ext fun j => ?_
  obtain ⟨g, rfl⟩ := hG.exists_smul_eq i j
  simpa [smul_def, Equiv.Perm.smul_def, hi] using
    congr($(mem_centralizer_iff.mp hτ g g.property) i).symm

/-- The centralizer of a transitive group of permutations acts freely on the letters by
evaluation. -/
theorem isCancelSMul_centralizer
    {G : Subgroup (Equiv.Perm α)} (hG : MulAction.IsPretransitive G α) :
    IsCancelSMul (centralizer (G : Set (Equiv.Perm α))) α :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr fun τ i hi =>
    OneMemClass.coe_eq_one.mp <| eq_one_of_mem_centralizer_of_apply_eq hG τ.property <| by
      rwa [smul_def, Equiv.Perm.smul_def] at hi

/-- **The order of the centralizer of a transitive group of permutations divides the number of
letters**, the centralizer acting freely on them. Since `Nat.card` is `0` on an infinite type,
this bounds the order of the centralizer only on a finite set of letters. -/
theorem card_centralizer_dvd
    {G : Subgroup (Equiv.Perm α)} (hG : MulAction.IsPretransitive G α) :
    Nat.card (centralizer (G : Set (Equiv.Perm α))) ∣ Nat.card α :=
  have := isCancelSMul_centralizer hG
  MulAction.natCard_dvd_natCard_of_isCancelSMul

end Subgroup

namespace Equiv.Perm

/-- **The permutations of at least three letters have trivial centre.** A permutation `g` moving
a letter `a` does not commute with the transposition of `g a` and a third letter. -/
theorem center_eq_bot {α : Type*} (hα : 3 ≤ Cardinal.mk α) : Subgroup.center (Perm α) = ⊥ := by
  classical
  refine (Subgroup.eq_bot_iff_forall _).2 fun g hg ↦
    Equiv.ext fun a ↦ by_contra fun (ha : g a ≠ a) ↦ ?_
  obtain ⟨c, hca, hcg⟩ := Cardinal.exists_ne_ne_of_three_le hα a (g a)
  -- `swap (g a) c * g` sends `a` to `c`, but `g * swap (g a) c` sends it to `g a`.
  have h := congr($(Subgroup.mem_center_iff.mp hg (swap (g a) c)) a)
  rw [mul_apply, mul_apply, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm ha) hca.symm] at h
  exact hcg h

end Equiv.Perm
