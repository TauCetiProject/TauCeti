/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.GroupTheory.SpecificGroups.Alternating
import TauCeti.GroupTheory.LeftMultipliers

/-!
# Regression examples: left multipliers and conjugation stabilizers

These examples exercise `TauCeti.GroupTheory.LeftMultipliers` on the symmetric group `S₃`:

* for the identity of `S₃`, the conjugation stabilizer is the trivial centre, although every
  conjugation preserves the kernel;
* for the squaring map of `S₃`, the conjugation stabilizer is `A₃` while the left multipliers are
  trivial, so the conjugation stabilizer can be nontrivial and proper while the multiplier
  subgroup is trivial.
-/

open Equiv Function

-- For the identity of `S₃` the conjugation stabilizer is the trivial centre.
example : conjStabilizer (MonoidHom.id (Perm (Fin 3))) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  simp only [MonoidHom.conjStabilizer_eq_comap_centralizer, Subgroup.mem_comap,
    Subgroup.mem_centralizer_iff, SetLike.mem_coe, MonoidHom.mem_range, MonoidHom.id_apply,
    exists_eq, forall_const] at hg
  revert g
  decide

-- For the squaring map of `S₃` the conjugation stabilizer is `A₃`.
example : conjStabilizer (fun x : Perm (Fin 3) ↦ x ^ 2) = alternatingGroup (Fin 3) := by
  ext g
  rw [mem_conjStabilizer_iff, Perm.mem_alternatingGroup]
  revert g
  decide

-- For the squaring map of `S₃` the left multipliers are trivial.
example : (⟨fun x ↦ x ^ 2, one_pow 2⟩ : OneHom (Perm (Fin 3)) (Perm (Fin 3))).leftMultipliers =
    ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  rw [OneHom.mem_leftMultipliers_iff] at hg
  revert g
  decide

-- Every element is a left multiplier of a homomorphism.
example {G C : Type*} [Group G] [Group C] (φ : G →* C) (g : G) :
    g ∈ φ.toOneHom.leftMultipliers := by
  simp
