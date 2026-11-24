/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.GroupTheory.GroupAction.Orbit.Weight
import Mathlib.GroupTheory.Perm.Sign

/-!
# The orbit weight is not the orbit count

Let `S₃ = Equiv.Perm (Fin 3)` act on `Fin 3`, with the trivial subgroup `Γ = ⊥` and `Y = {0}`.
The permutations keeping `0` in `Y` are the two permutations fixing `0`, so the orbit weight of
`0` is two, while `G • 0 ∩ Y = {0}` is a single orbit. The stabilizer sum computes the weight as
the one term `[Stab(0) : ⊥] = 2`.
-/

open Equiv MulAction

namespace TauCeti

/-- In `S₃` acting on three points, with `Γ = ⊥` and `Y = {0}`, the orbit weight of `0` is two
while the orbit count of `0` is one. -/
example : (⊥ : Subgroup (Perm (Fin 3))).orbitWeight ({0} : Set (Fin 3)) 0 = 2 ∧
    (⊥ : Subgroup (Perm (Fin 3))).orbitCount ({0} : Set (Fin 3)) 0 = 1 := by
  have hN : (⊥ : Subgroup (Perm (Fin 3))).orbitCountClasses ({0} : Set (Fin 3)) 0 =
      {Quotient.mk _ 0} := by
    ext o
    simp only [Subgroup.mem_orbitCountClasses, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, -, rfl, rfl⟩
      rfl
    · rintro rfl
      exact ⟨0, mem_orbit_self 0, rfl, rfl⟩
  have hout : (Quotient.mk (orbitRel (⊥ : Subgroup (Perm (Fin 3))) (Fin 3)) 0).out = 0 := by
    obtain ⟨γ, hγ⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact
      (Quotient.out_eq (Quotient.mk (orbitRel (⊥ : Subgroup (Perm (Fin 3))) (Fin 3)) 0))))
    rw [Subsingleton.elim γ 1, one_smul] at hγ
    exact hγ.symm
  refine ⟨?_, by rw [Subgroup.orbitCount_def, hN, Set.ncard_singleton]⟩
  rw [Subgroup.orbitWeight_eq_finsum_relIndex (Set.toFinite _) Quotient.out_eq, hN,
    finsum_mem_singleton, hout, Subgroup.relIndex_bot_left, Nat.card_eq_fintype_card]
  decide +kernel

end TauCeti
