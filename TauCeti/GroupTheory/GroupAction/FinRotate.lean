/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Jordan
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Transitivity from cyclic rotation

A permutation subgroup containing cyclic rotation acts transitively on the finite ordinal.
This gives a transitivity criterion for groups specified by generators, including the empty
and singleton ordinals.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm MulAction

/-- A permutation subgroup containing cyclic rotation acts transitively. -/
theorem isPretransitive_of_finRotate_mem {n : ℕ}
    {G : Subgroup (Perm (Fin n))} (hg : finRotate n ∈ G) : IsPretransitive G (Fin n) := by
  rcases n with _ | _ | n
  · infer_instance
  · refine ⟨fun x y ↦ ⟨1, ?_⟩⟩
    exact Fin.ext (by omega)
  · have h := Equiv.Perm.isPretransitive_of_isCycle_mem (G := G) isCycle_finRotate hg
    rw [support_finRotate, Finset.coe_univ, Set.compl_univ] at h
    exact IsPretransitive.of_surjective_map
      SubMulAction.ofFixingSubgroupEmpty_equivariantMap_bijective.surjective h

end TauCeti
