/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.FinThree.Basic
public import TauCeti.RepresentationTheory.CharacterTable.Degree.Center
public import TauCeti.RepresentationTheory.Symmetric.Standard

/-!
# Regression examples: degrees divide the index of a central subgroup

`Representation.finrank_dvd_index_of_le_center` says that the degree of an irreducible complex
representation of a finite group divides the index of every central subgroup. These examples
check on `S₃` that centrality cannot be dropped: the stabilizer of the point `2`, which is the
subgroup `⟨(0 1)⟩` of order `2` by `TauCeti.stabilizer_perm_fin_three_eq_zpowers`, has index `3`,
it is not central, and the standard representation is irreducible of degree `2`, which does not
divide `3`. The trivial subgroup is central, and `2` divides its index `6`.
-/

namespace TauCeti.FinrankDvdIndexOfLeCenterExamples

open Module

-- The stabilizer of `2` in `S₃` is `⟨(0 1)⟩`.
example : MulAction.stabilizer (Equiv.Perm (Fin 3)) (2 : Fin 3) =
    Subgroup.zpowers (Equiv.swap 0 1) :=
  stabilizer_perm_fin_three_eq_zpowers 2

-- The subgroup `⟨(0 1)⟩` has index `3` in `S₃`.
example : (MulAction.stabilizer (Equiv.Perm (Fin 3)) (2 : Fin 3)).index = 3 := by
  rw [MulAction.index_stabilizer_of_transitive]
  simp

-- The subgroup `⟨(0 1)⟩` is not central, since it is not even normal.
example : ¬ MulAction.stabilizer (Equiv.Perm (Fin 3)) (2 : Fin 3) ≤
    Subgroup.center (Equiv.Perm (Fin 3)) :=
  fun h => not_normal_stabilizer_perm_fin_three 2 (Subgroup.normal_of_le_center h)

-- The standard representation of `S₃` over `ℂ` is irreducible of degree `2`.
example : (standardRepresentation ℂ (Fin 3)).IsIrreducible ∧
    finrank ℂ (augmentationSubrepresentation ℂ (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule = 2 :=
  ⟨isIrreducible_standardRepresentation_fin_three (by norm_num), by simp⟩

-- Centrality is needed: the conclusion of `Representation.finrank_dvd_index_of_le_center` fails
-- for the non-central subgroup `⟨(0 1)⟩` of index `3`, since `2` does not divide `3`.
example : ¬ finrank ℂ (augmentationSubrepresentation ℂ (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule ∣
    (MulAction.stabilizer (Equiv.Perm (Fin 3)) (2 : Fin 3)).index := by
  rw [finrank_augmentationSubrepresentation, MulAction.index_stabilizer_of_transitive]
  simp

-- For the central subgroup `⊥` the theorem applies, and `2` divides `|S₃ : ⊥| = 6`.
example : finrank ℂ (augmentationSubrepresentation ℂ (Equiv.Perm (Fin 3)) (Fin 3)).toSubmodule ∣
    (⊥ : Subgroup (Equiv.Perm (Fin 3))).index :=
  haveI := isIrreducible_standardRepresentation_fin_three (k := ℂ) (by norm_num)
  Representation.finrank_dvd_index_of_le_center (standardRepresentation ℂ (Fin 3)) ⊥ bot_le

end TauCeti.FinrankDvdIndexOfLeCenterExamples
