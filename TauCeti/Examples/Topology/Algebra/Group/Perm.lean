/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Algebra.Group.Perm

/-!
# Examples of pointwise permutation topology

The infinite symmetric group is Polish and acts continuously on `ℕ`, while finite symmetric
groups, including the group on the empty carrier, are discrete. Every identity neighbourhood
in the infinite symmetric group contains a nonidentity transposition: finite pointwise
stabilizers do not make this topology discrete.
-/

open Set Filter Topology

namespace TauCeti

example : PolishSpace (Equiv.Perm ℕ) := inferInstance

example : IsTopologicalGroup (Equiv.Perm ℕ) := inferInstance

example : ContinuousSMul (Equiv.Perm ℕ) ℕ := inferInstance

example (n : ℕ) : DiscreteTopology (Equiv.Perm (Fin n)) := inferInstance

example : DiscreteTopology (Equiv.Perm (Fin 0)) := inferInstance

example (a b : ℕ) : IsOpen {σ : Equiv.Perm ℕ | σ a = b} :=
  (isOpen_discrete ({b} : Set ℕ)).preimage (Equiv.Perm.continuous_apply a)

example : ¬ DiscreteTopology (Equiv.Perm ℕ) := by
  intro h
  obtain ⟨s, hs, hsub⟩ := Equiv.Perm.hasBasis_nhds_one_fixingSubgroup.mem_iff.1
    ((discreteTopology_iff_singleton_mem_nhds.1 h) (1 : Equiv.Perm ℕ))
  obtain ⟨a, ha⟩ := hs.exists_notMem
  obtain ⟨b, hb⟩ := (hs.insert a).exists_notMem
  have hfix : Equiv.swap a b ∈ fixingSubgroup (Equiv.Perm ℕ) s := by
    rw [mem_fixingSubgroup_iff]
    intro x hx
    exact Equiv.swap_apply_of_ne_of_ne (ne_of_mem_of_not_mem hx ha)
      (ne_of_mem_of_not_mem hx (fun h => hb (Or.inr h)))
  have heq := congrArg (fun σ : Equiv.Perm ℕ => σ a) (Set.mem_singleton_iff.1 (hsub hfix))
  exact hb (Or.inl (by simpa using heq))

end TauCeti
