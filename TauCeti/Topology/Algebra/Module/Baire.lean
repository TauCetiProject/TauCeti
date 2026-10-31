/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Baire.Lemmas

/-!
# Countable covers by closed submodules

Let `A` be a ring with a topology in which zero is a limit of units, for instance a nontrivially
normed field. A topological module over `A` has no proper submodule with nonempty interior
(Mathlib's `Submodule.eq_top_of_nonempty_interior'`). In a Baire module, the Baire category
theorem then shows that countably many proper closed submodules never cover the whole module.
This is the form in which Baire category enters gliding-hump arguments that choose a vector
avoiding countably many closed subspaces at once, such as the inductive constructions used for
separating ideals of Banach algebras.

## Main results

* `Submodule.exists_forall_notMem_of_isClosed`: a Baire topological module is not the union of
  countably many proper closed submodules.
-/

public section

open Filter Topology

namespace Submodule

variable {A M ι : Type*} [Ring A] [TopologicalSpace A] [NeBot (𝓝[{x : A | IsUnit x}] 0)]
  [AddCommGroup M] [Module A M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousSMul A M]
  [BaireSpace M] [Countable ι]

/-- **A Baire module is not a countable union of proper closed submodules.** Over a ring in
which zero is a limit of units, some vector of a Baire topological module lies outside each
member of a countable family of proper closed submodules. -/
theorem exists_forall_notMem_of_isClosed (p : ι → Submodule A M)
    (hc : ∀ i, IsClosed (p i : Set M)) (hp : ∀ i, p i ≠ ⊤) : ∃ x : M, ∀ i, x ∉ p i := by
  by_contra! h
  obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_closed hc
    (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr (h x))
  exact hp i ((p i).eq_top_of_nonempty_interior' hi)

end Submodule
