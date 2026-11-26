/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Baire.Lemmas

/-!
# Avoiding closed submodules

Let `A` be a ring with a topology in which zero is a limit of units, for instance a nontrivially
normed field (`NormedField.nhdsWithin_isUnit_neBot`). A topological module over `A` has no proper
submodule with nonempty interior (Mathlib's `Submodule.eq_top_of_nonempty_interior'`), so the
complement of a proper closed submodule is a dense open set.

Finitely many such complements still meet in a dense open set. In particular the points at which
finitely many nonzero continuous linear maps all take nonzero values form a dense open set. This is
the generic-position statement behind choices of a parameter avoiding finitely many hyperplanes,
such as a regular element of a torus at which prescribed functionals take pairwise distinct values.

In a Baire module, the Baire category theorem shows moreover that countably many proper closed
submodules never cover the whole module. This is the form in which Baire category enters
gliding-hump arguments that choose a vector avoiding countably many closed subspaces at once, such
as the inductive constructions used for separating ideals of Banach algebras.

## Main results

* `Submodule.dense_iInter_compl`: the complement of finitely many proper closed submodules is
  dense.
* `ContinuousLinearMap.dense_setOf_forall_apply_ne_zero`: finitely many nonzero continuous linear
  maps are simultaneously nonzero on a dense set.
* `Submodule.exists_forall_notMem_of_isClosed`: a Baire topological module is not the union of
  countably many proper closed submodules.
-/

public section

open Set Filter Topology

variable {A M ι : Type*} [Ring A] [TopologicalSpace A] [NeBot (𝓝[{x : A | IsUnit x}] 0)]
  [AddCommGroup M] [Module A M] [TopologicalSpace M] [ContinuousAdd M] [ContinuousSMul A M]

namespace Submodule

/-- **The complement of finitely many proper closed submodules is dense.** In a topological module
over a ring in which `0` is a limit of units, the points outside finitely many proper closed
submodules form a dense set; it is open, as a finite intersection of open sets. -/
theorem dense_iInter_compl [Finite ι] {p : ι → Submodule A M}
    (hcl : ∀ i, IsClosed (p i : Set M)) (hp : ∀ i, p i ≠ ⊤) :
    Dense (⋂ i, (p i : Set M)ᶜ) := by
  rw [← sInter_range]
  refine (finite_range _).dense_sInter ?_ ?_ <;> rintro _ ⟨i, rfl⟩
  · exact (hcl i).isOpen_compl
  · -- A proper submodule has empty interior.
    refine interior_eq_empty_iff_dense_compl.1 (not_nonempty_iff_eq_empty.1 fun h ↦ ?_)
    exact hp i ((p i).eq_top_of_nonempty_interior' h)

/-- **A Baire module is not a countable union of proper closed submodules.** Over a ring in
which zero is a limit of units, some vector of a Baire topological module lies outside each
member of a countable family of proper closed submodules. -/
theorem exists_forall_notMem_of_isClosed [BaireSpace M] [Countable ι] (p : ι → Submodule A M)
    (hc : ∀ i, IsClosed (p i : Set M)) (hp : ∀ i, p i ≠ ⊤) : ∃ x : M, ∀ i, x ∉ p i := by
  by_contra! h
  obtain ⟨i, hi⟩ := nonempty_interior_of_iUnion_of_closed hc
    (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.mpr (h x))
  exact hp i ((p i).eq_top_of_nonempty_interior' hi)

end Submodule

namespace ContinuousLinearMap

/-- **Finitely many nonzero continuous linear maps are simultaneously nonzero on a dense set.** For
finitely many nonzero continuous linear maps `fᵢ` on a topological module over a ring in which `0`
is a limit of units, with values in T1 spaces, the points at which every `fᵢ` is nonzero form a
dense set; it is open, as the complement of finitely many closed kernels. -/
theorem dense_setOf_forall_apply_ne_zero [Finite ι] {F : ι → Type*} [∀ i, AddCommGroup (F i)]
    [∀ i, Module A (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, T1Space (F i)]
    {f : (i : ι) → M →L[A] F i} (hf : ∀ i, f i ≠ 0) :
    Dense {x | ∀ i, f i x ≠ 0} := by
  convert Submodule.dense_iInter_compl (p := fun i ↦ LinearMap.ker (f i : M →ₗ[A] F i))
    (fun i ↦ isClosed_singleton.preimage (f i).continuous)
    (fun i h ↦ hf i (coe_injective (LinearMap.ker_eq_top.1 h))) using 1
  ext
  simp

end ContinuousLinearMap
