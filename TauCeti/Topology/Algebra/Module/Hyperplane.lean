/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Baire.Lemmas

/-!
# The complement of finitely many closed hyperplanes is dense

Let `M` be a topological module over a ring `R` in which `0` is a limit of units, for instance a
topological vector space over a nontrivially normed field
(`NormedField.nhdsWithin_isUnit_neBot`). A proper submodule of `M` has empty interior
(`Submodule.eq_top_of_nonempty_interior'`), so the complement of a proper closed submodule is a
dense open set, and so is the complement of finitely many of them (`Submodule.dense_iInter_compl`).
In particular the points at which finitely many nonzero continuous linear maps all take nonzero
values form a dense open set (`ContinuousLinearMap.dense_setOf_forall_apply_ne_zero`). This is the
generic-position statement behind choices of a parameter avoiding finitely many hyperplanes, such
as a regular element of a torus at which prescribed functionals take pairwise distinct values.
-/

public section

open Set Filter Topology

variable {R M ι : Type*} [Ring R] [TopologicalSpace R] [TopologicalSpace M] [AddCommGroup M]
  [ContinuousAdd M] [Module R M] [ContinuousSMul R M] [NeBot (𝓝[{x : R | IsUnit x}] 0)]

namespace Submodule

/-- **The complement of finitely many proper closed submodules is dense.** In a topological module
over a ring in which `0` is a limit of units, the points outside finitely many proper closed
submodules form a dense set; it is open, as a finite intersection of open sets. -/
theorem dense_iInter_compl [Finite ι] {p : ι → Submodule R M}
    (hcl : ∀ i, IsClosed (p i : Set M)) (hp : ∀ i, p i ≠ ⊤) :
    Dense (⋂ i, (p i : Set M)ᶜ) := by
  rw [← sInter_range]
  refine (finite_range _).dense_sInter ?_ ?_ <;> rintro _ ⟨i, rfl⟩
  · exact (hcl i).isOpen_compl
  · -- A proper submodule has empty interior.
    refine interior_eq_empty_iff_dense_compl.1 (not_nonempty_iff_eq_empty.1 fun h ↦ ?_)
    exact hp i ((p i).eq_top_of_nonempty_interior' h)

end Submodule

namespace ContinuousLinearMap

/-- **Finitely many nonzero continuous linear maps are simultaneously nonzero on a dense set.** For
finitely many nonzero continuous linear maps `fᵢ` on a topological module over a ring in which `0`
is a limit of units, with values in T1 spaces, the points at which every `fᵢ` is nonzero form a
dense set; it is open, as the complement of finitely many closed kernels. -/
theorem dense_setOf_forall_apply_ne_zero [Finite ι] {F : ι → Type*} [∀ i, AddCommGroup (F i)]
    [∀ i, Module R (F i)] [∀ i, TopologicalSpace (F i)] [∀ i, T1Space (F i)]
    {f : (i : ι) → M →L[R] F i} (hf : ∀ i, f i ≠ 0) :
    Dense {x | ∀ i, f i x ≠ 0} := by
  convert Submodule.dense_iInter_compl (p := fun i ↦ LinearMap.ker (f i : M →ₗ[R] F i))
    (fun i ↦ isClosed_singleton.preimage (f i).continuous)
    (fun i h ↦ hf i (coe_injective (LinearMap.ker_eq_top.1 h))) using 1
  ext
  simp

end ContinuousLinearMap
