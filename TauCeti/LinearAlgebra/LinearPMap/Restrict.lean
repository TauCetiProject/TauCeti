/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Invariant submodules and restrictions of partial linear maps

A submodule `U` is invariant under a partial linear map `A : E →ₗ.[R] E` when `A` maps
`dom A ∩ U` into `U`. Such a map then restricts to a partial linear map `A.restrict hU` on `U`,
whose domain consists of the vectors of `U` lying in `dom A` and whose action is that of `A`.
The graph of the restriction is the preimage of the graph of `A` under the inclusion
`U × U → E × E`, which is how closedness passes to restrictions.

These restrictions are the reduced parts of an unbounded operator along a reducing subspace, the
operation by which spectral questions about a self-adjoint operator split along an orthogonal
decomposition of the space.

## Main definitions

* `LinearPMap.IsInvariant A U`: the submodule `U` is invariant under the partial linear map `A`.
* `LinearPMap.restrict A hU`: the restriction of `A` to an invariant submodule `U`.

## Main results

* `LinearPMap.mem_restrict_domain` and `LinearPMap.coe_restrict_apply`: the domain and the action
  of a restriction.
* `LinearPMap.graph_restrict`: the graph of a restriction is the preimage of the graph of `A`.
* `LinearPMap.isInvariant_toPMap_top_iff`: for an everywhere-defined map, invariance is membership
  in `Module.End.invtSubmodule`.

## References

K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Section 1.4.
-/

public section

namespace LinearPMap

variable {R E : Type*} [Ring R] [AddCommGroup E] [Module R E]

/-- A submodule `U` is invariant under a partial linear map `A` when `A` maps every domain vector
lying in `U` back into `U`, that is, `A (dom A ∩ U) ⊆ U`. -/
def IsInvariant (A : E →ₗ.[R] E) (U : Submodule R E) : Prop :=
  ∀ x : A.domain, (x : E) ∈ U → A x ∈ U

/-- Unfold `LinearPMap.IsInvariant`. -/
theorem isInvariant_iff {A : E →ₗ.[R] E} {U : Submodule R E} :
    A.IsInvariant U ↔ ∀ x : A.domain, (x : E) ∈ U → A x ∈ U :=
  Iff.rfl

/-- An invariant submodule contains the image of each of its domain vectors. -/
theorem IsInvariant.apply_mem {A : E →ₗ.[R] E} {U : Submodule R E} (hU : A.IsInvariant U)
    (x : A.domain) (hx : (x : E) ∈ U) : A x ∈ U :=
  hU x hx

/-- For an everywhere-defined linear map, invariance of a submodule in the sense of partial maps is
invariance in the sense of `Module.End.invtSubmodule`. -/
theorem isInvariant_toPMap_top_iff (f : Module.End R E) (U : Submodule R E) :
    (f.toPMap ⊤).IsInvariant U ↔ U ∈ f.invtSubmodule := by
  rw [Module.End.mem_invtSubmodule]
  exact ⟨fun h x hx ↦ h ⟨x, Submodule.mem_top⟩ hx, fun h x hx ↦ h hx⟩

/-- The restriction of a partial linear map `A` to an invariant submodule `U`: the partial linear
map on `U` whose domain consists of the vectors of `U` lying in `dom A`, acting as `A`. -/
def restrict (A : E →ₗ.[R] E) {U : Submodule R E} (hU : A.IsInvariant U) : U →ₗ.[R] U where
  domain := A.domain.comap U.subtype
  toFun := (A.toFun ∘ₗ U.subtype.restrict fun _ hx ↦ hx).codRestrict U fun x ↦ hU _ x.1.2

variable {A : E →ₗ.[R] E} {U : Submodule R E} (hU : A.IsInvariant U)

/-- The domain of the restriction is the preimage of `dom A` under the inclusion of `U`. -/
theorem restrict_domain : (A.restrict hU).domain = A.domain.comap U.subtype :=
  (rfl)

/-- A vector of `U` lies in the domain of the restriction exactly when it lies in `dom A`. -/
@[simp]
theorem mem_restrict_domain {x : U} : x ∈ (A.restrict hU).domain ↔ (x : E) ∈ A.domain := by
  rw [restrict_domain, Submodule.mem_comap, Submodule.subtype_apply]

/-- The restriction acts as the original partial linear map. -/
@[simp]
theorem coe_restrict_apply (x : (A.restrict hU).domain) :
    ((A.restrict hU x : U) : E) = A ⟨x, (mem_restrict_domain hU).1 x.2⟩ :=
  (rfl)

/-- The graph of the restriction is the preimage of the graph of `A` under the inclusion
`U × U → E × E`. -/
theorem graph_restrict :
    (A.restrict hU).graph = A.graph.comap (U.subtype.prodMap U.subtype) := by
  ext ⟨x, y⟩
  simp only [mem_graph_iff, Submodule.mem_comap, LinearMap.prodMap_apply, Submodule.subtype_apply,
    Subtype.exists, mem_restrict_domain]
  constructor
  · rintro ⟨z, hzU, hz, rfl, rfl⟩
    exact ⟨z, hz, rfl,
      (coe_restrict_apply hU ⟨⟨z, hzU⟩, (mem_restrict_domain hU).2 hz⟩).symm⟩
  · rintro ⟨z, hz, rfl, hzy⟩
    exact ⟨x, x.2, hz, rfl, Subtype.ext ((coe_restrict_apply hU _).trans hzy)⟩

end LinearPMap
