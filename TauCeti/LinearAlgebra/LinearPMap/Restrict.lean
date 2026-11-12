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

A partial linear map `A : E →ₛₗ.[σ] F` that maps `dom A ∩ U` into `V`, for submodules `U` of `E`
and `V` of `F`, restricts to a partial linear map `A.restrict hUV` from `U` to `V`, whose domain
consists of the vectors of `U` lying in `dom A` and whose action is that of `A`. For a linear `A`
the graph of the restriction is the preimage of the graph of `A` under the inclusion
`U × V → E × F`, which is how closedness passes to restrictions.

The main case is that of a submodule `U` invariant under a partial linear map `A : E →ₗ.[R] E`,
meaning that `A` maps `dom A ∩ U` into `U`; then `A.restrict hU.apply_mem` is a partial linear
map on `U`.

The restrictions to invariant submodules are the reduced parts of an unbounded operator along a
reducing subspace, the operation by which spectral questions about a self-adjoint operator split
along an orthogonal decomposition of the space.

## Main definitions

* `LinearPMap.IsInvariant A U`: the submodule `U` is invariant under the partial linear map `A`.
* `LinearPMap.restrict A hUV`: the restriction of `A` to a partial linear map from `U` to `V`.

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

variable {R S E F : Type*} [Ring R] [Ring S] {σ : R →+* S}
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module S F]

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

/-- The restriction of a partial linear map `A : E →ₛₗ.[σ] F` to submodules `U` of `E` and `V` of
`F` such that `A` maps every domain vector lying in `U` into `V`: the partial linear map from `U`
to `V` whose domain consists of the vectors of `U` lying in `dom A`, acting as `A`. For an
invariant submodule `U` of an endomorphism, this is `A.restrict hU.apply_mem`. -/
def restrict (A : E →ₛₗ.[σ] F) {U : Submodule R E} {V : Submodule S F}
    (hUV : ∀ x : A.domain, (x : E) ∈ U → A x ∈ V) : U →ₛₗ.[σ] V where
  domain := A.domain.comap U.subtype
  toFun := (A.toFun ∘ₛₗ U.subtype.restrict fun _ hx ↦ hx).codRestrict V fun x ↦ hUV _ x.1.2

section Restrict

variable {A : E →ₛₗ.[σ] F} {U : Submodule R E} {V : Submodule S F}
  (hUV : ∀ x : A.domain, (x : E) ∈ U → A x ∈ V)

/-- The domain of the restriction is the preimage of `dom A` under the inclusion of `U`. -/
theorem restrict_domain : (A.restrict hUV).domain = A.domain.comap U.subtype :=
  (rfl)

/-- A vector of `U` lies in the domain of the restriction exactly when it lies in `dom A`. -/
@[simp]
theorem mem_restrict_domain {x : U} : x ∈ (A.restrict hUV).domain ↔ (x : E) ∈ A.domain := by
  rw [restrict_domain, Submodule.mem_comap, Submodule.subtype_apply]

/-- The restriction acts as the original partial linear map. -/
@[simp]
theorem coe_restrict_apply (x : (A.restrict hUV).domain) :
    ((A.restrict hUV x : V) : F) = A ⟨x, (mem_restrict_domain hUV).1 x.2⟩ :=
  (rfl)

end Restrict

/-- The graph of the restriction is the preimage of the graph of `A` under the inclusion
`U × V → E × F`. -/
theorem graph_restrict [Module R F] {A : E →ₗ.[R] F} {U : Submodule R E} {V : Submodule R F}
    (hUV : ∀ x : A.domain, (x : E) ∈ U → A x ∈ V) :
    (A.restrict hUV).graph = A.graph.comap (U.subtype.prodMap V.subtype) := by
  ext ⟨x, y⟩
  simp only [mem_graph_iff, Submodule.mem_comap, LinearMap.prodMap_apply, Submodule.subtype_apply,
    Subtype.exists, mem_restrict_domain, Subtype.ext_iff, coe_restrict_apply]
  exact ⟨fun ⟨z, _, hz, hzx, hzy⟩ ↦ ⟨z, hz, hzx, hzy⟩,
    fun ⟨z, hz, hzx, hzy⟩ ↦ ⟨z, hzx ▸ x.2, hz, hzx, hzy⟩⟩

end LinearPMap
