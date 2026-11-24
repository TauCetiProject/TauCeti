/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearPMap

/-!
# Conjugating a partial linear map by a linear equivalence

For a partial linear map `A : E →ₗ.[R] E` and a linear equivalence `e : E ≃ₗ[R] F`, the
conjugate `A.conj e` is the partial linear map `e A e⁻¹` on `F`: its domain is the image
`e (dom A)` and it sends `e x` to `e (A x)`. This is the partial-map counterpart of Mathlib's
`LinearEquiv.conj` on endomorphisms. Read in the other direction, `A.conj e.symm` is the pullback
`e⁻¹ A e` of a partial map `A` on `F` along `e`.

Conjugation transports every structure defined through the graph, since the graph of `A.conj e`
is the image of the graph of `A` under `e × e`. It is functorial in `e`, preserves the extension
order and restrictions of the domain, and agrees with `LinearEquiv.conj` on everywhere-defined
maps.

The topological consequences (closedness, closures, cores) are in
`TauCeti.Topology.Algebra.Module.LinearPMap.Conj`, resolvents and spectra in
`TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Conj`, and unitary conjugation of adjoints
and of self-adjoint operators in `TauCeti.Analysis.InnerProductSpace.LinearPMap.Constructions`.

## Main definitions

* `LinearPMap.conj A e`: the conjugate `e A e⁻¹` of a partial linear map by a linear equivalence.

## Main results

* `LinearPMap.mem_conj_domain_iff` and `LinearPMap.conj_apply`: the domain and the action.
* `LinearPMap.graph_conj` and `LinearPMap.mem_graph_conj_iff`: the graph of a conjugate is the
  preimage of the graph of `A` under `e⁻¹ × e⁻¹`.
* `LinearPMap.conj_refl`, `LinearPMap.conj_trans`, `LinearPMap.conj_conj_symm`: functoriality.
* `LinearPMap.conj_le_conj_iff`: conjugation preserves and reflects extensions.
* `LinearPMap.conj_toPMap`: on everywhere-defined maps conjugation is `LinearEquiv.conj`.

## References

K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Sections 1.1 and 1.2.
-/

public section

namespace LinearPMap

variable {R E F G : Type*} [Ring R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [AddCommGroup G] [Module R G]

/-- The conjugate `e A e⁻¹` of a partial linear map `A` on `E` by a linear equivalence
`e : E ≃ₗ[R] F`: the partial linear map on `F` with domain `e (dom A)` sending `e x` to
`e (A x)`. -/
def conj (A : E →ₗ.[R] E) (e : E ≃ₗ[R] F) : F →ₗ.[R] F where
  domain := A.domain.map (e : E →ₗ[R] F)
  toFun := (e : E →ₗ[R] F) ∘ₗ A.toFun ∘ₗ ((e.submoduleMap A.domain).symm : _ →ₗ[R] A.domain)

variable {A B : E →ₗ.[R] E} {e : E ≃ₗ[R] F}

/-- The domain of the conjugate is the image of the domain. -/
theorem conj_domain (A : E →ₗ.[R] E) (e : E ≃ₗ[R] F) :
    (A.conj e).domain = A.domain.map (e : E →ₗ[R] F) :=
  (rfl)

/-- A vector lies in the domain of `e A e⁻¹` exactly when its preimage under `e` lies in the
domain of `A`. -/
@[simp]
theorem mem_conj_domain_iff {x : F} : x ∈ (A.conj e).domain ↔ e.symm x ∈ A.domain := by
  rw [conj_domain, Submodule.mem_map_equiv]

/-- `e` maps the domain of `A` into the domain of `e A e⁻¹`. -/
theorem map_mem_conj_domain (x : A.domain) : e x ∈ (A.conj e).domain := by
  simp

/-- The conjugate acts as `x ↦ e (A (e⁻¹ x))`. -/
@[simp]
theorem conj_apply (x : (A.conj e).domain) :
    A.conj e x = e (A ⟨e.symm x, mem_conj_domain_iff.1 x.property⟩) :=
  (rfl)

/-- The conjugate sends `e x` to `e (A x)`. -/
theorem conj_apply_map (x : A.domain) {h : e x ∈ (A.conj e).domain} :
    A.conj e ⟨e x, h⟩ = e (A x) := by
  rw [conj_apply]
  congr 2
  exact Subtype.ext (e.symm_apply_apply _)

/-- A pair lies on the graph of `e A e⁻¹` exactly when its image under `e⁻¹ × e⁻¹` lies on the
graph of `A`. -/
theorem mem_graph_conj_iff {p : F × F} :
    p ∈ (A.conj e).graph ↔ (e.symm p.1, e.symm p.2) ∈ A.graph := by
  simp only [mem_graph_iff, Subtype.exists, mem_conj_domain_iff, conj_apply, exists_and_left,
    exists_eq_left]
  exact exists_congr fun _ ↦ e.eq_symm_apply.symm

/-- The graph of `e A e⁻¹` is the preimage of the graph of `A` under `e⁻¹ × e⁻¹`. -/
theorem graph_conj (A : E →ₗ.[R] E) (e : E ≃ₗ[R] F) :
    (A.conj e).graph = A.graph.comap ((e.symm : F →ₗ[R] E).prodMap (e.symm : F →ₗ[R] E)) := by
  ext p
  exact mem_graph_conj_iff

/-- Conjugating by the identity does nothing. -/
@[simp]
theorem conj_refl (A : E →ₗ.[R] E) : A.conj (LinearEquiv.refl R E) = A :=
  eq_of_eq_graph <| by ext p; rw [mem_graph_conj_iff]; simp

/-- Conjugating by a composite is conjugating successively. -/
theorem conj_trans (A : E →ₗ.[R] E) (e : E ≃ₗ[R] F) (e' : F ≃ₗ[R] G) :
    A.conj (e.trans e') = (A.conj e).conj e' :=
  eq_of_eq_graph <| by
    ext p
    rw [mem_graph_conj_iff, mem_graph_conj_iff, mem_graph_conj_iff]
    simp

/-- Conjugating by `e` and then by `e⁻¹` recovers the original partial map. -/
@[simp]
theorem conj_conj_symm (A : E →ₗ.[R] E) (e : E ≃ₗ[R] F) : (A.conj e).conj e.symm = A := by
  rw [← conj_trans, LinearEquiv.self_trans_symm, conj_refl]

/-- Conjugating by `e⁻¹` and then by `e` recovers the original partial map. -/
@[simp]
theorem conj_symm_conj (B : F →ₗ.[R] F) (e : E ≃ₗ[R] F) : (B.conj e.symm).conj e = B := by
  simpa using conj_conj_symm B e.symm

/-- Conjugation by `e` is injective. -/
theorem conj_injective (e : E ≃ₗ[R] F) : Function.Injective fun A : E →ₗ.[R] E ↦ A.conj e :=
  Function.LeftInverse.injective (g := fun B ↦ B.conj e.symm) (conj_conj_symm · e)

/-- Two partial maps have the same conjugate exactly when they are equal. -/
@[simp]
theorem conj_inj : A.conj e = B.conj e ↔ A = B :=
  (conj_injective e).eq_iff

/-- A conjugate of `A` equals `B` exactly when `A` is the conjugate of `B` by the inverse. -/
theorem conj_eq_iff_eq_conj_symm {B : F →ₗ.[R] F} : A.conj e = B ↔ A = B.conj e.symm := by
  rw [← conj_inj (e := e), conj_symm_conj]

/-- Conjugation preserves and reflects extensions of partial maps. -/
@[simp]
theorem conj_le_conj_iff : A.conj e ≤ B.conj e ↔ A ≤ B := by
  rw [← le_graph_iff, graph_conj, graph_conj, Submodule.comap_le_comap_iff_of_surjective,
    le_graph_iff]
  exact e.symm.surjective.prodMap e.symm.surjective

/-- Restricting the domain of a conjugate to the image of a submodule is conjugating the
restriction. -/
theorem domRestrict_conj (A : E →ₗ.[R] E) (e : E ≃ₗ[R] F) (S : Submodule R E) :
    (A.conj e).domRestrict (S.map (e : E →ₗ[R] F)) = (A.domRestrict S).conj e := by
  refine ext ?_ fun x hx hx' ↦ ?_
  · rw [domRestrict_domain, conj_domain, conj_domain, domRestrict_domain,
      Submodule.map_inf _ e.injective]
  · -- Both sides restrict `A.conj e`, so they agree with it at `x`.
    let y : (A.conj e).domain := ⟨x, domRestrict_le.1 hx⟩
    exact (domRestrict_le.2 (y := y) rfl).trans ((conj_le_conj_iff.2 domRestrict_le).2 rfl).symm

/-- On an everywhere-defined map conjugation is `LinearEquiv.conjRingEquiv`, with the domain
transported along `e`. -/
theorem conj_toPMap (f : Module.End R E) (p : Submodule R E) (e : E ≃ₗ[R] F) :
    (f.toPMap p).conj e = (e.conjRingEquiv f).toPMap (p.map (e : E →ₗ[R] F)) :=
  ext (conj_domain _ _) fun _ _ _ ↦ by
    simp [conj_apply, LinearMap.toPMap_apply]

end LinearPMap
