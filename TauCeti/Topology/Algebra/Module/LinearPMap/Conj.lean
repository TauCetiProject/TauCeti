/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.LinearPMap
public import TauCeti.LinearAlgebra.LinearPMap.Conj
public import TauCeti.Topology.Algebra.Module.LinearPMap.Intertwining

/-!
# Conjugating a partial linear map by a continuous linear equivalence

For a continuous linear equivalence `e : E ≃L[R] F`, the conjugate `A.conj e = e A e⁻¹` of a
partial linear map `A` on `E` (see `TauCeti.LinearAlgebra.LinearPMap.Conj`) has as graph the
preimage of the graph of `A` under the homeomorphism `e⁻¹ × e⁻¹`. Every notion defined through
the closure of the graph therefore passes through conjugation: closedness, closability, the
closure, density of the domain and graph cores. Taking `e⁻¹` instead of `e` gives the pullback
`e⁻¹ A e` of a partial map on `F` along `e`. Resolvents and spectra of conjugates are in
`TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Conj`.

Conjugation is characterised by intertwining: `A.conj e = B` exactly when `e` intertwines `A`
with `B` and `e⁻¹` intertwines `B` with `A`.

## Main results

* `LinearPMap.isClosed_conj_iff`, `LinearPMap.isClosable_conj_iff` and
  `LinearPMap.closure_conj`: closedness, closability and closures.
* `LinearPMap.dense_conj_domain_iff` and `LinearPMap.HasCore.conj`: dense domains and cores.
* `LinearPMap.conj_eq_iff_intertwines`: the intertwining characterisation.

## References

K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Sections 1.1 and 2.2.
-/

public section

namespace LinearPMap

section Ring

variable {R E F : Type*} [Ring R] [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F]

variable {A : E →ₗ.[R] E} (e : E ≃L[R] F)

/-- The graph of `e A e⁻¹` is, as a set, the preimage of the graph of `A` under `e⁻¹ × e⁻¹`. -/
theorem coe_graph_conj (A : E →ₗ.[R] E) :
    ((A.conj (e : E ≃ₗ[R] F)).graph : Set (F × F)) = Prod.map e.symm e.symm ⁻¹' A.graph := by
  ext p
  exact mem_graph_conj_iff

/-- The domain of a conjugate by a continuous linear equivalence is dense exactly when the domain
of the original partial map is. -/
@[simp]
theorem dense_conj_domain_iff :
    Dense ((A.conj (e : E ≃ₗ[R] F)).domain : Set F) ↔ Dense (A.domain : Set E) := by
  rw [conj_domain, Submodule.map_coe]
  exact e.toHomeomorph.isDenseEmbedding.dense_image

/-! ### Intertwining -/

/-- `A.conj e = B` exactly when `e` intertwines `A` with `B` and `e⁻¹` intertwines `B` with
`A`. -/
theorem conj_eq_iff_intertwines {B : F →ₗ.[R] F} :
    A.conj (e : E ≃ₗ[R] F) = B ↔
      A.Intertwines B (e : E →L[R] F) ∧ B.Intertwines A (e.symm : F →L[R] E) := by
  simp only [intertwines_iff_forall_mem_graph]
  refine ⟨?_, fun ⟨hAB, hBA⟩ ↦ eq_of_eq_graph (le_antisymm (fun p hp ↦ ?_) fun p hp ↦ ?_)⟩
  · rintro rfl
    refine ⟨fun p hp ↦ ?_, fun p hp ↦ mem_graph_conj_iff.1 hp⟩
    rw [mem_graph_conj_iff]
    simpa using hp
  · simpa using hAB _ (mem_graph_conj_iff.1 hp)
  · rw [mem_graph_conj_iff]
    exact hBA p hp

/-- `e` intertwines `A` with its conjugate `e A e⁻¹`. -/
theorem intertwines_conj (A : E →ₗ.[R] E) :
    A.Intertwines (A.conj (e : E ≃ₗ[R] F)) (e : E →L[R] F) :=
  ((conj_eq_iff_intertwines e).1 rfl).1

end Ring

/-! ### Closedness, closures and cores -/

section CommRing

variable {R E F : Type*} [CommRing R] [AddCommGroup E] [Module R E] [TopologicalSpace E]
  [AddCommGroup F] [Module R F] [TopologicalSpace F]

variable {A : E →ₗ.[R] E} (e : E ≃L[R] F)

/-- The conjugate of a closed partial map by a continuous linear equivalence is closed. -/
theorem IsClosed.conj (hA : A.IsClosed) : (A.conj (e : E ≃ₗ[R] F)).IsClosed := by
  rw [LinearPMap.IsClosed, coe_graph_conj]
  exact hA.preimage (e.symm.continuous.prodMap e.symm.continuous)

/-- A conjugate by a continuous linear equivalence is closed exactly when the original partial
map is. -/
@[simp]
theorem isClosed_conj_iff : (A.conj (e : E ≃ₗ[R] F)).IsClosed ↔ A.IsClosed :=
  ⟨fun h ↦ by simpa using h.conj e.symm, (·.conj e)⟩

variable [ContinuousAdd E] [ContinuousAdd F] [TopologicalSpace R] [ContinuousSMul R E]
  [ContinuousSMul R F]

/-- The closure of the graph of `e A e⁻¹` is the preimage of the closure of the graph of `A`. -/
private theorem coe_topologicalClosure_graph_conj (A : E →ₗ.[R] E) :
    ((A.conj (e : E ≃ₗ[R] F)).graph.topologicalClosure : Set (F × F)) =
      Prod.map e.symm e.symm ⁻¹' A.graph.topologicalClosure := by
  rw [Submodule.topologicalClosure_coe, Submodule.topologicalClosure_coe, coe_graph_conj]
  exact ((e.symm.toHomeomorph.prodCongr e.symm.toHomeomorph).preimage_closure _).symm

/-- The conjugate of a closable partial map by a continuous linear equivalence is closable. -/
theorem IsClosable.conj (hA : A.IsClosable) : (A.conj (e : E ≃ₗ[R] F)).IsClosable := by
  obtain ⟨B, hB⟩ := hA
  exact ⟨B.conj e, SetLike.coe_injective <| by
    rw [coe_topologicalClosure_graph_conj, hB, coe_graph_conj]⟩

/-- A conjugate by a continuous linear equivalence is closable exactly when the original partial
map is. -/
@[simp]
theorem isClosable_conj_iff : (A.conj (e : E ≃ₗ[R] F)).IsClosable ↔ A.IsClosable :=
  ⟨fun h ↦ by simpa using h.conj e.symm, (·.conj e)⟩

/-- The closure of `e A e⁻¹` is the conjugate of the closure of `A`. -/
@[simp]
theorem closure_conj (A : E →ₗ.[R] E) :
    (A.conj (e : E ≃ₗ[R] F)).closure = A.closure.conj e := by
  by_cases hA : A.IsClosable
  · refine eq_of_eq_graph (SetLike.coe_injective ?_)
    rw [← (hA.conj e).graph_closure_eq_closure_graph, coe_topologicalClosure_graph_conj,
      hA.graph_closure_eq_closure_graph, coe_graph_conj]
  · rw [closure_def' hA, closure_def' (mt (isClosable_conj_iff e).1 hA)]

/-- Conjugation by a continuous linear equivalence carries a core of `A` to a core of
`e A e⁻¹`. -/
theorem HasCore.conj {S : Submodule R E} (hS : A.HasCore S) :
    (A.conj (e : E ≃ₗ[R] F)).HasCore (S.map ((e : E ≃ₗ[R] F) : E →ₗ[R] F)) where
  le_domain := by
    rw [conj_domain]
    exact Submodule.map_mono hS.le_domain
  closure_eq := by rw [domRestrict_conj, closure_conj, hS.closure_eq]

end CommRing

end LinearPMap
