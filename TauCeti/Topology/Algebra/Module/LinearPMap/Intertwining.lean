/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Domain-aware intertwining of partial linear maps

A continuous linear map `X` intertwines partial operators `A` and `B` when it sends
the domain of `A` into that of `B` and satisfies `X (A x) = B (X x)` there.
Equivalently, applying `X` to both coordinates sends the graph of `A` into the graph
of `B`. The relation composes and specializes to the usual bounded-operator equation.

Keeping domain transport in the relation is essential for passing intertwining identities
through inverses of unbounded operators. The resolvent characterization is developed in
`TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Intertwining`.

## References

K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Sections 1.1 and 2.2.
-/

public section

namespace TauCeti

variable {𝕜 E F G : Type*} [Ring 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]
  [AddCommGroup G] [TopologicalSpace G] [Module 𝕜 G]

/-- A continuous linear map intertwines two partial operators if it transports their
domains and their actions: `X A ⊆ B X`. -/
structure _root_.LinearPMap.Intertwines (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (X : E →L[𝕜] F) : Prop where
  /-- The intertwiner sends the source operator's domain into the target domain. -/
  mem_domain (x : A.domain) : X x ∈ B.domain
  /-- The actions agree on the source operator's domain. -/
  apply_eq (x : A.domain) : X (A x) = B ⟨X x, mem_domain x⟩

variable {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F} {C : G →ₗ.[𝕜] G}
  {X : E →L[𝕜] F} {Y : F →L[𝕜] G}

/-- Intertwining is equivalent to transporting every point of the source graph to
the target graph by applying the continuous linear map to both coordinates. -/
theorem _root_.LinearPMap.intertwines_iff_forall_mem_graph :
    A.Intertwines B X ↔ ∀ p ∈ A.graph, (X p.1, X p.2) ∈ B.graph := by
  constructor
  · intro h p hp
    obtain ⟨x, hx, hAx⟩ := A.mem_graph_iff.mp hp
    exact B.mem_graph_iff.mpr ⟨⟨X x, h.mem_domain x⟩,
      congrArg X hx, (h.apply_eq x).symm.trans (congrArg X hAx)⟩
  · intro h
    have hmem (x : A.domain) : X x ∈ B.domain := by
      obtain ⟨y, hy, _⟩ := B.mem_graph_iff.mp (h _ (A.mem_graph x))
      simp only at hy
      exact hy ▸ y.property
    refine ⟨hmem, fun x => ?_⟩
    obtain ⟨y, hy, hBy⟩ := B.mem_graph_iff.mp (h _ (A.mem_graph x))
    have heq : y = ⟨X x, hmem x⟩ := Subtype.ext hy
    exact hBy.symm.trans (congrArg B heq)

/-- The identity intertwines a partial operator with itself. -/
@[simp] theorem _root_.LinearPMap.intertwines_id (A : E →ₗ.[𝕜] E) :
    A.Intertwines A (ContinuousLinearMap.id 𝕜 E) where
  mem_domain x := x.property
  apply_eq _ := rfl

/-- Domain-aware intertwiners compose. -/
theorem _root_.LinearPMap.Intertwines.comp (hAB : A.Intertwines B X)
    (hBC : B.Intertwines C Y) : A.Intertwines C (Y ∘L X) where
  mem_domain x := hBC.mem_domain ⟨X x, hAB.mem_domain x⟩
  apply_eq x := by
    simp only [ContinuousLinearMap.comp_apply]
    rw [hAB.apply_eq x, hBC.apply_eq ⟨X x, hAB.mem_domain x⟩]

/-- For bounded everywhere-defined operators, domain-aware intertwining is exactly
the equality of the two continuous linear compositions. -/
@[simp] theorem _root_.ContinuousLinearMap.intertwines_toPMap_top_iff
    (S : E →L[𝕜] E) (T : F →L[𝕜] F) (X : E →L[𝕜] F) :
    ((S : E →ₗ[𝕜] E).toPMap ⊤).Intertwines
      ((T : F →ₗ[𝕜] F).toPMap ⊤) X ↔ X ∘L S = T ∘L X := by
  constructor
  · intro h
    ext x
    simpa [LinearMap.toPMap_apply] using h.apply_eq ⟨x, Submodule.mem_top⟩
  · intro h
    refine ⟨fun _ => Submodule.mem_top, fun x => ?_⟩
    rcases x with ⟨x, hx⟩
    simpa [LinearMap.toPMap_apply] using DFunLike.congr_fun h x

end TauCeti
