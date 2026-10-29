/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Prod

/-!
# Composition of linear relations

A submodule of `M × N` is a linear relation from `M` to `N`. Relational composition
eliminates the shared coordinate. It is associative, has the diagonal as identity,
and agrees with composition of linear maps on graphs. Unlike a partial linear map,
a linear relation can have several outputs for one input.

This operation is used for the tangent spaces of composed Lagrangian correspondences.
-/

public section

namespace Submodule

variable {R M N P Q : Type*} [Semiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

/-- Compose linear relations by eliminating the common coordinate. The first relation
goes from `M` to `N` and the second from `N` to `P`. -/
def relComp (L : Submodule R (M × N)) (K : Submodule R (N × P)) :
    Submodule R (M × P) where
  carrier := {x | ∃ y, (x.1, y) ∈ L ∧ (y, x.2) ∈ K}
  zero_mem' := ⟨0, L.zero_mem, K.zero_mem⟩
  add_mem' := by
    rintro x z ⟨y, hy, hy'⟩ ⟨w, hw, hw'⟩
    exact ⟨y + w, L.add_mem hy hw, K.add_mem hy' hw'⟩
  smul_mem' := by
    rintro c x ⟨y, hy, hy'⟩
    exact ⟨c • y, L.smul_mem c hy, K.smul_mem c hy'⟩

/-- A pair belongs to the composite exactly when it has a shared intermediate value. -/
@[simp]
theorem mem_relComp {L : Submodule R (M × N)} {K : Submodule R (N × P)} {x : M × P} :
    x ∈ L.relComp K ↔ ∃ y, (x.1, y) ∈ L ∧ (y, x.2) ∈ K := Iff.rfl

/-- Composition of linear relations is associative. -/
theorem relComp_assoc (L : Submodule R (M × N)) (K : Submodule R (N × P))
    (J : Submodule R (P × Q)) :
    (L.relComp K).relComp J = L.relComp (K.relComp J) := by
  ext x
  simp only [mem_relComp]
  constructor
  · rintro ⟨z, ⟨y, hy, hz⟩, hw⟩
    exact ⟨y, hy, z, hz, hw⟩
  · rintro ⟨y, hy, z, hz, hw⟩
    exact ⟨z, ⟨y, hy, hz⟩, hw⟩

/-- The diagonal is a right identity for composition of linear relations. -/
@[simp]
theorem relComp_graph_id (L : Submodule R (M × N)) :
    L.relComp (LinearMap.id : N →ₗ[R] N).graph = L := by
  ext x
  simp [LinearMap.mem_graph_iff]

/-- The diagonal is a left identity for composition of linear relations. -/
@[simp]
theorem graph_id_relComp (L : Submodule R (M × N)) :
    (LinearMap.id : M →ₗ[R] M).graph.relComp L = L := by
  ext x
  simp [LinearMap.mem_graph_iff]

/-- Composing the graphs of linear maps gives the graph of their composite. -/
@[simp]
theorem _root_.LinearMap.graph_relComp_graph (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    f.graph.relComp g.graph = (g.comp f).graph := by
  ext x
  simp [LinearMap.mem_graph_iff]

end Submodule
