/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Rel
public import Mathlib.LinearAlgebra.Prod

/-!
# Composition of linear relations

A submodule of `M × N` is a linear relation from `M` to `N`. Relational composition
eliminates the shared coordinate. It is associative, has the diagonal as identity,
and agrees with composition of linear maps on graphs. Unlike a partial linear map,
a linear relation can have several outputs for one input. The underlying set of the
composite is Mathlib's `SetRel.comp` of the underlying sets, and the laws below are
transported from the corresponding `SetRel` lemmas.

This operation is used for the tangent spaces of composed Lagrangian correspondences.
-/

public section

namespace Submodule

variable {R M N P Q : Type*} [Semiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

open scoped SetRel

/-- Compose linear relations by eliminating the common coordinate. The first relation
goes from `M` to `N` and the second from `N` to `P`. The underlying set is the
`SetRel` composite of the underlying sets. -/
def relComp (L : Submodule R (M × N)) (K : Submodule R (N × P)) :
    Submodule R (M × P) where
  carrier := (L : SetRel M N) ○ (K : SetRel N P)
  zero_mem' := ⟨0, L.zero_mem, K.zero_mem⟩
  add_mem' := by
    rintro x z ⟨y, hy, hy'⟩ ⟨w, hw, hw'⟩
    exact ⟨y + w, L.add_mem hy hw, K.add_mem hy' hw'⟩
  smul_mem' := by
    rintro c x ⟨y, hy, hy'⟩
    exact ⟨c • y, L.smul_mem c hy, K.smul_mem c hy'⟩

/-- The underlying relation of a composite is the `SetRel` composite. -/
@[simp]
theorem coe_relComp (L : Submodule R (M × N)) (K : Submodule R (N × P)) :
    (L.relComp K : SetRel M P) = (L : SetRel M N) ○ (K : SetRel N P) := by
  ext
  exact Iff.rfl

/-- A pair belongs to the composite exactly when it has a shared intermediate value. -/
@[simp]
theorem mem_relComp {L : Submodule R (M × N)} {K : Submodule R (N × P)} {x : M × P} :
    x ∈ L.relComp K ↔ ∃ y, (x.1, y) ∈ L ∧ (y, x.2) ∈ K := Iff.rfl

/-- Composition of linear relations is associative. -/
theorem relComp_assoc (L : Submodule R (M × N)) (K : Submodule R (N × P))
    (J : Submodule R (P × Q)) :
    (L.relComp K).relComp J = L.relComp (K.relComp J) :=
  SetLike.coe_injective <| by
    rw [coe_relComp, coe_relComp, coe_relComp, coe_relComp]
    exact SetRel.comp_assoc _ _ _

/-- The underlying relation of the graph of a linear map is the graph of the function. -/
@[simp]
theorem _root_.LinearMap.coe_graph (f : M →ₗ[R] N) :
    (f.graph : SetRel M N) = Function.graph f := by
  ext x
  exact eq_comm

/-- The diagonal is a right identity for composition of linear relations. -/
@[simp]
theorem relComp_graph_id (L : Submodule R (M × N)) :
    L.relComp (LinearMap.id : N →ₗ[R] N).graph = L :=
  SetLike.coe_injective <| by
    rw [coe_relComp, LinearMap.coe_graph]
    exact SetRel.comp_id _

/-- The diagonal is a left identity for composition of linear relations. -/
@[simp]
theorem graph_id_relComp (L : Submodule R (M × N)) :
    (LinearMap.id : M →ₗ[R] M).graph.relComp L = L :=
  SetLike.coe_injective <| by
    rw [coe_relComp, LinearMap.coe_graph]
    exact SetRel.id_comp _

/-- Composing the graphs of linear maps gives the graph of their composite. -/
@[simp]
theorem _root_.LinearMap.graph_relComp_graph (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    f.graph.relComp g.graph = (g.comp f).graph :=
  SetLike.coe_injective <| by
    rw [coe_relComp, LinearMap.coe_graph, LinearMap.coe_graph, LinearMap.coe_graph]
    exact (Function.graph_comp g f).symm

end Submodule
