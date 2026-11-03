/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import TauCeti.Combinatorics.Quiver.UnderlyingGraph

/-!
# Directed and zigzag reachability in a quiver

A vertex `b` of a quiver is reachable from `a` (`Quiver.Reachable a b`) when some directed path
runs from `a` to `b`. This is the reflexive transitive closure of the relation "some arrow runs
from `x` to `y`", which turns statements about reachability into statements about relations,
where the arrows themselves no longer appear.

Two vertices lie in the same weakly connected component when a zigzag of arrows, each traversed
in either direction, joins them, that is, a path in the symmetrized quiver. Since loops and the
multiplicity of arrows play no role, this is reachability in the simple graph underlying the
quiver (`TauCeti.Quiver.underlyingGraph`), and the weakly connected components of a quiver are the
connected components of its underlying graph.

## Main results

* `Quiver.reachable_iff_reflTransGen`: directed reachability is the reflexive transitive closure
  of being joined by an arrow.
* `TauCeti.Quiver.nonempty_path_symmetrify_iff_reachable`: two vertices are joined by a zigzag of
  arrows exactly when they are reachable in the underlying graph.
* `TauCeti.Quiver.weaklyConnectedComponentEquiv`: the weakly connected components of a quiver are
  the connected components of its underlying graph.
-/

public section

universe u v

namespace Quiver

variable {V : Type u} [Quiver.{v} V] {a b : V}

/-- Directed reachability is the reflexive transitive closure of the relation "some arrow runs
from `x` to `y`". -/
theorem reachable_iff_reflTransGen :
    Reachable a b ↔ Relation.ReflTransGen (fun x y : V ↦ Nonempty (x ⟶ y)) a b := by
  constructor
  · rintro ⟨p⟩
    induction p with
    | nil => rfl
    | cons _ e ih => exact ih.tail ⟨e⟩
  · intro h
    induction h with
    | refl => rfl
    | tail _ he ih => exact he.elim fun e ↦ ih.trans e.reachable

end Quiver

namespace TauCeti.Quiver

open _root_.Quiver

variable {V : Type u} [_root_.Quiver.{v} V] {a b : V}

/-- Two vertices are joined by a zigzag of arrows, a path in the symmetrized quiver, exactly when
they are reachable in the underlying graph. -/
theorem nonempty_path_symmetrify_iff_reachable :
    Nonempty (@Path (Symmetrify V) _ a b) ↔ (underlyingGraph V).Reachable a b := by
  refine (reachable_iff_reflTransGen (V := Symmetrify V)).trans ?_
  rw [SimpleGraph.reachable_iff_reflTransGen, ← Relation.transGen_reflGen,
    ← Relation.transGen_reflGen]
  -- Both reflexive closures relate `x` and `y` when `x = y` or an arrow joins them either way.
  -- An arrow of the symmetrized quiver from `x` to `y` is an arrow from `x` to `y` or back.
  have h (x y : V) : Relation.ReflGen (fun x y : V ↦ Nonempty ((x ⟶ y) ⊕ (y ⟶ x))) x y ↔
      Relation.ReflGen (underlyingGraph V).Adj x y := by
    simp only [Relation.reflGen_iff, underlyingGraph_adj, nonempty_sum]
    tauto
  exact ⟨fun hab ↦ Relation.TransGen.mono (fun x y ↦ (h x y).1) a b hab,
    fun hab ↦ Relation.TransGen.mono (fun x y ↦ (h x y).2) a b hab⟩

/-- Two vertices lie in the same weakly connected component exactly when they are reachable in the
underlying graph. -/
theorem weaklyConnectedComponent_mk_eq_mk_iff :
    WeaklyConnectedComponent.mk a = WeaklyConnectedComponent.mk b ↔
      (underlyingGraph V).Reachable a b :=
  (WeaklyConnectedComponent.eq a b).trans nonempty_path_symmetrify_iff_reachable

variable (V) in
/-- The weakly connected components of a quiver are the connected components of its underlying
graph. -/
def weaklyConnectedComponentEquiv :
    WeaklyConnectedComponent V ≃ (underlyingGraph V).ConnectedComponent :=
  Quot.congrRight fun _ _ ↦ nonempty_path_symmetrify_iff_reachable

@[simp]
theorem weaklyConnectedComponentEquiv_mk (a : V) :
    weaklyConnectedComponentEquiv V (WeaklyConnectedComponent.mk a) =
      (underlyingGraph V).connectedComponentMk a :=
  (rfl)

@[simp]
theorem weaklyConnectedComponentEquiv_symm_mk (a : V) :
    (weaklyConnectedComponentEquiv V).symm ((underlyingGraph V).connectedComponentMk a) =
      WeaklyConnectedComponent.mk a :=
  (rfl)

end TauCeti.Quiver
