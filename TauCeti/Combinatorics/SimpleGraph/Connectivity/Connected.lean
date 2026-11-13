/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connectedness and connected components

A graph on a well-founded order in which every vertex other than a fixed root has a neighbour
below it is connected: well-founded induction walks every vertex down to the root. Numbering the
vertices of a diagram by `Fin n` so that every nonzero vertex has a neighbour with a smaller
number is what makes connectedness of the Dynkin diagrams, finite and affine alike, a short check.

Graphs with the same reachability relation have canonically equivalent connected components.
Deleting any vertex leaves each connected component not containing it as a single component.

## Main results

* `SimpleGraph.connected_of_exists_adj_lt`: a graph on a type with a well-founded `<`, in which
  every vertex other than `v₀` has an adjacent vertex below it, is connected.
* `SimpleGraph.ConnectedComponent.natCard_fiber_map_induce_compl_singleton_eq_one`: deleting a
  vertex leaves each other connected component intact.
-/

public section

namespace SimpleGraph

/-- Graphs on the same vertices with equal reachability have equivalent connected components,
with the equivalence preserving the component of each vertex. -/
def connectedComponentEquivOfReachableEq {V : Type*} (G : SimpleGraph V)
    {H : SimpleGraph V} (h : G.Reachable = H.Reachable) :
    G.ConnectedComponent ≃ H.ConnectedComponent where
  toFun := ConnectedComponent.lift H.connectedComponentMk fun _ _ p _ =>
    ConnectedComponent.sound (h ▸ p.reachable)
  invFun := ConnectedComponent.lift G.connectedComponentMk fun _ _ p _ =>
    ConnectedComponent.sound (h.symm ▸ p.reachable)
  left_inv c := c.ind fun _ => by simp
  right_inv c := c.ind fun _ => by simp

@[simp] theorem connectedComponentEquivOfReachableEq_mk {V : Type*} (G : SimpleGraph V)
    {H : SimpleGraph V} (h : G.Reachable = H.Reachable) (v : V) :
    G.connectedComponentEquivOfReachableEq h (G.connectedComponentMk v) =
      H.connectedComponentMk v := (rfl)

@[simp] theorem connectedComponentEquivOfReachableEq_symm_mk {V : Type*} (G : SimpleGraph V)
    {H : SimpleGraph V} (h : G.Reachable = H.Reachable) (v : V) :
    (G.connectedComponentEquivOfReachableEq h).symm (H.connectedComponentMk v) =
      G.connectedComponentMk v := (rfl)

/-! ### Components after deleting a vertex -/

/-- Deleting a vertex leaves every other connected component intact: exactly one component of the
graph with `v` deleted maps onto each component not containing `v`. -/
theorem ConnectedComponent.natCard_fiber_map_induce_compl_singleton_eq_one
    {V : Type*} {G : SimpleGraph V} {v : V} {C : G.ConnectedComponent}
    (hC : C ≠ G.connectedComponentMk v) :
    Nat.card {D : (G.induce ({v}ᶜ : Set V)).ConnectedComponent //
      D.map (Embedding.induce ({v}ᶜ : Set V)).toHom = C} = 1 := by
  classical
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · constructor
    intro D E
    obtain ⟨x, hxD⟩ := D.1.exists_rep
    obtain ⟨y, hyE⟩ := E.1.exists_rep
    have hxC : G.connectedComponentMk (x : V) = C :=
      (ConnectedComponent.map_mk (Embedding.induce ({v}ᶜ : Set V)).toHom x).symm.trans
        ((congrArg (ConnectedComponent.map
          (Embedding.induce ({v}ᶜ : Set V)).toHom) hxD).trans D.2)
    have hyC : G.connectedComponentMk (y : V) = C :=
      (ConnectedComponent.map_mk (Embedding.induce ({v}ᶜ : Set V)).toHom y).symm.trans
        ((congrArg (ConnectedComponent.map
          (Embedding.induce ({v}ᶜ : Set V)).toHom) hyE).trans E.2)
    obtain ⟨p⟩ := ConnectedComponent.exact (hxC.trans hyC.symm)
    have hvp : v ∉ p.support := by
      intro hv
      have hxv : G.connectedComponentMk (x : V) = G.connectedComponentMk v :=
        ConnectedComponent.sound (p.takeUntil v hv).reachable
      exact hC (hxC.symm.trans hxv)
    have hxy : (G.induce ({v}ᶜ : Set V)).Reachable x y :=
      (p.induce ({v}ᶜ : Set V) fun z hz ↦
        Set.mem_compl_singleton_iff.mpr fun hzv ↦ hvp (hzv ▸ hz)).reachable
    apply Subtype.ext
    exact hxD.symm.trans ((ConnectedComponent.sound hxy).trans hyE)
  · obtain ⟨x, hxC⟩ := C.exists_rep
    have hxv : x ≠ v := by
      intro h
      subst x
      exact hC hxC.symm
    let x' : ↑({v}ᶜ : Set V) := ⟨x, Set.mem_compl_singleton_iff.mpr hxv⟩
    refine ⟨⟨(G.induce ({v}ᶜ : Set V)).connectedComponentMk x', ?_⟩⟩
    rw [ConnectedComponent.map_mk]
    exact hxC

variable {V : Type*} [LT V] [WellFoundedLT V] {G : SimpleGraph V}

/-- **A graph on a well-founded order in which every vertex other than `v₀` has a neighbour below
it is connected.** Every vertex reaches `v₀` by descending along such neighbours. -/
theorem connected_of_exists_adj_lt (v₀ : V) (h : ∀ v ≠ v₀, ∃ w < v, G.Adj w v) :
    G.Connected := by
  refine (connected_iff_exists_forall_reachable G).2 ⟨v₀, fun v ↦ ?_⟩
  induction v using WellFoundedLT.induction with
  | ind v ih =>
    rcases eq_or_ne v v₀ with rfl | hv
    · rfl
    · obtain ⟨w, hwv, hadj⟩ := h v hv
      exact (ih w hwv).trans hadj.reachable

end SimpleGraph
