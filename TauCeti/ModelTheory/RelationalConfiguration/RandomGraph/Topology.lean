/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.GDelta.Basic
public import TauCeti.Combinatorics.SimpleGraph.ExtensionProperty
public import TauCeti.Combinatorics.SimpleGraph.RelationalConfiguration
public import TauCeti.ModelTheory.RelationalConfiguration.Topology
import TauCeti.ModelTheory.Scott.RandomGraph

/-!
# The Rado graph isomorphism class is Gδ

On a countable vertex type, the simple graphs with the extension property form a Gδ set in
the topology induced by the graph coding. Each extension axiom asks for a vertex satisfying
a finite adjacency pattern, so its satisfaction set is open. Taking all the extension axioms
together gives a countable intersection of open sets. On `ℕ` these axioms characterize the
Rado graph up to isomorphism.
-/

public section

open TauCeti.RelationalConfiguration

namespace SimpleGraph

/-- In the topology induced by the relational configuration of a graph, the extension property
defines a Gδ set on a countable vertex type. -/
theorem isGδ_setOf_hasExtensionProperty {V : Type*} [Countable V] :
    @IsGδ (SimpleGraph V) (.induced toRelationalConfiguration inferInstance)
      {G | G.HasExtensionProperty} := by
  classical
  let : TopologicalSpace (SimpleGraph V) := .induced toRelationalConfiguration inferInstance
  have hcontinuous : Continuous (toRelationalConfiguration (V := V)) := continuous_induced_dom
  have hadj (z u : V) : IsClopen {G : SimpleGraph V | G.Adj z u} := by
    simpa only [Set.preimage_ofPred_eq, eval_toRelationalConfiguration_adjAtom, decide_eq_true_eq]
      using (isClopen_setOf_eval (adjAtom z u) true).preimage hcontinuous
  simp only [hasExtensionProperty_def, Set.ofPred_forall]
  refine .iInter fun s => .iInter fun t => .iInter fun _ => IsOpen.isGδ ?_
  simp only [Set.ofPred_exists, Set.ofPred_and]
  refine isOpen_iUnion fun z => isOpen_const.inter (IsOpen.inter ?_ ?_)
  · simp only [Set.ofPred_forall]
    exact isOpen_biInter_finset fun u _ => (hadj z u).isOpen
  · simp only [Set.ofPred_forall]
    exact isOpen_biInter_finset fun w _ => (hadj z w).isClosed.isOpen_compl

end SimpleGraph

namespace TauCeti

/-- The isomorphism class of the Rado graph is Gδ in the topology on `SimpleGraph ℕ` induced by
`SimpleGraph.toRelationalConfiguration`. -/
theorem isGδ_setOf_nonempty_iso_radoGraph :
    @IsGδ (SimpleGraph ℕ) (.induced SimpleGraph.toRelationalConfiguration inferInstance)
      {G | Nonempty (G ≃g radoGraph)} := by
  simpa only [nonempty_iso_radoGraph_iff] using
    (SimpleGraph.isGδ_setOf_hasExtensionProperty (V := ℕ))

end TauCeti
