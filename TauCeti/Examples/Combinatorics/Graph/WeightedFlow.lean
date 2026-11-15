/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

import Mathlib.Tactic.FinCases
public import TauCeti.Combinatorics.Graph.Connectivity.Flow
public import TauCeti.Combinatorics.Graph.Union

/-!
# A bidirected flow on a weighted multigraph

This example exercises the multigraph flow interface on two parallel edges and a loop. A feasible
flow sends two units forward and one unit backward on one parallel edge, one unit forward on the
other edge, and one unit around the loop. Its value is two. Cycle cancellation produces an acyclic
flow of the same value below it; the normalized flow therefore vanishes on the loop and cannot use
both directions of either nonloop edge.
-/

public section

namespace TauCeti.Examples.WeightedMultigraphFlow

open Finset Set
open scoped Graph

/-- The three edge identities in the example: two parallel edges and one loop. -/
abbrev Edge := Fin 3

private def parallelPart : Graph (Fin 2) Edge := Graph.banana 0 1 {0, 1}

private def loopPart : Graph (Fin 2) Edge := Graph.bouquet 0 {2}

private theorem edgeSets_disjoint : Disjoint E(parallelPart) E(loopPart) := by
  simp [parallelPart, loopPart]

/-- The two-vertex multigraph with parallel edges `0` and `1`, and loop `2` at vertex `0`. -/
def graph : Graph (Fin 2) Edge :=
  (Graph.Compatible.of_disjoint_edgeSet edgeSets_disjoint).union

private noncomputable instance : Fintype V(graph) := Fintype.ofFinite _

private noncomputable instance (x y : V(graph)) : Fintype (graph.BidirectedHom x y) :=
  Fintype.ofFinite _

private theorem pLink : graph.IsLink 0 0 1 := by
  simp [graph, parallelPart]

private theorem qLink : graph.IsLink 1 0 1 := by
  simp [graph, parallelPart]

private theorem loopLink : graph.IsLink 2 0 0 := by
  simp [graph, loopPart]

private abbrev s : V(graph) := ⟨0, pLink.left_mem⟩
private abbrev t : V(graph) := ⟨1, pLink.right_mem⟩

private abbrev pForward : graph.BidirectedHom s t := pLink.toBidirectedHom
private abbrev pBackward : graph.BidirectedHom t s := pLink.symm.toBidirectedHom
private abbrev qForward : graph.BidirectedHom s t := qLink.toBidirectedHom
private abbrev loopArrow : graph.BidirectedHom s s := loopLink.toBidirectedHom

private def edgeCapacity (e : E(graph)) : ℤ := if e.1 = 0 then 2 else 1

private noncomputable def assignment : Assignment graph.BidirectedHom ℤ :=
  Assignment.single pForward 2 + Assignment.single pBackward 1 +
    Assignment.single qForward 1 + Assignment.single loopArrow 1

private theorem assignment_nonneg : 0 ≤ assignment := by
  intro x y a
  simp only [assignment, Pi.add_apply, Assignment.single_apply]
  split_ifs <;> norm_num

private theorem assignment_le_capacity : assignment ≤ graph.bidirectedCapacity edgeCapacity := by
  intro x y a
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  rcases a with ⟨e, he⟩
  fin_cases x <;> fin_cases y <;> fin_cases e <;>
    simp [graph, parallelPart, loopPart] at he <;>
    simp [assignment, Assignment.single_apply, edgeCapacity]

private noncomputable def bidirectedFlow : Flow (graph.bidirectedCapacity edgeCapacity) s t where
  toFun := assignment
  mem_Icc := ⟨assignment_nonneg, assignment_le_capacity⟩
  conserve v hvs hvt := by
    rcases v with ⟨v, hv⟩
    fin_cases v <;> simp_all
  excessAt_sink_nonneg := by
    simp [assignment, excessAt_add]

private theorem bidirectedFlow_val : bidirectedFlow.val = 2 := by
  rw [BoundedFlow.val_def]
  simp [bidirectedFlow, assignment, excessAt_add]

-- The original flow uses both directions of `p` and carries a nonzero loop circulation.
example : bidirectedFlow.toFun pForward = 2 ∧ bidirectedFlow.toFun pBackward = 1 ∧
    bidirectedFlow.toFun loopArrow = 1 := by
  simp [bidirectedFlow, assignment, Assignment.single_apply]

-- Cycle cancellation gives the required undirected normal form at the same value.
example :
    ∃ f : Flow (graph.bidirectedCapacity edgeCapacity) s t,
      f.toFun.IsAcyclic ∧ f.val = 2 ∧ f.toFun ≤ bidirectedFlow.toFun ∧
      f.toFun loopArrow = 0 ∧ (f.toFun pForward = 0 ∨ f.toFun pBackward = 0) := by
  obtain ⟨f, hacyc, hval, hle⟩ := bidirectedFlow.exists_isAcyclic
  refine ⟨f, hacyc, hval.trans bidirectedFlow_val, hle,
    hacyc.apply_eq_zero_of_loop (fun _ _ e ↦ f.nonneg e) loopArrow,
    hacyc.apply_eq_zero_or_apply_eq_zero (fun _ _ e ↦ f.nonneg e) pForward pBackward⟩

end TauCeti.Examples.WeightedMultigraphFlow
