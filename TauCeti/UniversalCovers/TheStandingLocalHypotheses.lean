/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Topology.Order.Real

/-!
# Standing local hypotheses for covering space theory

This module formalizes the standing local topological hypotheses required for the construction
and classification of universal covering spaces: path-connectedness, local path-connectedness,
and semilocal simple connectedness. It provides verified witnesses for both discrete spaces
and nondegenerate connected spaces such as the real line `ℝ`.

<!--tauceti-target:v1
  {"focus":"UniversalCovers",
   "id":"UniversalCovers.The_standing_local_hypotheses"}-->
-/

public section

namespace UniversalCovers

open scoped Topology

/-- A topological space is semilocally simply connected if every point has an open neighborhood
such that every loop based at that point is null-homotopic in the ambient space. -/
def IsSemilocallySimplyConnected (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ x : X, ∃ U : Set X, IsOpen U ∧ ∃ hx : x ∈ U,
    ∀ (γ : Path (⟨x, hx⟩ : U) (⟨x, hx⟩ : U)),
      Path.Homotopic (γ.map continuous_subtype_val) (Path.refl x)

/-- Standing local topological hypotheses on a base space for universal covers:
path-connectedness, local path-connectedness, and semilocal simple connectedness. -/
structure LocalCoveringData (X : Type*) [TopologicalSpace X] : Prop where
  /-- The base space is path-connected. -/
  pathConnected : PathConnectedSpace X
  /-- The base space is locally path-connected. -/
  locallyPathConnected : LocallyPathConnectedSpace X
  /-- The base space is semilocally simply connected. -/
  semilocallySimplyConnected : IsSemilocallySimplyConnected X

/-- Any discrete space is semilocally simply connected, since singleton neighborhoods are
open and have only constant loops. -/
theorem isSemilocallySimplyConnected_of_discreteTopology
    (X : Type*) [TopologicalSpace X] [DiscreteTopology X] :
    IsSemilocallySimplyConnected X := by
  intro x
  refine ⟨{x}, isOpen_discrete {x}, ⟨Set.mem_singleton x, fun γ => ?_⟩⟩
  have hγ : γ.map continuous_subtype_val = Path.refl x := by
    ext t
    have h : (γ t).1 = x := (γ t).2
    exact h
  exact hγ ▸ Path.Homotopic.refl (Path.refl x)

/-- Canonical discrete witness: the unit space `PUnit` satisfies the standing local hypotheses. -/
theorem localCoveringDataPUnit : LocalCoveringData PUnit where
  pathConnected := inferInstance
  locallyPathConnected := inferInstance
  semilocallySimplyConnected := isSemilocallySimplyConnected_of_discreteTopology PUnit

/-- The real line `ℝ` is semilocally simply connected via simple connectivity of contractible
spaces in Mathlib. -/
theorem isSemilocallySimplyConnected_real : IsSemilocallySimplyConnected ℝ := by
  intro x
  refine ⟨Set.univ, isOpen_univ, ⟨trivial, fun γ => ?_⟩⟩
  exact SimplyConnectedSpace.paths_homotopic _ _

/-- Nondegenerate connected witness: the real line `ℝ` satisfies the standing local hypotheses. -/
theorem localCoveringDataReal : LocalCoveringData ℝ where
  pathConnected := inferInstance
  locallyPathConnected := inferInstance
  semilocallySimplyConnected := isSemilocallySimplyConnected_real

end UniversalCovers
