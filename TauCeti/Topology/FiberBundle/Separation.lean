/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Hausdorffness of the total space of a fiber bundle

Mathlib records that each fiber of a fiber bundle inherits the separation axioms of the model
fiber (`FiberBundle.t2Space`). This file proves the corresponding statement for the total space:
if the base and the model fiber are Hausdorff, so is the total space.

Two points of the total space over distinct base points are separated by preimages under the
projection. Two points over the same base point lie in the source of one local trivialization,
which is a homeomorphism onto an open subset of the Hausdorff space `B × F`.

The main application is to tangent bundles: the tangent bundle of a Hausdorff manifold is
Hausdorff, which is what uniqueness of integral curves of vector fields on the tangent bundle,
such as the geodesic spray, requires.
-/

public section

open Bundle

namespace TauCeti.FiberBundle

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- The total space of a fiber bundle with Hausdorff base and Hausdorff model fiber is
Hausdorff. -/
instance t2Space_totalSpace [T2Space B] [T2Space F] : T2Space (TotalSpace F E) := by
  refine t2Space_iff_disjoint_nhds.2 fun x y hxy ↦ ?_
  by_cases h : x.proj = y.proj
  · -- Both points lie in the source of the trivialization at their common base point.
    let e := trivializationAt F E x.proj
    have hx : x ∈ e.source := _root_.FiberBundle.mem_trivializationAt_proj_source
    have hy : y ∈ e.source := by
      rw [e.mem_source, ← h]
      exact mem_baseSet_trivializationAt F E x.proj
    exact (e.continuousAt hx).tendsto.disjoint
      (disjoint_nhds_nhds.2 fun hexy ↦ hxy (e.injOn hx hy hexy)) (e.continuousAt hy).tendsto
  · -- Points over distinct base points are separated through the projection.
    have hproj := _root_.FiberBundle.continuous_proj F E
    exact (hproj.tendsto x).disjoint (disjoint_nhds_nhds.2 h) (hproj.tendsto y)

end TauCeti.FiberBundle
