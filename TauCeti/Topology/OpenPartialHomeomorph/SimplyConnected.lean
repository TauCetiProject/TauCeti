/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Topology.PartialHomeomorph.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.PuncturedStarConvex
import TauCeti.Analysis.Convex.SimplyConnected
import TauCeti.Analysis.Normed.Module.Connected

/-!
# Simply connected neighbourhoods in the source of a chart

A partial homeomorphism carries simply connected subsets of its source to simply connected sets.
Pulling back small open balls along a partial homeomorphism `φ : X → E` to a real normed space
therefore gives every point `p` of the source of `φ` a simply connected neighbourhood `B`. Its
punctured version `B \ {p}` is the image of a punctured ball, so it is path connected when `E` has
dimension greater than one and simply connected when `E` has dimension greater than two. These
are the local inputs for deleting a point from a manifold.

## Main declarations

* `PartialHomeomorph.isSimplyConnected_image`: a partial homeomorphism carries simply connected
  subsets of its source to simply connected sets.
* `OpenPartialHomeomorph.exists_mem_nhds_isSimplyConnected_isPathConnected_sdiff_singleton`: in
  dimension greater than one, every point `p` in the source of a chart has a simply connected
  neighbourhood `B`, the preimage of a ball, with `B \ {p}` path connected.
* `OpenPartialHomeomorph.exists_mem_nhds_isSimplyConnected_sdiff_singleton`: in dimension greater
  than two, `B \ {p}` can moreover be taken simply connected.
-/

public section

open Metric Set Topology

/-- The image under a partial homeomorphism `φ` of a simply connected subset of the source of `φ`
is simply connected. -/
theorem PartialHomeomorph.isSimplyConnected_image {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (φ : PartialHomeomorph X Y) {S : Set X} (hS : S ⊆ φ.source)
    (hSc : IsSimplyConnected S) : IsSimplyConnected (φ '' S) :=
  have := hSc.simplyConnectedSpace
  (φ.homeomorphOfImageSubsetSource hS rfl).symm.toHomotopyEquiv.simplyConnectedSpace

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A point `p` in the source of `φ` has a simply connected neighbourhood `φ.symm '' ball (φ p) r`,
whose complement of `p` is the image of the punctured ball. -/
private theorem OpenPartialHomeomorph.exists_ball_subset_target (φ : OpenPartialHomeomorph X E)
    {p : X} (hp : p ∈ φ.source) :
    ∃ r > 0, ball (φ p) r ⊆ φ.target ∧ φ.symm '' ball (φ p) r ∈ 𝓝 p ∧
      IsSimplyConnected (φ.symm '' ball (φ p) r) ∧
      φ.symm '' ball (φ p) r \ {p} = φ.symm '' (ball (φ p) r \ {φ p}) := by
  obtain ⟨r, hr, hbt⟩ := Metric.isOpen_iff.1 φ.open_target (φ p) (φ.map_source hp)
  refine ⟨r, hr, hbt, ?_,
    φ.symm.isSimplyConnected_image hbt ((convex_ball _ r).isSimplyConnected ⟨_, mem_ball_self hr⟩),
    ?_⟩
  · simpa [φ.left_inv hp] using φ.symm.image_mem_nhds (φ.map_source hp) (ball_mem_nhds _ hr)
  · rw [(φ.symm.injOn.mono hbt).image_sdiff_subset (singleton_subset_iff.2 (mem_ball_self hr)),
      image_singleton, φ.left_inv hp]

/-- If `E` is a real normed space of dimension greater than one, every point `p` in the source of
a partial homeomorphism `φ : X → E` has a simply connected neighbourhood `B` with `B \ {p}` path
connected: the preimage of a small open ball about `φ p`. -/
theorem OpenPartialHomeomorph.exists_mem_nhds_isSimplyConnected_isPathConnected_sdiff_singleton
    (h : 1 < Module.rank ℝ E) (φ : OpenPartialHomeomorph X E) {p : X} (hp : p ∈ φ.source) :
    ∃ B ∈ 𝓝 p, IsSimplyConnected B ∧ IsPathConnected (B \ {p}) := by
  obtain ⟨r, hr, hbt, hB, hBsc, hsdiff⟩ := φ.exists_ball_subset_target hp
  refine ⟨_, hB, hBsc, ?_⟩
  rw [hsdiff]
  exact (TauCeti.isPathConnected_ball_sdiff_singleton h _ hr).image'
    (φ.continuousOn_symm.mono (sdiff_subset.trans hbt))

/-- If `E` is a real normed space of dimension greater than two, every point `p` in the source of
a partial homeomorphism `φ : X → E` has a neighbourhood `B` such that `B` and `B \ {p}` are simply
connected: the preimage of a small open ball about `φ p`. -/
theorem OpenPartialHomeomorph.exists_mem_nhds_isSimplyConnected_sdiff_singleton
    (h : 2 < Module.rank ℝ E) (φ : OpenPartialHomeomorph X E) {p : X} (hp : p ∈ φ.source) :
    ∃ B ∈ 𝓝 p, IsSimplyConnected B ∧ IsSimplyConnected (B \ {p}) := by
  obtain ⟨r, hr, hbt, hB, hBsc, hsdiff⟩ := φ.exists_ball_subset_target hp
  refine ⟨_, hB, hBsc, ?_⟩
  rw [hsdiff]
  exact φ.symm.isSimplyConnected_image (sdiff_subset.trans hbt)
    (TauCeti.isSimplyConnected_ball_sdiff_singleton h _ hr)
