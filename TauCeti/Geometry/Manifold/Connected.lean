/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
import TauCeti.Analysis.Normed.Module.Connected
import TauCeti.Topology.ConnectedComponents
import Mathlib.Geometry.Manifold.HasGroupoid

/-!
# Removing a discrete set from a connected manifold

A connected topological manifold modelled on a real seminormed space `E` of dimension greater than
one stays connected when a closed discrete set is removed. When the model space is normed, this
applies in particular to finite sets. For a compact Riemann surface this is the statement that the
complement of finitely many points, such as the preimage of the branch values of a holomorphic map,
is connected.

The local input is that every point has arbitrarily small neighbourhoods whose punctured versions
are connected: in a chart these are punctured balls of `E`
(`TauCeti.isConnected_ball_sdiff_singleton`). The global argument is
`TauCeti.isPreconnected_compl_of_isDiscrete`. Only the charted-space structure is used, with the
model space `E` itself; no smoothness of the transition maps is needed.

## Main declarations

* `TauCeti.exists_mem_nhds_subset_isConnected_sdiff_singleton`: every point of the manifold has
  arbitrarily small neighbourhoods whose punctured versions are connected.
* `TauCeti.isPreconnected_compl_of_isDiscrete_of_one_lt_rank`: removing a closed discrete set from
  a preconnected manifold leaves it preconnected.
* `TauCeti.isConnected_compl_of_isDiscrete_of_one_lt_rank`: removing a closed discrete set from a
  connected manifold leaves it connected.
* `TauCeti.isConnected_compl_of_finite_of_one_lt_rank`: the special case of a finite set.
* `TauCeti.isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank`: closed discrete
  deletion inside a preconnected open subset.
-/

public section

open Metric Set Topology

namespace TauCeti

variable {E X : Type*} [TopologicalSpace X]

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E X]

/-- In a manifold modelled on a real seminormed space of dimension greater than one, every point `x`
has arbitrarily small neighbourhoods `V` with `V \ {x}` connected. -/
theorem exists_mem_nhds_subset_isConnected_sdiff_singleton (h : 1 < Module.rank ℝ E) (x : X)
    {U : Set X} (hU : U ∈ 𝓝 x) : ∃ V ∈ 𝓝 x, V ⊆ U ∧ IsConnected (V \ {x}) :=
  exists_mem_nhds_subset_isConnected_sdiff_singleton_of_mem_source h (chartAt E x)
    (mem_chart_source E x) hU

/-- **Removing a closed discrete set from a preconnected manifold leaves it preconnected**, when
the model is a real seminormed space of dimension greater than one. -/
theorem isPreconnected_compl_of_isDiscrete_of_one_lt_rank [PreconnectedSpace X]
    (h : 1 < Module.rank ℝ E) {s : Set X} (hs : IsClosed s) (hd : IsDiscrete s) :
    IsPreconnected sᶜ :=
  isPreconnected_compl_of_isDiscrete hs hd fun x _ _ hU ↦
    exists_mem_nhds_subset_isConnected_sdiff_singleton h x hU

/-- **Removing a closed discrete set from a connected manifold leaves it connected**, when the
model is a real seminormed space of dimension greater than one. -/
theorem isConnected_compl_of_isDiscrete_of_one_lt_rank [ConnectedSpace X]
    (h : 1 < Module.rank ℝ E) {s : Set X} (hs : IsClosed s) (hd : IsDiscrete s) :
    IsConnected sᶜ := by
  refine ⟨?_, isPreconnected_compl_of_isDiscrete_of_one_lt_rank h hs hd⟩
  obtain ⟨x⟩ := ConnectedSpace.toNonempty (α := X)
  by_cases hx : x ∈ s
  · -- A punctured neighbourhood of `x` avoiding the rest of `s` supplies a point off `s`.
    obtain ⟨u, hu, hus⟩ := isDiscrete_iff_forall_mem_exists_isOpen.1 hd x hx
    have hxu : x ∈ u := (hus.symm ▸ mem_singleton x : x ∈ u ∩ s).1
    obtain ⟨V, -, hVu, hc⟩ := exists_mem_nhds_subset_isConnected_sdiff_singleton h x
      (hu.mem_nhds hxu)
    obtain ⟨z, hz⟩ := hc.nonempty
    refine ⟨z, fun hzs ↦ hz.2 ?_⟩
    simpa [← hus] using And.intro (hVu hz.1) hzs
  · exact ⟨x, hx⟩

/-- Removing a closed discrete set from a preconnected open subset of a manifold of real
dimension greater than one leaves it preconnected. -/
theorem isPreconnected_sdiff_of_isOpen_of_isDiscrete_of_one_lt_rank
    (h : 1 < Module.rank ℝ E) {U s : Set X} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hs : IsClosed s) (hd : IsDiscrete s) : IsPreconnected (U \ s) := by
  let V : TopologicalSpace.Opens X := ⟨U, hU⟩
  let : PreconnectedSpace V := isPreconnected_iff_preconnectedSpace.mp hUc
  have hc := isPreconnected_compl_of_isDiscrete_of_one_lt_rank (E := E) h
    (hs.preimage (continuous_subtype_val : Continuous (Subtype.val : V → X)))
    (hd.preimage continuous_subtype_val.continuousOn Subtype.val_injective)
  have himage : Subtype.val '' (Subtype.val ⁻¹' s : Set V)ᶜ = U \ s := by
    rw [image_compl_preimage, Subtype.range_val]
    rfl
  rw [← himage]
  exact hc.image _ continuous_subtype_val.continuousOn

end Seminormed

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [ChartedSpace E X]

/-- **Removing a finite set from a connected manifold leaves it connected**, when the model is a
real normed space of dimension greater than one. -/
theorem isConnected_compl_of_finite_of_one_lt_rank [ConnectedSpace X] (h : 1 < Module.rank ℝ E)
    {s : Set X} (hs : s.Finite) : IsConnected sᶜ :=
  have := ChartedSpace.t1Space E X
  isConnected_compl_of_isDiscrete_of_one_lt_rank h hs.isClosed hs.isDiscrete

end TauCeti
