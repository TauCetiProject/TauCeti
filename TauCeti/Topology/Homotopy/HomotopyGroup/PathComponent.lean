/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.Sigma
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map

/-!
# Homotopy groups only see the path component of the base point

In positive dimension a generalized loop `I^N → X` based at `x` takes all its values in the path
component of `x`, since the cube is path-connected and its boundary, which goes to `x`, is
nonempty (`GenLoop.apply_mem_pathComponent`). So the map induced on `π_N(X, x)` by a continuous
map depends only on its restriction to that path component
(`HomotopyGroup.map_eq_of_eqOn_pathComponent`).

In particular, for a disjoint union `Σ i, X i` the inclusion of the summand `X i` induces
bijections `π_N(X i, x) → π_N(Σ i, X i, ⟨i, x⟩)` in positive dimension
(`HomotopyGroup.bijective_map_sigmaMk`): it has a retraction (`ContinuousMap.sigmaRetraction`),
collapsing every other summand to `x`, and the composite the other way round is the identity on the
summand, which contains the path component of `⟨i, x⟩`. In dimension zero this fails as soon as
there is a second nonempty summand. These are the homotopy groups of a CW approximation assembled
from one approximation for each path component.

## Main results

* `GenLoop.apply_mem_pathComponent`: a positive-dimensional generalized loop stays in the path
  component of its base point.
* `HomotopyGroup.map_eq_of_eqOn_pathComponent`: maps agreeing on the path component of the base
  point induce the same map on positive-dimensional homotopy groups.
* `HomotopyGroup.bijective_map_sigmaMk`: a summand of a disjoint union has the same
  positive-dimensional homotopy groups as the disjoint union.
-/

public section

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

namespace GenLoop

/-- In positive dimension a generalized loop based at `x` takes its values in the path component
of `x`. -/
theorem apply_mem_pathComponent [Nonempty N] (p : Ω^ N X x) (t : I^N) : p t ∈ pathComponent x := by
  obtain ⟨i⟩ := ‹Nonempty N›
  have : PathConnectedSpace I :=
    (Set.projIcc_surjective (zero_le_one : (0 : ℝ) ≤ 1)).pathConnectedSpace continuous_projIcc
  have h : Joined (p 0) (p t) := (PathConnectedSpace.joined (0 : I^N) t).map p.1.continuous
  rw [_root_.GenLoop.boundary p 0 ⟨i, Or.inl rfl⟩] at h
  exact h

/-- In positive dimension, postcomposing a generalized loop based at `x` with two maps that agree
on the path component of `x` gives the same generalized loop. -/
theorem map_eq_of_eqOn_pathComponent [Nonempty N] {f g : C(X, Y)}
    (h : Set.EqOn f g (pathComponent x)) (hf : f x = y) (hg : g x = y) (p : Ω^ N X x) :
    map f hf p = map g hg p :=
  _root_.GenLoop.ext _ _ fun t ↦ by
    rw [map_apply, map_apply]
    exact h (apply_mem_pathComponent p t)

end GenLoop

namespace HomotopyGroup

/-- In positive dimension, the map induced on the homotopy group at `x` depends only on the values
of the continuous map on the path component of `x`. -/
theorem map_eq_of_eqOn_pathComponent [Nonempty N] {f g : C(X, Y)}
    (h : Set.EqOn f g (pathComponent x)) (hf : f x = y) (hg : g x = y) :
    map (N := N) f hf = map g hg :=
  funext fun a ↦ Quotient.inductionOn a fun p ↦
    congrArg _ (GenLoop.map_eq_of_eqOn_pathComponent h hf hg p)

section Sigma

variable {ι : Type*} {Z : ι → Type*} [∀ i, TopologicalSpace (Z i)]

/-- **Homotopy groups of a disjoint union.** In positive dimension, the inclusion of a summand
`Z i` into the disjoint union `Σ j, Z j` induces a bijection on homotopy groups at every point
of the summand. -/
theorem bijective_map_sigmaMk [Nonempty N] (i : ι) (z : Z i) :
    Function.Bijective (map (N := N) (x := z) (ContinuousMap.sigmaMk (X := Z) i) rfl) := by
  let ι' : C(Z i, Σ j, Z j) := ContinuousMap.sigmaMk i
  let r := ContinuousMap.sigmaRetraction i z
  have hr : r (ι' z) = z := ContinuousMap.sigmaRetraction_sigmaMk i z z
  have hri : r.comp ι' = ContinuousMap.id (Z i) := ContinuousMap.sigmaRetraction_comp_sigmaMk i z
  -- On the summand of `⟨i, z⟩`, which contains its path component, `ι' ∘ r` is the identity.
  have hir : Set.EqOn (ι'.comp r) (ContinuousMap.id _) (pathComponent (ι' z)) := by
    intro p hp
    obtain ⟨w, rfl⟩ := (isClopen_range_sigmaMk.connectedComponent_subset ⟨z, rfl⟩)
      (pathComponent_subset_component _ hp)
    simp [ι', r]
  refine Function.bijective_iff_has_inverse.2 ⟨map r hr, fun a ↦ ?_, fun a ↦ ?_⟩
  · exact map_map_of_comp_eq_id r ι' rfl hr hri a
  · exact (map_comp_apply _ _ _ _ a).trans
      ((congrFun (map_eq_of_eqOn_pathComponent hir _ rfl) a).trans (map_id_apply a))

end Sigma

end HomotopyGroup
