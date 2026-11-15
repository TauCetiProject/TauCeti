/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.Compactness.Lindelof

/-!
# Gluing local `Cⁿ` representatives on a manifold

A function on a manifold that agrees almost everywhere near each point with a `Cⁿ` function
agrees almost everywhere with a single globally `Cⁿ` function. Two local representatives are
continuous and agree almost everywhere on their common open domain, so for a measure that charges
every nonempty open set they agree everywhere there (`MeasureTheory.Measure.eqOn_open_of_ae_eq`).
The value at `y` of any representative near `y` therefore defines the glued function, and the
Lindelöf property turns the local almost everywhere equalities into a global one.

This is how regularity proved in charts, for instance by Euclidean elliptic regularity, becomes
regularity of one representative on the whole manifold. The case `n = 0` glues continuous
representatives. It is the manifold counterpart of `TauCeti.exists_contDiffOn_ae_eq_of_locally`.

## Main results

* `TauCeti.exists_contMDiff_ae_eq_of_locally`: local `Cⁿ` representatives glue to a global `Cⁿ`
  representative.
-/

public section

open MeasureTheory Set Filter Topology
open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [LindelofSpace M] [MeasurableSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [T2Space N]
  {μ : Measure M} [μ.IsOpenPosMeasure] {n : WithTop ℕ∞} {u : M → N}

/-- **Gluing local `Cⁿ` representatives on a manifold.** If near each point of `M` the function
`u` agrees almost everywhere with a function that is `Cⁿ` on a neighbourhood of that point, then
`u` agrees almost everywhere with a single globally `Cⁿ` function. The measure must charge every
nonempty open set. -/
theorem exists_contMDiff_ae_eq_of_locally
    (h : ∀ x, ∃ U ∈ 𝓝 x, ∃ g : M → N, ContMDiffOn I I' n g U ∧ u =ᵐ[μ.restrict U] g) :
    ∃ g : M → N, ContMDiff I I' n g ∧ u =ᵐ[μ] g := by
  -- Shrink every neighbourhood to an open one.
  have h' : ∀ x, ∃ U, IsOpen U ∧ x ∈ U ∧
      ∃ g : M → N, ContMDiffOn I I' n g U ∧ u =ᵐ[μ.restrict U] g := by
    intro x
    obtain ⟨U, hU, g, hg, hug⟩ := h x
    exact ⟨interior U, isOpen_interior, mem_interior_iff_mem_nhds.2 hU, g,
      hg.mono interior_subset, ae_restrict_of_ae_restrict_of_subset interior_subset hug⟩
  choose U hUo hxU g hg hug using h'
  -- Two representatives are continuous and agree almost everywhere on their common open domain,
  -- hence agree everywhere there; so the representative at `y` agrees with the one near `x`.
  have hG (x : M) : EqOn (fun y ↦ g y y) (g x) (U x) := fun y hy ↦
    Measure.eqOn_open_of_ae_eq (f := g y) (g := g x)
      ((EventuallyEq.symm <| ae_restrict_of_ae_restrict_of_subset inter_subset_left
        (hug y)).trans (ae_restrict_of_ae_restrict_of_subset inter_subset_right (hug x)))
      ((hUo y).inter (hUo x)) ((hg y).continuousOn.mono inter_subset_left)
      ((hg x).continuousOn.mono inter_subset_right) ⟨hxU y, hy⟩
  refine ⟨fun y ↦ g y y, fun x ↦ ((hg x).congr (hG x)).contMDiffAt ((hUo x).mem_nhds (hxU x)),
    ?_⟩
  -- Near `x` the glued function is `g x`, which equals `u` almost everywhere on `U x`; countably
  -- many of the sets `U x` cover `M`.
  obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover U fun x ↦ (hUo x).mem_nhds (hxU x)
  rw [EventuallyEq, ae_iff]
  have hsub : {y | u y ≠ g y y} ⊆ ⋃ x ∈ t, U x ∩ {y | u y ≠ g x y} := by
    intro y hy
    obtain ⟨x, hxt, hyU⟩ := mem_iUnion₂.1 (hcover ▸ mem_univ y)
    exact mem_iUnion₂.2 ⟨x, hxt, hyU, fun h ↦ hy (h.trans (hG x hyU).symm)⟩
  refine measure_mono_null hsub ((measure_biUnion_null_iff ht).2 fun x _ ↦ ?_)
  rw [inter_comm]
  exact nonpos_iff_eq_zero.1 ((Measure.le_restrict_apply _ _).trans (ae_iff.1 (hug x)).le)

end TauCeti
