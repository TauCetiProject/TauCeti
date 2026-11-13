/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Basic

/-!
# Coordinates of vector-bundle sections along curves

This file records the coordinate reading of a section of a vector bundle along a curve in one of
the bundle's canonical trivializations. It also relates manifold differentiability of the
corresponding total-space map to differentiability and higher regularity of that coordinate
reading.

## Main definitions and results

* `TauCeti.Manifold.differentiableWithinAt_sectionCoord`: a differentiability entry point for that
  reading within a parameter set.
* `TauCeti.Manifold.differentiableWithinAt_sectionCoord_sum`: finite sums of sections with
  differentiable readings have differentiable readings.
* `TauCeti.Manifold.contDiffWithinAt_sectionCoord_iff`: the `C^n` coordinate characterization
  for a section along a `C^n` base curve.
-/

public section

open Bundle Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

variable (γ : 𝕜 → M) (W : ∀ t, V (γ t))

/-! ### Differentiability of the coordinate reading -/

/-- A finite sum of sections along a curve whose coordinate readings are differentiable within
`s` at `t` again has a coordinate reading differentiable within `s` at `t`. -/
theorem differentiableWithinAt_sectionCoord_sum {ι : Type*} {A : Finset ι}
    {U : ι → ∀ t, V (γ t)} {x : M} {s : Set 𝕜} {t : 𝕜}
    (hU : ∀ i ∈ A, DifferentiableWithinAt 𝕜 (sectionCoord 𝕜 (F := F) γ (U i) x) s t) :
    DifferentiableWithinAt 𝕜 (sectionCoord 𝕜 (F := F) γ (fun r ↦ ∑ i ∈ A, U i r) x) s t := by
  rw [sectionCoord_sum]
  exact DifferentiableWithinAt.fun_sum hU

/-- Given a `C^n` base curve, a section along it is `C^n` as a map into the total space if
and only if its coordinate reading in any trivialization containing the base point is `C^n`.
This statement uses the section's original fibre carriers. -/
theorem contDiffWithinAt_sectionCoord_iff {n : ℕ∞ω} {s : Set 𝕜} {x : M} {t : 𝕜}
    [ContMDiffVectorBundle n F V I]
    (hγ : ContMDiffWithinAt 𝓘(𝕜, 𝕜) I n γ s t)
    (hx : γ t ∈ (trivializationAt F V x).baseSet) :
    ContDiffWithinAt 𝕜 n (sectionCoord 𝕜 (F := F) γ W x) s t ↔
      ContMDiffWithinAt 𝓘(𝕜, 𝕜) (I.prod 𝓘(𝕜, F)) n
        (fun r ↦ TotalSpace.mk' F (γ r) (W r)) s t := by
  let e := trivializationAt F V x
  have hbase : ∀ᶠ r in 𝓝[s] t, γ r ∈ e.baseSet :=
    hγ.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hx)
  have heq : sectionCoord 𝕜 (F := F) γ W x =ᶠ[𝓝[s] t]
      fun r ↦ (e (TotalSpace.mk' F (γ r) (W r))).2 := by
    filter_upwards [hbase] with r hr
    rw [sectionCoord_apply]
    exact e.continuousLinearMapAt_apply_of_mem 𝕜 hr _
  have heq₀ : sectionCoord 𝕜 (F := F) γ W x t =
      (e (TotalSpace.mk' F (γ t) (W t))).2 := by
    rw [sectionCoord_apply]
    exact e.continuousLinearMapAt_apply_of_mem 𝕜 hx _
  rw [e.contMDiffWithinAt_iff (f := fun r ↦ TotalSpace.mk' F (γ r) (W r))
    ((e.coe_mem_source).2 hx)]
  constructor
  · intro h
    exact ⟨hγ, (h.congr_of_eventuallyEq heq.symm heq₀.symm).contMDiffWithinAt⟩
  · intro h
    exact h.2.contDiffWithinAt.congr_of_eventuallyEq heq heq₀

/-- A section along a curve which is differentiable within `s` at `t` as a map into the total
space has a differentiable coordinate reading in the canonical trivialization at any point `x`
whose base set contains `γ t`. -/
theorem differentiableWithinAt_sectionCoord {s : Set 𝕜} {x : M} {t : 𝕜}
    [ContMDiffVectorBundle 1 F V I]
    (h : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) (I.prod 𝓘(𝕜, F))
      (fun r ↦ TotalSpace.mk' F (γ r) (W r)) s t)
    (hx : γ t ∈ (trivializationAt F V x).baseSet) :
    DifferentiableWithinAt 𝕜 (sectionCoord 𝕜 (F := F) γ W x) s t :=
  (mdifferentiableWithinAt_sectionCoord γ W h hx).differentiableWithinAt

/-- A section along a curve which is differentiable at `t` as a map into the total space has a
differentiable coordinate reading in the canonical trivialization at any point `x` whose base set
contains `γ t`. -/
theorem differentiableAt_sectionCoord {x : M} {t : 𝕜} [ContMDiffVectorBundle 1 F V I]
    (h : MDifferentiableAt 𝓘(𝕜, 𝕜) (I.prod 𝓘(𝕜, F))
      (fun r ↦ TotalSpace.mk' F (γ r) (W r)) t)
    (hx : γ t ∈ (trivializationAt F V x).baseSet) :
    DifferentiableAt 𝕜 (sectionCoord 𝕜 (F := F) γ W x) t :=
  (mdifferentiableAt_sectionCoord γ W h hx).differentiableAt

/-- Given a differentiable base curve, differentiability of a section along it is equivalent
to differentiability of its reading in any bundle chart containing the current base point. -/
theorem differentiableAt_sectionCoord_iff {x : M} {t : 𝕜}
    [ContMDiffVectorBundle 1 F V I]
    (hγ : MDifferentiableAt 𝓘(𝕜, 𝕜) I γ t)
    (hx : γ t ∈ (trivializationAt F V x).baseSet) :
    DifferentiableAt 𝕜 (sectionCoord 𝕜 (F := F) γ W x) t ↔
      MDifferentiableAt 𝓘(𝕜, 𝕜) (I.prod 𝓘(𝕜, F))
        (fun r ↦ TotalSpace.mk' F (γ r) (W r)) t := by
  rw [← mdifferentiableAt_iff_differentiableAt]
  exact mdifferentiableAt_sectionCoord_iff γ W hγ hx

end TauCeti.Manifold
