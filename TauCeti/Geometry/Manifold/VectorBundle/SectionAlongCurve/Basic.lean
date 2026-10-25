/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Coordinates of vector-bundle sections along curves

This file records the coordinate reading of a section of a vector bundle along a curve in one of
the bundle's canonical trivializations. It also relates manifold differentiability of the
corresponding total-space map to differentiability and higher regularity of that coordinate
reading.

## Main definitions and results

* `TauCeti.Manifold.sectionCoord`: the coordinate reading of a section along a curve.
* `TauCeti.Manifold.differentiableWithinAt_sectionCoord`: a differentiability entry point for that
  reading within a parameter set.
* `TauCeti.Manifold.contMDiffWithinAt_sectionCoord_iff`: the `C^n` coordinate characterization
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

/-- The model-fibre reading of a section `W` along `γ` in the vector-bundle trivialization
centred at `x`. The continuous linear map is defined everywhere, carrying Mathlib's junk value
`0` at parameters with `γ t` outside `(trivializationAt F V x).baseSet`. -/
def sectionCoord (x : M) (t : 𝕜) : F :=
  (trivializationAt F V x).continuousLinearMapAt 𝕜 (γ t) (W t)

/-- The defining formula for the coordinate reading of a section along a curve. -/
@[simp]
theorem sectionCoord_apply (x : M) (t : 𝕜) :
    sectionCoord (F := F) (V := V) γ W x t =
      (trivializationAt F V x).continuousLinearMapAt 𝕜 (γ t) (W t) :=
  (rfl)

/-- Coordinate reading commutes with pointwise addition of sections along a curve. -/
@[simp]
theorem sectionCoord_add (W' : ∀ t, V (γ t)) (x : M) :
    sectionCoord (F := F) γ (fun t ↦ W t + W' t) x =
      sectionCoord (F := F) γ W x + sectionCoord (F := F) γ W' x := by
  funext t
  exact map_add _ _ _

/-- Coordinate reading commutes with finite sums of sections along a curve. -/
@[simp]
theorem sectionCoord_sum {ι : Type*} (A : Finset ι) (U : ι → ∀ t, V (γ t)) (x : M) :
    sectionCoord (F := F) γ (fun t ↦ ∑ i ∈ A, U i t) x =
      fun t ↦ ∑ i ∈ A, sectionCoord (F := F) γ (U i) x t := by
  classical
  funext t
  simp only [sectionCoord_apply, map_sum]

/-- Coordinate reading commutes with pointwise scalar multiplication of a section along a curve. -/
@[simp]
theorem sectionCoord_smul (f : 𝕜 → 𝕜) (x : M) :
    sectionCoord (F := F) γ (fun t ↦ f t • W t) x = f • sectionCoord (F := F) γ W x := by
  funext t
  exact map_smul _ _ _

/-- The zero section along a curve has zero coordinate reading. -/
@[simp]
theorem sectionCoord_zero (x : M) :
    sectionCoord (F := F) γ (fun t : 𝕜 ↦ (0 : V (γ t))) x = (0 : 𝕜 → F) := by
  funext t
  exact map_zero _

/-- The coordinate reading of a reparametrized section is the composition of its reading with the
reparametrizing function. -/
@[simp]
theorem sectionCoord_comp (φ : 𝕜 → 𝕜) (x : M) :
    sectionCoord (F := F) (γ ∘ φ) (fun t ↦ W (φ t)) x =
      sectionCoord (F := F) γ W x ∘ φ := by
  ext t
  simp only [sectionCoord_apply, Function.comp_apply]

/-! ### Differentiability of the coordinate reading -/

/-- Given a `C^n` base curve, a section along it is `C^n` as a map into the total space if
and only if its coordinate reading in any trivialization containing the base point is `C^n`.
This statement uses the section's original fibre carriers. -/
theorem contMDiffWithinAt_sectionCoord_iff {n : ℕ∞ω} {s : Set 𝕜} {x : M} {t : 𝕜}
    [ContMDiffVectorBundle n F V I]
    (hγ : ContMDiffWithinAt 𝓘(𝕜, 𝕜) I n γ s t)
    (hx : γ t ∈ (trivializationAt F V x).baseSet) :
    ContDiffWithinAt 𝕜 n (sectionCoord (F := F) γ W x) s t ↔
      ContMDiffWithinAt 𝓘(𝕜, 𝕜) (I.prod 𝓘(𝕜, F)) n
        (fun r ↦ TotalSpace.mk' F (γ r) (W r)) s t := by
  let e := trivializationAt F V x
  have hbase : ∀ᶠ r in 𝓝[s] t, γ r ∈ e.baseSet :=
    hγ.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hx)
  have heq : sectionCoord (F := F) γ W x =ᶠ[𝓝[s] t]
      fun r ↦ (e (TotalSpace.mk' F (γ r) (W r))).2 := by
    filter_upwards [hbase] with r hr
    exact e.continuousLinearMapAt_apply_of_mem 𝕜 hr _
  have heq₀ : sectionCoord (F := F) γ W x t =
      (e (TotalSpace.mk' F (γ t) (W t))).2 :=
    e.continuousLinearMapAt_apply_of_mem 𝕜 hx _
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
    DifferentiableWithinAt 𝕜 (sectionCoord (F := F) γ W x) s t := by
  let e := trivializationAt F V x
  rw [e.mdifferentiableWithinAt_totalSpace_iff I] at h
  · obtain ⟨hproj, hcoord⟩ := h
    have hbase : ∀ᶠ r in 𝓝[s] t, γ r ∈ e.baseSet :=
      hproj.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hx)
    refine hcoord.differentiableWithinAt.congr_of_eventuallyEq
      (hbase.mono fun r hr ↦ ?_) ?_
    · rw [sectionCoord_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _ hr]
    · rw [sectionCoord_apply,
        Bundle.Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _ hx]
  · exact (Bundle.Trivialization.coe_mem_source e).2 hx

/-- A section along a curve which is differentiable at `t` as a map into the total space has a
differentiable coordinate reading in the canonical trivialization at any point `x` whose base set
contains `γ t`. -/
theorem differentiableAt_sectionCoord {x : M} {t : 𝕜} [ContMDiffVectorBundle 1 F V I]
    (h : MDifferentiableAt 𝓘(𝕜, 𝕜) (I.prod 𝓘(𝕜, F))
      (fun r ↦ TotalSpace.mk' F (γ r) (W r)) t)
    (hx : γ t ∈ (trivializationAt F V x).baseSet) :
    DifferentiableAt 𝕜 (sectionCoord (F := F) γ W x) t := by
  rw [← differentiableWithinAt_univ]
  exact differentiableWithinAt_sectionCoord γ W h.mdifferentiableWithinAt hx

end TauCeti.Manifold
