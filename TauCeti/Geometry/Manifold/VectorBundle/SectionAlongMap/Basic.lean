/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable

/-!
# Coordinates of vector-bundle sections along maps

Reading a dependent section in a fixed bundle trivialization gives a model-fibre-valued map
on the parameter domain. This permits manifold differentiation, in particular for covariant
differentiation of tangent fields along maps in submanifold geometry.

The coordinate reading and its algebra laws require only a vector bundle over a topological
space. For a differentiable base map, differentiability of the total-space section at a point
is equivalent to differentiability of its coordinate reading in any trivialization containing
the image point. Differentiability of the total-space section within a set also implies
differentiability of its coordinate reading within that set.
-/

public section

open Bundle Filter
open scoped Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [TopologicalSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

variable {N : Type*} (γ : N → M) (W : ∀ t, V (γ t))

variable (𝕜) in
/-- The model-fibre reading of a section `W` along `γ` in the vector-bundle trivialization
centred at `x`. The continuous linear map is defined everywhere, carrying Mathlib's junk value
`0` at parameters with `γ t` outside `(trivializationAt F V x).baseSet`. -/
def sectionCoord (x : M) (t : N) : F :=
  (trivializationAt F V x).continuousLinearMapAt 𝕜 (γ t) (W t)

/-- The defining formula for the coordinate reading of a section along a map. -/
@[simp]
theorem sectionCoord_apply (x : M) (t : N) :
    sectionCoord 𝕜 (F := F) (V := V) γ W x t =
      (trivializationAt F V x).continuousLinearMapAt 𝕜 (γ t) (W t) :=
  (rfl)

/-- Coordinate reading commutes with pointwise addition of sections along a map. -/
@[simp]
theorem sectionCoord_add (W' : ∀ t, V (γ t)) (x : M) :
    sectionCoord 𝕜 (F := F) γ (fun t ↦ W t + W' t) x =
      sectionCoord 𝕜 (F := F) γ W x + sectionCoord 𝕜 (F := F) γ W' x := by
  funext t
  exact map_add _ _ _

/-- Coordinate reading commutes with pointwise subtraction of sections along a map. -/
@[simp]
theorem sectionCoord_sub (W' : ∀ t, V (γ t)) (x : M) :
    sectionCoord 𝕜 (F := F) γ (fun t ↦ W t - W' t) x =
      sectionCoord 𝕜 (F := F) γ W x - sectionCoord 𝕜 (F := F) γ W' x := by
  funext t
  exact map_sub _ _ _

/-- Coordinate reading commutes with finite sums of sections along a map. -/
@[simp]
theorem sectionCoord_sum {ι : Type*} (A : Finset ι) (U : ι → ∀ t, V (γ t)) (x : M) :
    sectionCoord 𝕜 (F := F) γ (fun t ↦ ∑ i ∈ A, U i t) x =
      fun t ↦ ∑ i ∈ A, sectionCoord 𝕜 (F := F) γ (U i) x t := by
  classical
  funext t
  simp only [sectionCoord_apply, map_sum]

/-- Coordinate reading commutes with pointwise scalar multiplication of a section along a map. -/
@[simp]
theorem sectionCoord_smul (f : N → 𝕜) (x : M) :
    sectionCoord 𝕜 (F := F) γ (fun t ↦ f t • W t) x = f • sectionCoord 𝕜 (F := F) γ W x := by
  funext t
  exact map_smul _ _ _

/-- Coordinate reading commutes with negation. -/
@[simp]
theorem sectionCoord_neg (x : M) :
    sectionCoord 𝕜 (F := F) γ (fun t ↦ -W t) x = -sectionCoord 𝕜 (F := F) γ W x := by
  funext t
  exact map_neg _ _

/-- Coordinate reading commutes with multiplication by a constant scalar. -/
@[simp]
theorem sectionCoord_const_smul (c : 𝕜) (x : M) :
    sectionCoord 𝕜 (F := F) γ (c • W) x = c • sectionCoord 𝕜 (F := F) γ W x := by
  funext t
  exact map_smul _ _ _

/-- The zero section along a map has zero coordinate reading. -/
@[simp, to_fun (attr := simp)]
theorem sectionCoord_zero (x : M) :
    sectionCoord 𝕜 (F := F) γ (0 : ∀ t, V (γ t)) x = (0 : N → F) := by
  funext t
  exact map_zero _

/-- The coordinate reading of a reparametrized section is the composition of its reading with the
reparametrizing function. -/
@[simp]
theorem sectionCoord_comp {P : Type*} (φ : P → N) (x : M) :
    sectionCoord 𝕜 (F := F) (γ ∘ φ) (fun t ↦ W (φ t)) x =
      sectionCoord 𝕜 (F := F) γ W x ∘ φ := by
  ext t
  simp only [sectionCoord_apply, Function.comp_apply]

/-- Inverting the coordinate reading recovers the section on the trivialization base set. -/
theorem symmL_sectionCoord (x : M) (t : N)
    (hx : γ t ∈ (trivializationAt F V x).baseSet) :
    (trivializationAt F V x).symmL 𝕜 (γ t) (sectionCoord 𝕜 (F := F) γ W x t) = W t := by
  rw [sectionCoord_apply]
  exact (trivializationAt F V x).symmL_continuousLinearMapAt hx (W t)

/-- The coordinate reading at its own base point always reconstructs the section. -/
theorem symmL_sectionCoord_self (t : N) :
    (trivializationAt F V (γ t)).symmL 𝕜 (γ t)
      (sectionCoord 𝕜 (F := F) γ W (γ t) t) = W t :=
  symmL_sectionCoord γ W (γ t) t (FiberBundle.mem_baseSet_trivializationAt F V (γ t))

variable
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [ContMDiffVectorBundle 1 F V I]

/-- A section differentiable into the total space within a set has a differentiable coordinate
reading within that set whenever the image point belongs to the trivialization base set. -/
theorem mdifferentiableWithinAt_sectionCoord {s : Set N} {x : M} {t : N}
    (h : MDifferentiableWithinAt J (I.prod 𝓘(𝕜, F))
      (fun r ↦ TotalSpace.mk' F (γ r) (W r)) s t)
    (hx : γ t ∈ (trivializationAt F V x).baseSet) :
    MDifferentiableWithinAt J 𝓘(𝕜, F) (sectionCoord 𝕜 (F := F) γ W x) s t := by
  let e := trivializationAt F V x
  obtain ⟨hf, hc⟩ := (e.mdifferentiableWithinAt_totalSpace_iff I
    (fun r ↦ TotalSpace.mk' F (γ r) (W r))
    (e.coe_mem_source.mpr hx)).mp h
  have hbase : ∀ᶠ r in 𝓝[s] t, γ r ∈ e.baseSet :=
    hf.continuousWithinAt.preimage_mem_nhdsWithin (e.open_baseSet.mem_nhds hx)
  exact hc.congr_of_eventuallyEq
    (hbase.mono fun r hr ↦ e.continuousLinearMapAt_apply_of_mem 𝕜 hr (W r))
    (e.continuousLinearMapAt_apply_of_mem 𝕜 hx (W t))

/-- A section differentiable into the total space at a point has a differentiable coordinate
reading at that point whenever its image belongs to the trivialization base set. -/
theorem mdifferentiableAt_sectionCoord {x : M} {t : N}
    (h : MDifferentiableAt J (I.prod 𝓘(𝕜, F))
      (fun r ↦ TotalSpace.mk' F (γ r) (W r)) t)
    (hx : γ t ∈ (trivializationAt F V x).baseSet) :
    MDifferentiableAt J 𝓘(𝕜, F) (sectionCoord 𝕜 (F := F) γ W x) t := by
  rw [← mdifferentiableWithinAt_univ]
  exact mdifferentiableWithinAt_sectionCoord γ W h.mdifferentiableWithinAt hx

/-- For a differentiable base map, differentiability of the coordinate reading characterizes
that of the total-space section. -/
theorem mdifferentiableAt_sectionCoord_iff {x : M} {t : N}
    (hγ : MDifferentiableAt J I γ t)
    (hx : γ t ∈ (trivializationAt F V x).baseSet) :
    MDifferentiableAt J 𝓘(𝕜, F) (sectionCoord 𝕜 (F := F) γ W x) t ↔
      MDifferentiableAt J (I.prod 𝓘(𝕜, F))
        (fun r ↦ TotalSpace.mk' F (γ r) (W r)) t := by
  refine ⟨fun h ↦ ?_, fun h ↦ mdifferentiableAt_sectionCoord γ W h hx⟩
  let e := trivializationAt F V x
  rw [e.mdifferentiableAt_totalSpace_iff I
    (fun r ↦ TotalSpace.mk' F (γ r) (W r)) (e.coe_mem_source.mpr hx)]
  refine ⟨hγ, h.congr_of_eventuallyEq ?_⟩
  filter_upwards [hγ.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hx)] with r hr
  exact (e.continuousLinearMapAt_apply_of_mem 𝕜 hr (W r)).symm

end TauCeti.Manifold
