/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PartitionOfUnity
public import Mathlib.Topology.VectorBundle.Basic

import TauCeti.Topology.VectorBundle.Smul

/-!
# Continuous sections of vector bundles and partitions of unity

This file develops the arithmetic of continuous sections of a topological vector bundle and uses
it to glue local sections along a partition of unity.

A section `s : Π x, E x` is continuous when `x ↦ TotalSpace.mk' F x (s x)` is continuous.
Over the base set of a trivialization `e`, this is equivalent to continuity of the coordinate
function `x ↦ (e ⟨x, s x⟩).2` (`Bundle.Trivialization.continuousAt_section_iff` and
`Bundle.Trivialization.continuousOn_section_iff`), with no atlas or linearity assumption on `e`.
Sums, finite sums, scalar multiples by continuous functions and locally finite sums of continuous
sections are continuous (`ContinuousAt.add_section`, `ContinuousAt.smul_section`,
`ContinuousAt.sum_section`, `Continuous.finsum_section_of_locallyFinite`; for global scalar
multiples use `Continuous.smul_totalSpace`), and a function with
closed support inside an open set multiplies a section continuous on that set into a globally
continuous section (`ContinuousOn.smul_section_of_tsupport`).

The main result, `TauCeti.exists_continuous_section_forall_mem_convex_of_local`, is the bundle form
of `exists_continuous_forall_mem_convex_of_local`: over a normal paracompact base, if convex
fibrewise conditions can be met by sections that are continuous near each point, then they are met
by a single global continuous section. This is how continuous fibre metrics, and other
fibrewise-convex structures on bundles over paracompact bases, are constructed.

The statements and proofs are the continuous counterparts of Mathlib's smooth section API
`ContMDiffWithinAt.add_section`, `ContMDiffOn.smul_section_of_tsupport` and
`exists_contMDiffSection_forall_mem_convex_of_local`.
-/

public section

open Bundle Filter Function Set
open scoped Topology

namespace Bundle.Trivialization

variable {B F : Type*} [TopologicalSpace B] [TopologicalSpace F] {E : B → Type*}
  [TopologicalSpace (TotalSpace F E)] (e : Trivialization F (π F E)) {s : ∀ x, E x}

/-- Within the base set of a trivialization `e`, a section is continuous at a point within a set
exactly when its coordinate function read in `e` is. -/
theorem continuousWithinAt_section_iff {a : Set B} {x₀ : B} (hx₀ : x₀ ∈ e.baseSet) :
    ContinuousWithinAt (fun x ↦ TotalSpace.mk' F x (s x)) a x₀ ↔
      ContinuousWithinAt (fun x ↦ (e ⟨x, s x⟩).2) a x₀ := by
  rw [ContinuousWithinAt, e.tendsto_nhds_iff (e.mem_source.mpr hx₀)]
  exact and_iff_right (tendsto_nhdsWithin_of_tendsto_nhds continuousAt_id)

/-- Within the base set of a trivialization `e`, a section is continuous at a point exactly when
its coordinate function read in `e` is. -/
theorem continuousAt_section_iff {x₀ : B} (hx₀ : x₀ ∈ e.baseSet) :
    ContinuousAt (fun x ↦ TotalSpace.mk' F x (s x)) x₀ ↔
      ContinuousAt (fun x ↦ (e ⟨x, s x⟩).2) x₀ := by
  simp_rw [← continuousWithinAt_univ]
  exact e.continuousWithinAt_section_iff hx₀

/-- On a subset of the base set of a trivialization `e`, a section is continuous exactly when its
coordinate function read in `e` is. -/
theorem continuousOn_section_iff {a : Set B} (ha : a ⊆ e.baseSet) :
    ContinuousOn (fun x ↦ TotalSpace.mk' F x (s x)) a ↔
      ContinuousOn (fun x ↦ (e ⟨x, s x⟩).2) a :=
  forall₂_congr fun _ hx ↦ e.continuousWithinAt_section_iff (ha hx)

end Bundle.Trivialization

section Operations

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  {f : B → 𝕜} {s t : ∀ x, E x} {u : Set B} {x₀ : B}

variable (𝕜) in
include 𝕜 in
/-- The sum of two sections continuous at a point within a set is continuous there. -/
theorem ContinuousWithinAt.add_section
    (hs : ContinuousWithinAt (fun x ↦ TotalSpace.mk' F x (s x)) u x₀)
    (ht : ContinuousWithinAt (fun x ↦ TotalSpace.mk' F x (t x)) u x₀) :
    ContinuousWithinAt (fun x ↦ TotalSpace.mk' F x (s x + t x)) u x₀ := by
  rw [FiberBundle.continuousWithinAt_section] at hs ht ⊢
  -- The coordinates in the preferred trivialization at `x₀` are linear near `x₀`.
  set e := trivializationAt F E x₀
  have hx₀ : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt F E x₀
  have hlin {x} (hx : x ∈ e.baseSet) := (e.linear 𝕜 hx).map_add (s x) (t x)
  refine (hs.add ht).congr_of_eventuallyEq ?_ (hlin hx₀)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (e.open_baseSet.mem_nhds hx₀)] with x hx
  exact hlin hx

variable (𝕜) in
include 𝕜 in
/-- The sum of two sections continuous at a point is continuous there. -/
theorem ContinuousAt.add_section (hs : ContinuousAt (fun x ↦ TotalSpace.mk' F x (s x)) x₀)
    (ht : ContinuousAt (fun x ↦ TotalSpace.mk' F x (t x)) x₀) :
    ContinuousAt (fun x ↦ TotalSpace.mk' F x (s x + t x)) x₀ := by
  simp_rw [← continuousWithinAt_univ] at hs ht ⊢
  exact hs.add_section 𝕜 ht

variable (𝕜) in
include 𝕜 in
/-- The sum of two sections continuous on a set is continuous on it. -/
theorem ContinuousOn.add_section (hs : ContinuousOn (fun x ↦ TotalSpace.mk' F x (s x)) u)
    (ht : ContinuousOn (fun x ↦ TotalSpace.mk' F x (t x)) u) :
    ContinuousOn (fun x ↦ TotalSpace.mk' F x (s x + t x)) u :=
  fun x hx ↦ (hs x hx).add_section 𝕜 (ht x hx)

variable (𝕜) in
include 𝕜 in
/-- The sum of two continuous sections is continuous. -/
theorem Continuous.add_section (hs : Continuous fun x ↦ TotalSpace.mk' F x (s x))
    (ht : Continuous fun x ↦ TotalSpace.mk' F x (t x)) :
    Continuous fun x ↦ TotalSpace.mk' F x (s x + t x) :=
  continuous_iff_continuousAt.mpr fun _ ↦ hs.continuousAt.add_section 𝕜 ht.continuousAt

/-- The product of a scalar function and a section, both continuous at a point within a set, is
continuous there. -/
theorem ContinuousWithinAt.smul_section (hf : ContinuousWithinAt f u x₀)
    (hs : ContinuousWithinAt (fun x ↦ TotalSpace.mk' F x (s x)) u x₀) :
    ContinuousWithinAt (fun x ↦ TotalSpace.mk' F x (f x • s x)) u x₀ :=
  (TauCeti.VectorBundle.continuous_smul 𝕜 F E).continuousAt.comp_continuousWithinAt (hf.prodMk hs)

/-- The product of a scalar function and a section, both continuous at a point, is continuous
there. -/
theorem ContinuousAt.smul_section (hf : ContinuousAt f x₀)
    (hs : ContinuousAt (fun x ↦ TotalSpace.mk' F x (s x)) x₀) :
    ContinuousAt (fun x ↦ TotalSpace.mk' F x (f x • s x)) x₀ := by
  rw [← continuousWithinAt_univ] at hf hs ⊢
  exact hf.smul_section hs

/-- The product of a scalar function and a section, both continuous on a set, is continuous on
it. -/
theorem ContinuousOn.smul_section (hf : ContinuousOn f u)
    (hs : ContinuousOn (fun x ↦ TotalSpace.mk' F x (s x)) u) :
    ContinuousOn (fun x ↦ TotalSpace.mk' F x (f x • s x)) u :=
  fun x hx ↦ (hf x hx).smul_section (hs x hx)

/-- The product `f • s` of a continuous scalar function `f` and a section `s` is continuous as soon
as `s` is continuous on an open set containing the closed support of `f`. This is the vector
bundle analogue of `continuous_of_tsupport`. -/
theorem ContinuousOn.smul_section_of_tsupport (hf : Continuous f) (hu : IsOpen u)
    (hfu : tsupport f ⊆ u) (hs : ContinuousOn (fun x ↦ TotalSpace.mk' F x (s x)) u) :
    Continuous fun x ↦ TotalSpace.mk' F x (f x • s x) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  by_cases hx : x ∈ tsupport f
  · exact hf.continuousAt.smul_section (hs.continuousAt (hu.mem_nhds (hfu hx)))
  · -- Away from the closed support of `f`, the section `f • s` is the zero section.
    refine (Trivialization.continuousAt_zeroSection 𝕜 (F := F) (E := E) x).congr ?_
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with y hy
    simp [zeroSection, image_eq_zero_of_notMem_tsupport hy]

variable {ι : Type*} {t : ι → ∀ x, E x}

variable (𝕜) in
include 𝕜 in
/-- A finite sum of sections continuous at a point is continuous there. -/
theorem ContinuousAt.sum_section {I : Finset ι}
    (ht : ∀ i ∈ I, ContinuousAt (fun x ↦ TotalSpace.mk' F x (t i x)) x₀) :
    ContinuousAt (fun x ↦ TotalSpace.mk' F x (∑ i ∈ I, t i x)) x₀ := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    -- The zero section is `fun x ↦ TotalSpace.mk' F x 0` by definition.
    exact Trivialization.continuousAt_zeroSection 𝕜 x₀
  | insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact (ht i (Finset.mem_insert_self i I)).add_section 𝕜
      (ih fun j hj ↦ ht j (Finset.mem_insert_of_mem hj))

variable (𝕜) in
include 𝕜 in
/-- The sum of a locally finite family of continuous sections is continuous. -/
theorem Continuous.finsum_section_of_locallyFinite
    (hlf : LocallyFinite fun i ↦ {x | t i x ≠ 0})
    (ht : ∀ i, Continuous fun x ↦ TotalSpace.mk' F x (t i x)) :
    Continuous fun x ↦ TotalSpace.mk' F x (∑ᶠ i, t i x) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  -- Near `x`, only the finitely many sections whose support meets a neighbourhood contribute.
  obtain ⟨U, hU, hfin⟩ := hlf x
  refine (ContinuousAt.sum_section 𝕜 (I := hfin.toFinset) fun i _ ↦ (ht i).continuousAt).congr ?_
  filter_upwards [hU] with y hy
  rw [finsum_eq_sum_of_support_subset _ fun i hi ↦ hfin.mem_toFinset.mpr ⟨y, hi, hy⟩]

end Operations

namespace TauCeti

variable {B F : Type*} [TopologicalSpace B] [NormalSpace B] [ParacompactSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {E : B → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

/-- Let `E` be a real vector bundle over a normal paracompact space and `t x ⊆ E x` a family of
convex sets. If near each point some section, continuous there, lies in `t`, then a single
continuous global section lies in `t` everywhere. This is the vector bundle version of
`exists_continuous_forall_mem_convex_of_local`. -/
theorem exists_continuous_section_forall_mem_convex_of_local (t : ∀ x, Set (E x))
    (ht : ∀ x, Convex ℝ (t x))
    (H : ∀ x₀ : B, ∃ U ∈ 𝓝 x₀, ∃ s : ∀ x, E x,
      ContinuousOn (fun x ↦ TotalSpace.mk' F x (s x)) U ∧ ∀ y ∈ U, s y ∈ t y) :
    ∃ s : ∀ x, E x, Continuous (fun x ↦ TotalSpace.mk' F x (s x)) ∧ ∀ x, s x ∈ t x := by
  choose U hU s hsc hst using H
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (fun x ↦ interior (U x))
    (fun x ↦ isOpen_interior) fun x _ ↦ mem_iUnion.2 ⟨x, mem_interior_iff_mem_nhds.2 (hU x)⟩
  refine ⟨fun x ↦ ∑ᶠ i, ρ i x • s i x, ?_, fun x ↦ ?_⟩
  · refine Continuous.finsum_section_of_locallyFinite ℝ
      (ρ.locallyFinite.subset fun i x (hx : ρ i x • s i x ≠ 0) ↦ left_ne_zero_of_smul hx) fun i ↦ ?_
    exact ContinuousOn.smul_section_of_tsupport (ρ i).continuous isOpen_interior (hρ i)
      ((hsc i).mono interior_subset)
  · refine (ht x).finsum_mem (fun i ↦ ρ.nonneg i x) (ρ.sum_eq_one (mem_univ x)) fun i hi ↦ ?_
    exact hst i x (interior_subset (hρ i (subset_closure hi)))

end TauCeti
