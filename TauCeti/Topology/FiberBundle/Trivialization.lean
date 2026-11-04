/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Preferred trivializations and disjoint unions of trivializations

Near a point `v₀` of the total space of a fibre bundle, every point lies over the base set of the
preferred trivialization at the base point `v₀.proj`, so it can be read in that trivialization.
A compact subset of the total space lies over finitely many preferred trivializing base sets.
An arbitrary family of trivializations over pairwise disjoint open base sets glues to one
trivialization over their union, with the same forward and inverse maps on each constituent.

## Main results

* `Bundle.TotalSpace.eventually_proj_mem_baseSet_trivializationAt`: near `v₀`, points lie over
  the base set of the trivialization at `v₀.proj`.
* `IsCompact.exists_finset_subset_preimage_biUnion_baseSet`: a compact subset of the total
  space lies over a finite union of preferred trivializing base sets.
-/

public section

open Bundle Filter Set
open scoped Topology

namespace Bundle.TotalSpace

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, TopologicalSpace (E x)] [FiberBundle F E]

/-- Near a point `v₀` of the total space, every point lies over the base set of the
trivialization at `v₀.proj`. -/
theorem eventually_proj_mem_baseSet_trivializationAt (v₀ : TotalSpace F E) :
    ∀ᶠ v in 𝓝 v₀, v.proj ∈ (trivializationAt F E v₀.proj).baseSet :=
  (FiberBundle.continuous_proj F E).continuousAt.preimage_mem_nhds
    ((trivializationAt F E v₀.proj).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' v₀.proj))

end Bundle.TotalSpace

/-- A compact subset of a fibre bundle's total space lies over a finite union of the
chosen trivializing base sets. -/
theorem IsCompact.exists_finset_subset_preimage_biUnion_baseSet
    {B : Type*} [TopologicalSpace B] {F : Type*} [TopologicalSpace F]
    {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
    [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
    {K : Set (TotalSpace F E)} (hK : IsCompact K) :
    ∃ s : Finset B, K ⊆ π F E ⁻¹' ⋃ b ∈ s, (trivializationAt F E b).baseSet := by
  obtain ⟨s, hs⟩ := (hK.image (FiberBundle.continuous_proj F E)).elim_finite_subcover
    (fun b : B ↦ (trivializationAt F E b).baseSet)
    (fun b ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩)
  exact ⟨s, fun p hp ↦ hs (mem_image_of_mem _ hp)⟩

namespace Bundle.Trivialization

section DisjointUnion

variable {ι B F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [Nonempty F] [∀ b, Nonempty (E b)]
  (e : ι → Trivialization F (π F E))
  (hd : Pairwise fun i j ↦ Disjoint (e i).baseSet (e j).baseSet)

open Classical in
private noncomputable def iUnionFun (p : TotalSpace F E) : B × F :=
  if h : ∃ i, p.proj ∈ (e i).baseSet then e h.choose p
  else (p.proj, Classical.choice ‹Nonempty F›)

open Classical in
private noncomputable def iUnionInv (p : B × F) : TotalSpace F E :=
  if h : ∃ i, p.1 ∈ (e i).baseSet then (e h.choose).toOpenPartialHomeomorph.symm p
  else ⟨p.1, Classical.choice (inferInstance : Nonempty (E p.1))⟩

omit [Nonempty F] [∀ b, Nonempty (E b)] in
include hd in
private theorem iUnion_index_eq {b : B} {i : ι} (hi : b ∈ (e i).baseSet)
    (h : ∃ j, b ∈ (e j).baseSet) : h.choose = i := by
  by_contra hne
  exact Set.disjoint_left.1 (hd hne) h.choose_spec hi

omit [∀ b, Nonempty (E b)] in
include hd in
private theorem iUnionFun_eq {i : ι} {p : TotalSpace F E}
    (hp : p.proj ∈ (e i).baseSet) : iUnionFun e p = e i p := by
  rw [iUnionFun, dite_eq_left ⟨i, hp⟩, iUnion_index_eq e hd hp]

omit [Nonempty F] in
include hd in
private theorem iUnionInv_eq {i : ι} {p : B × F}
    (hp : p.1 ∈ (e i).baseSet) :
    iUnionInv e p = (e i).toOpenPartialHomeomorph.symm p := by
  rw [iUnionInv, dite_eq_left ⟨i, hp⟩, iUnion_index_eq e hd hp]

/-- Glue an arbitrary family of trivializations with pairwise disjoint base sets. The base set
is their union. No local finiteness is required: every base set is open. The nonempty fibers
supply arbitrary values outside the source and target, where a trivialization has no meaning. -/
noncomputable def iUnion : Trivialization F (π F E) where
  toFun := iUnionFun e
  invFun := iUnionInv e
  source := ⋃ i, (e i).source
  target := ⋃ i, (e i).target
  map_source' p hp := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hp
    rw [iUnionFun_eq e hd ((e i).mem_source.1 hi)]
    exact Set.mem_iUnion.2 ⟨i, (e i).map_source hi⟩
  map_target' p hp := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hp
    rw [iUnionInv_eq e hd ((e i).mem_target.1 hi)]
    exact Set.mem_iUnion.2 ⟨i, (e i).map_target hi⟩
  left_inv' p hp := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hp
    rw [iUnionFun_eq e hd ((e i).mem_source.1 hi),
      iUnionInv_eq e hd (p := e i p) ((e i).mem_target.1 ((e i).map_source hi))]
    exact (e i).left_inv hi
  right_inv' p hp := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hp
    rw [iUnionInv_eq e hd ((e i).mem_target.1 hi),
      iUnionFun_eq e hd ((e i).mem_source.1 ((e i).map_target hi))]
    exact (e i).right_inv hi
  open_source := isOpen_iUnion fun i ↦ (e i).open_source
  open_target := isOpen_iUnion fun i ↦ (e i).open_target
  continuousOn_toFun := ContinuousOn.iUnion_of_isOpen (fun i ↦
    (e i).continuousOn.congr fun p hp ↦ iUnionFun_eq e hd ((e i).mem_source.1 hp))
    fun i ↦ (e i).open_source
  continuousOn_invFun := ContinuousOn.iUnion_of_isOpen (fun i ↦
    (e i).toOpenPartialHomeomorph.symm.continuousOn.congr fun p hp ↦
      iUnionInv_eq e hd ((e i).mem_target.1 hp))
    fun i ↦ (e i).open_target
  baseSet := ⋃ i, (e i).baseSet
  open_baseSet := isOpen_iUnion fun i ↦ (e i).open_baseSet
  source_eq := by simp only [source_eq, Set.preimage_iUnion]
  target_eq := by simp only [target_eq, Set.iUnion_prod_const]
  proj_toFun p hp := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hp
    exact (congrArg Prod.fst (iUnionFun_eq e hd ((e i).mem_source.1 hi))).trans
      ((e i).coe_fst hi)

@[simp]
theorem iUnion_baseSet : (iUnion e hd).baseSet = ⋃ i, (e i).baseSet :=
  (rfl)

include hd in
/-- The glued trivialization agrees with a constituent over its base set. -/
theorem iUnion_apply {i : ι} {p : TotalSpace F E} (hp : p.proj ∈ (e i).baseSet) :
    iUnion e hd p = e i p :=
  iUnionFun_eq e hd hp

include hd in
/-- The inverse of the glued trivialization agrees with the corresponding local inverse. -/
theorem iUnion_symm_apply {i : ι} {p : B × F} (hp : p.1 ∈ (e i).baseSet) :
    (iUnion e hd).toOpenPartialHomeomorph.symm p =
      (e i).toOpenPartialHomeomorph.symm p :=
  iUnionInv_eq e hd hp

end DisjointUnion

end Bundle.Trivialization
