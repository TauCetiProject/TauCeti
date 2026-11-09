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
The coordinate change between two trivializations is jointly continuous in the base point and the
fibre coordinate over the overlap of their base sets, which makes the transition functions of a
fibre bundle continuous.
Finally, the inverse of a trivialization undoes a coordinate change into it, and over a point
of its base set it is an equivalence between the model fibre and the fibre.

## Main results

* `Bundle.TotalSpace.eventually_proj_mem_baseSet_trivializationAt`: near `v₀`, points lie over
  the base set of the trivialization at `v₀.proj`.
* `IsCompact.exists_finset_subset_preimage_biUnion_baseSet`: a compact subset of the total
  space lies over a finite union of preferred trivializing base sets.
* `Bundle.Trivialization.continuousOn_coordChange`: coordinate changes are jointly continuous over
  the overlap of the base sets.
* `Bundle.Trivialization.symm_mk_coordChange`: the inverse of `e₂` undoes the coordinate change
  from `e₁` to `e₂`, landing on the point with the original fibre coordinate in `e₁`.
* `Bundle.Trivialization.symmEquivAt`: the inverse of a trivialization as an equivalence between
  the model fibre and the fibre over a point of its base set.
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

namespace Bundle.Trivialization

variable {B F Z : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z]
  {proj : Z → B}

/-- The coordinate change `(b, v) ↦ e₁.coordChange e₂ b v` between two trivializations is jointly
continuous over the overlap of their base sets. -/
theorem continuousOn_coordChange (e₁ e₂ : Trivialization F proj) :
    ContinuousOn (fun p : B × F ↦ e₁.coordChange e₂ p.1 p.2)
      ((e₁.baseSet ∩ e₂.baseSet) ×ˢ univ) := by
  -- Over the overlap, the coordinate change is the second coordinate of `e₂ ∘ e₁⁻¹`.
  have hsymm : ContinuousOn e₁.toOpenPartialHomeomorph.symm
      ((e₁.baseSet ∩ e₂.baseSet) ×ˢ univ) :=
    e₁.toOpenPartialHomeomorph.continuousOn_symm.mono fun _ hp ↦ e₁.mem_target.2 hp.1.1
  have hmaps : MapsTo e₁.toOpenPartialHomeomorph.symm ((e₁.baseSet ∩ e₂.baseSet) ×ˢ univ)
      e₂.toOpenPartialHomeomorph.source := fun _ hp ↦
    e₂.mem_source.2 (by rw [e₁.proj_symm_apply' hp.1.1]; exact hp.1.2)
  refine (continuous_snd.comp_continuousOn
    (e₂.toOpenPartialHomeomorph.continuousOn.comp hsymm hmaps)).congr
    fun p hp ↦ ?_
  simp only [Function.comp_apply, e₂.coe_coe, ← e₁.mk_coordChange e₂ hp.1.1 hp.1.2 p.2]

end Bundle.Trivialization

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

section CoordChange

variable {B F : Type*} {E : B → Type*} [TopologicalSpace B] [TopologicalSpace F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, Nonempty (E x)]

/-- Reading a coordinate change from `e₁` to `e₂` back through `e₂` gives the point of the fibre
that `e₁` sends to the original fibre coordinate. -/
theorem symm_mk_coordChange (e₁ e₂ : Trivialization F (π F E)) {b : B} (h₁ : b ∈ e₁.baseSet)
    (h₂ : b ∈ e₂.baseSet) (v : F) :
    e₂.toOpenPartialHomeomorph.symm (b, e₁.coordChange e₂ b v) = ⟨b, e₁.symm b v⟩ := by
  rw [e₁.mk_coordChange e₂ h₁ h₂, e₂.symm_apply_apply
    (e₂.mem_source.2 (by rwa [e₁.proj_symm_apply' h₁])), e₁.mk_symm h₁]

/-- The equivalence between the model fibre and the fibre over a point of the base set of a
trivialization, given by the inverse of the trivialization. -/
noncomputable def symmEquivAt (e : Trivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) :
    F ≃ E b where
  toFun := e.symm b
  invFun p := (e ⟨b, p⟩).2
  left_inv v := by simp [e.apply_mk_symm hb]
  right_inv := e.symm_apply_apply_mk hb

@[simp]
theorem symmEquivAt_apply (e : Trivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet) (v : F) :
    e.symmEquivAt hb v = e.symm b v :=
  (rfl)

@[simp]
theorem symmEquivAt_symm_apply (e : Trivialization F (π F E)) {b : B} (hb : b ∈ e.baseSet)
    (p : E b) : (e.symmEquivAt hb).symm p = (e ⟨b, p⟩).2 :=
  (rfl)

end CoordChange

end Bundle.Trivialization
