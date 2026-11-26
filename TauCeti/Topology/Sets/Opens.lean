/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.Separation.Regular
import TauCeti.Topology.Compactness.Compact

/-!
# Carrying a basis from families of sets to families of opens

A basis of a topological space is presented in two ways in Mathlib, and neither is canonical:
`TopologicalSpace.IsTopologicalBasis` takes a `Set (Set X)`, while `TopologicalSpace.Opens.IsBasis`
takes a `Set (Opens X)`. This file bridges the first form to the second, for consumers stated in
terms of `Opens` — the sheaf-theoretic ones, since `Opens X` is the category a presheaf on `X` is
indexed by.

## Main results

* `TopologicalSpace.IsTopologicalBasis.isBasis_opens` : a basis presented as a family of sets
  yields one presented as a family of `Opens`.
* `TopologicalSpace.Opens.isClosed_setOf_not_exists` : the points with no open neighbourhood
  satisfying a given predicate form a closed set.
* `TopologicalSpace.Opens.exists_le_preimage_coe_eq` : every open subset of an open set `Ω`,
  viewed as a subspace, is the trace of an open set contained in `Ω`.
* `TopologicalSpace.Opens.exists_between_and_isCompact_closure` : in a locally compact regular
  space, a compact subset of an open set `U` lies in an open set with compact closure inside `U`;
  `TopologicalSpace.Opens.exists_mem_and_isCompact_closure` is the case of a point.
* `TopologicalSpace.Opens.le_iSup_iff_subset_iUnion` : an open set lies below the supremum of a
  family of open sets exactly when their underlying sets cover it.
* `TopologicalSpace.Opens.isEmpty_of_iSup_eq_top` : an empty family of open sets covers only the
  empty space.
* `TopologicalSpace.Opens.eq_bot_of_not_nonempty` : an open set with no points is the empty open
  set.
* `TauCeti.TopologicalSpace.Opens.isClopen_of_pairwiseDisjoint_iSup_eq_top` : every member of a
  pairwise-disjoint open cover is clopen.
* `TopologicalSpace.Opens.isCompl_comap_iff` : the preimages of two open sets under a continuous
  map are complementary exactly when the range lies in their union and misses their intersection.
* `TopologicalSpace.Opens.instLocallyCompactSpace` : an open subset of a locally compact space is
  locally compact.
* `TopologicalSpace.Opens.sigmaCompactSpace_top` : the open subset `⊤` of a σ-compact space is
  σ-compact.
* `TopologicalSpace.Opens.Ioo` : the open interval `Set.Ioo a b` bundled as an open set.
* `TopologicalSpace.Opens.IsBasis.exists_finset_sup_le_of_isCompact` : a compact subset of an
  open set has a neighbourhood inside it which is a finite union of basis members.
* `IsCompact.preimage_val_of_pairwise_disjoint` : a compact set covered by open sets meeting it in
  pairwise disjoint sets has compact preimage in each of them.
-/

public section

namespace TopologicalSpace.IsTopologicalBasis

variable {X : Type*} [TopologicalSpace X]

/-- **A basis of sets is a basis of opens.** A basis presented as a `Set (Set X)`, the form
`TopologicalSpace.IsTopologicalBasis` takes, yields one presented as a `Set (Opens X)`, the form
`Opens.IsBasis` takes: keep the opens whose underlying set is a member. Nothing is lost, since
every member of a topological basis is open. -/
theorem isBasis_opens {S : Set (Set X)} (hS : IsTopologicalBasis S) :
    Opens.IsBasis {U : Opens X | (U : Set X) ∈ S} := by
  rwa [Opens.IsBasis, ← Set.preimage_ofPred_eq, Set.ofPred_mem_eq,
    Set.image_preimage_eq_of_subset fun s hs ↦ ⟨⟨s, hS.isOpen hs⟩, rfl⟩]

end TopologicalSpace.IsTopologicalBasis

namespace TopologicalSpace.Opens

variable {X : Type*} [TopologicalSpace X]

/-- The interior of the underlying set of an open set is that open set. -/
@[simp]
theorem interior_coe (U : Opens X) : Opens.interior (U : Set X) = U :=
  Opens.ext U.isOpen.interior_eq

/-- A set of the form `{x | ¬ ∃ U : Opens X, x ∈ U ∧ P U}` is closed: its complement is the union
of the open sets `U` with `P U`. -/
theorem isClosed_setOf_not_exists (P : Opens X → Prop) :
    IsClosed {x : X | ¬ ∃ U : Opens X, x ∈ U ∧ P U} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hxU, hU⟩ := not_not.mp hx
  exact ⟨U, fun y hy ↦ not_not.mpr ⟨U, hy, hU⟩, U.isOpen, hxU⟩

/-- Every open subset `W` of the subspace `Ω` is the trace on `Ω` of an open set `U ≤ Ω`, namely
its image in `X`. -/
theorem exists_le_preimage_coe_eq (Ω : Opens X) {W : Set Ω} (hW : IsOpen W) :
    ∃ U : Opens X, U ≤ Ω ∧ ((↑) : Ω → X) ⁻¹' (U : Set X) = W :=
  ⟨⟨(↑) '' W, Ω.isOpen.isOpenMap_subtypeVal W hW⟩, Subtype.coe_image_subset _ _,
    Set.preimage_image_eq W Subtype.val_injective⟩

/-- In a locally compact regular space, every compact subset `K` of an open set `U` lies in an
open set whose closure is compact and contained in `U`. This is
`exists_open_between_and_isCompact_closure` with the open sets bundled as `Opens`. -/
theorem exists_between_and_isCompact_closure [LocallyCompactSpace X] [RegularSpace X]
    {K : Set X} (hK : IsCompact K) {U : Opens X} (hKU : K ⊆ U) :
    ∃ V : Opens X, K ⊆ V ∧ closure (V : Set X) ⊆ U ∧ IsCompact (closure (V : Set X)) := by
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK U.isOpen hKU
  exact ⟨⟨V, hVo⟩, hKV, hVU, hVc⟩

/-- In a locally compact regular space, every point `x` of an open set `U` lies in an open set
whose closure is compact and contained in `U`. This is the case `K = {x}` of
`TopologicalSpace.Opens.exists_between_and_isCompact_closure`. -/
theorem exists_mem_and_isCompact_closure [LocallyCompactSpace X] [RegularSpace X] {x : X}
    {U : Opens X} (hx : x ∈ U) :
    ∃ V : Opens X, x ∈ V ∧ closure (V : Set X) ⊆ U ∧ IsCompact (closure (V : Set X)) := by
  obtain ⟨V, hxV, hVU, hVc⟩ :=
    exists_between_and_isCompact_closure isCompact_singleton (Set.singleton_subset_iff.2 hx)
  exact ⟨V, hxV rfl, hVU, hVc⟩

/-- An open set lies below the supremum of a family of open sets exactly when their underlying
sets cover it. -/
theorem le_iSup_iff_subset_iUnion {ι : Sort*} {U : Opens X} {V : ι → Opens X} :
    U ≤ ⨆ i, V i ↔ (U : Set X) ⊆ ⋃ i, (V i : Set X) := by
  rw [← SetLike.coe_subset_coe, coe_iSup]

/-- An empty family of open sets covers only the empty space. -/
theorem isEmpty_of_iSup_eq_top {ι : Sort*} [IsEmpty ι] {U : ι → Opens X}
    (hcover : ⨆ i, U i = ⊤) : IsEmpty X :=
  ⟨fun x ↦ isEmptyElim (Opens.mem_iSup.1 (hcover ▸ Opens.mem_top x)).choose⟩

/-- An open set with no points is the empty open set. -/
theorem eq_bot_of_not_nonempty {U : Opens X} (h : ¬ Nonempty U) : U = ⊥ :=
  (not_nonempty_iff_eq_bot U).mp fun hne ↦ h (Set.nonempty_coe_sort.mpr hne)

/-- Every member of a pairwise-disjoint open cover is clopen, without a finiteness assumption
on the indexing type. -/
theorem _root_.TauCeti.TopologicalSpace.Opens.isClopen_of_pairwiseDisjoint_iSup_eq_top
    {ι : Type*} (U : ι → Opens X)
    (hcover : ⨆ i, U i = ⊤) (hdisj : Pairwise fun i j ↦ Disjoint (U i) (U j)) (j : ι) :
    IsClopen (U j : Set X) := by
  classical
  let V : Opens X := ⨆ i : {i : ι // i ≠ j}, U i.val
  apply isClopen_of_disjoint_cover_open (b := (V : Set X)) ?_ (U j).isOpen V.isOpen ?_
  · intro x _
    have hxcover : x ∈ ⨆ i, U i := hcover.symm ▸ trivial
    obtain ⟨i, hi⟩ := mem_iSup.mp hxcover
    by_cases hij : i = j
    · exact Or.inl (hij ▸ hi)
    · exact Or.inr (mem_iSup.mpr ⟨⟨i, hij⟩, hi⟩)
  · apply Set.disjoint_left.mpr
    intro x hxj hxV
    obtain ⟨i, hi⟩ := mem_iSup.mp hxV
    exact (hdisj i.property).le_bot ⟨hi, hxj⟩

/-- The preimages of two open sets under a continuous map are complementary exactly when the
range of the map lies in their union and misses their intersection. -/
theorem isCompl_comap_iff {Y : Type*} [TopologicalSpace Y] {f : C(X, Y)} (U V : Opens Y) :
    IsCompl (comap f U) (comap f V) ↔
      Set.range f ⊆ (U : Set Y) ∪ V ∧ Disjoint (Set.range f) ((U : Set Y) ∩ V) := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff, ← coe_eq_empty, ← coe_eq_univ]
  simp only [coe_inf, coe_sup, coe_comap, ← Set.preimage_inter, ← Set.preimage_union,
    Set.preimage_eq_empty_iff, Set.preimage_eq_univ_iff]
  exact and_comm.trans (and_congr_right' disjoint_comm)

/-- An open subset of a locally compact space is locally compact. -/
instance instLocallyCompactSpace [LocallyCompactSpace X] (U : Opens X) : LocallyCompactSpace U :=
  U.isOpen.locallyCompactSpace

/-- The open subset `⊤` of a σ-compact space is σ-compact, being a closed subspace. -/
instance sigmaCompactSpace_top [SigmaCompactSpace X] : SigmaCompactSpace (⊤ : Opens X) :=
  IsClosed.sigmaCompactSpace (by simp)

section Order

variable {α : Type*} [TopologicalSpace α] [Preorder α] [OrderTopology α]

/-- The open interval `Set.Ioo a b` bundled as an element of `TopologicalSpace.Opens α`. -/
def Ioo (a b : α) : Opens α :=
  ⟨Set.Ioo a b, isOpen_Ioo' a b⟩

/-- The underlying set of `TopologicalSpace.Opens.Ioo a b` is `Set.Ioo a b`. -/
@[simp, norm_cast]
theorem coe_Ioo (a b : α) : (Opens.Ioo a b : Set α) = Set.Ioo a b :=
  (rfl)

/-- Membership in `TopologicalSpace.Opens.Ioo a b` is `a < x ∧ x < b`. -/
@[simp]
theorem mem_Ioo {a b x : α} : x ∈ Opens.Ioo a b ↔ a < x ∧ x < b :=
  Iff.rfl

end Order

end TopologicalSpace.Opens

namespace TopologicalSpace.Opens.IsBasis

variable {X : Type*} [TopologicalSpace X] {B : Set (Opens X)}

/-- A compact subset of an open set has a neighbourhood which is a finite union of basis
members and is contained in that open set. -/
theorem exists_finset_sup_le_of_isCompact (hB : Opens.IsBasis B) {K : Set X}
    (hK : IsCompact K) {U : Opens X} (hKU : K ⊆ U) :
    ∃ s : Finset (Opens X), (∀ V ∈ s, V ∈ B) ∧ K ⊆ (s.sup id : Opens X) ∧ s.sup id ≤ U := by
  classical
  let C := {V : Opens X // V ∈ B ∧ V ≤ U}
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun V : C ↦ (V.val : Set X))
    (fun V ↦ V.val.isOpen) (fun x hx ↦ by
      obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp hB (hKU hx)
      exact Set.mem_iUnion.mpr ⟨⟨V, hV, hVU⟩, hxV⟩)
  refine ⟨s.image Subtype.val, ?_, ?_, ?_⟩
  · intro V hV
    obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hV
    exact W.property.1
  · intro x hx
    obtain ⟨V, hVs, hxV⟩ := Set.mem_iUnion₂.mp (hs hx)
    have hle : V.val ≤ (s.image Subtype.val).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨V, hVs, rfl⟩)
    exact hle hxV
  · exact Finset.sup_le fun V hV ↦ by
      obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hV
      exact W.property.2

end TopologicalSpace.Opens.IsBasis

open Set in
/-- A compact set `A` covered by open sets `U i` which meet `A` in pairwise disjoint sets meets each
of them in a compact set, so its preimage in each of them is compact. -/
theorem IsCompact.preimage_val_of_pairwise_disjoint {X ι : Type*} [TopologicalSpace X]
    {U : ι → TopologicalSpace.Opens X} {A : Set X} (hA : IsCompact A)
    (hU : Pairwise fun i k ↦ Disjoint (A ∩ U i) (A ∩ U k)) (hAU : A ⊆ ⋃ i, (U i : Set X))
    (i : ι) : IsCompact ((Subtype.val : U i → X) ⁻¹' A) := by
  -- `A` lies in `U i` together with the open union of the other `U k`, which misses `A ∩ U i`.
  refine (U i).isOpenEmbedding'.isInducing.isCompact_preimage_of_subset_union
    (V := ⋃ (k : ι) (_ : k ≠ i), (U k : Set X))
    (isOpen_iUnion fun k ↦ isOpen_iUnion fun _ ↦ (U k).isOpen) hA (fun x hx ↦ ?_) ?_
  · obtain ⟨k, hxk⟩ := mem_iUnion.1 (hAU hx)
    rw [Subtype.range_val]
    by_cases hki : k = i
    · exact .inl (hki ▸ hxk)
    · exact .inr (mem_iUnion₂.2 ⟨k, hki, hxk⟩)
  · rw [Subtype.range_val]
    refine disjoint_left.2 fun x hx hxV ↦ ?_
    obtain ⟨k, hki, hxk⟩ := mem_iUnion₂.1 hxV
    exact disjoint_left.1 (hU hki) ⟨hx.1, hxk⟩ hx

end
