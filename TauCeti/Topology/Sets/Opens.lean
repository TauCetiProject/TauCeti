/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Sets.Opens

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
* `TopologicalSpace.Opens.le_iSup_iff_subset_iUnion` : an open set lies below the supremum of a
  family of open sets exactly when their underlying sets cover it.
* `TopologicalSpace.Opens.sigmaCompactSpace_top` : the open subset `⊤` of a σ-compact space is
  σ-compact.
* `TopologicalSpace.Opens.IsBasis.exists_finset_sup_le_of_isCompact` : a compact subset of an
  open set has a neighbourhood inside it which is a finite union of basis members.
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
  ⟨⟨(↑) '' W, Ω.isOpen.isOpenMap_subtype_val W hW⟩, Subtype.coe_image_subset _ _,
    Set.preimage_image_eq W Subtype.val_injective⟩

/-- An open set lies below the supremum of a family of open sets exactly when their underlying
sets cover it. -/
theorem le_iSup_iff_subset_iUnion {ι : Sort*} {U : Opens X} {V : ι → Opens X} :
    U ≤ ⨆ i, V i ↔ (U : Set X) ⊆ ⋃ i, (V i : Set X) := by
  rw [← SetLike.coe_subset_coe, coe_iSup]

/-- The open subset `⊤` of a σ-compact space is σ-compact, being a closed subspace. -/
instance sigmaCompactSpace_top [SigmaCompactSpace X] : SigmaCompactSpace (⊤ : Opens X) :=
  IsClosed.sigmaCompactSpace (by simp)

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
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun V : C ↦ (V.1 : Set X))
    (fun V ↦ V.1.isOpen) (fun x hx ↦ by
      obtain ⟨V, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.mp hB (hKU hx)
      exact Set.mem_iUnion.mpr ⟨⟨V, hV, hVU⟩, hxV⟩)
  refine ⟨s.image Subtype.val, ?_, ?_, ?_⟩
  · intro V hV
    obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hV
    exact W.2.1
  · intro x hx
    obtain ⟨V, hVs, hxV⟩ := Set.mem_iUnion₂.mp (hs hx)
    have hle : V.1 ≤ (s.image Subtype.val).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image.mpr ⟨V, hVs, rfl⟩)
    exact hle hxV
  · exact Finset.sup_le fun V hV ↦ by
      obtain ⟨W, _, rfl⟩ := Finset.mem_image.mp hV
      exact W.2.2

end TopologicalSpace.Opens.IsBasis

end
