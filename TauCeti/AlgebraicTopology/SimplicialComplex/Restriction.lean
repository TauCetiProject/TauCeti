/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Maps

/-!
# Restricting the vertices of a simplicial complex

The restriction of a pre-abstract or abstract simplicial complex to a set of vertices is a complex
on that set as a subtype. Its faces are precisely the original faces using only those vertices. The
subtype inclusion is simplicial; in particular, finite vertex restrictions give finite models inside
arbitrary complexes without adjoining unused ambient vertices.
-/

public section

open Set TauCeti.SetLike

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [DecidableEq ι]

/-- Restrict a precomplex to a set of vertices, changing the vertex type to that set. -/
def restrict (K : PreAbstractSimplicialComplex ι) (s : Set ι) :
    PreAbstractSimplicialComplex s where
  faces := {σ | σ.image Subtype.val ∈ K}
  isRelLowerSet_faces := fun {_} hσ =>
    ⟨Finset.image_nonempty.mp (K.isRelLowerSet_faces.prop_of_mem hσ),
      fun _ hτσ hτ => K.isRelLowerSet_faces.mem_of_le hσ (Finset.image_mono _ hτσ) (hτ.image _)⟩

/-- A face in the restriction is a face after forgetting the vertex-membership proofs. -/
@[simp]
theorem mem_restrict_iff (K : PreAbstractSimplicialComplex ι) (s : Set ι) (σ : Finset s) :
    σ ∈ K.restrict s ↔ σ.image Subtype.val ∈ K := (Iff.rfl)

/-- Relabeling the restricted precomplex into the original vertex type gives the faces of the
original precomplex contained in `s`. -/
@[simp]
theorem mem_map_restrict_iff (K : PreAbstractSimplicialComplex ι) (s : Set ι) (σ : Finset ι) :
    σ ∈ (K.restrict s).map (Subtype.val : s → ι) ↔ σ ∈ K ∧ (σ : Set ι) ⊆ s := by
  classical
  constructor
  · intro hσ
    obtain ⟨τ, hτ, rfl⟩ := mem_map_iff.mp hσ
    refine ⟨(mem_restrict_iff K s τ).mp hτ, fun v hv => ?_⟩
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact w.2
  · rintro ⟨hσ, hs⟩
    have heq : (σ.subtype (· ∈ s)).image Subtype.val = σ := by
      simpa only [Finset.map_eq_image, Function.Embedding.coe_subtype] using
        Finset.subtype_map_of_mem hs
    exact mem_map_iff.mpr ⟨σ.subtype (· ∈ s), (mem_restrict_iff K s _).mpr (heq.symm ▸ hσ), heq⟩

/-- When every face of `K` lies in `s`, mapping `K.restrict s` back by `Subtype.val` recovers
`K`. -/
theorem map_val_restrict_of_subset (K : PreAbstractSimplicialComplex ι) {s : Set ι}
    (hs : ∀ σ ∈ K, (σ : Set ι) ⊆ s) :
    (K.restrict s).map (Subtype.val : s → ι) = K :=
  SetLike.ext fun σ => (mem_map_restrict_iff K s σ).trans
    ⟨And.left, fun hσ => ⟨hσ, hs σ hσ⟩⟩

/-- When every face of `K` lies in `s` and `s ⊆ t`, mapping `K.restrict s` along `Set.inclusion`
gives `K.restrict t`. -/
theorem map_inclusion_restrict_of_subset (K : PreAbstractSimplicialComplex ι) {s t : Set ι}
    (hst : s ⊆ t) [DecidableEq t] (hs : ∀ σ ∈ K, (σ : Set ι) ⊆ s) :
    (K.restrict s).map (Set.inclusion hst) = K.restrict t := by
  refine SetLike.ext fun τ => ?_
  have hinj := Finset.image_injective (Subtype.val_injective (p := (· ∈ t)))
  rw [mem_map_iff, mem_restrict_iff]
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    rwa [Finset.image_image, Set.val_comp_inclusion]
  · intro hτ
    let : DecidablePred (· ∈ s) := Classical.decPred _
    have hsub : (τ.image Subtype.val : Set ι) ⊆ s := hs _ hτ
    let ρ : Finset s := (τ.image Subtype.val).subtype (· ∈ s)
    have hρ : ρ.image Subtype.val = τ.image Subtype.val := by
      simpa only [ρ, Finset.map_eq_image, Function.Embedding.coe_subtype] using
        Finset.subtype_map_of_mem hsub
    refine ⟨ρ, (mem_restrict_iff K s ρ).mpr (hρ.symm ▸ hτ), hinj ?_⟩
    rwa [Finset.image_image, Set.val_comp_inclusion]

end PreAbstractSimplicialComplex

noncomputable section

namespace AbstractSimplicialComplex

variable {ι : Type*}

attribute [local instance] Classical.decEq

/-- Restrict a complex to a set of vertices, changing the vertex type to that set. -/
def restrict (K : AbstractSimplicialComplex ι) (s : Set ι) : AbstractSimplicialComplex s where
  faces := {σ | σ.image Subtype.val ∈ K}
  isRelLowerSet_faces := by
    intro σ hσ
    refine ⟨?_, ?_⟩
    · exact Finset.image_nonempty.mp (K.isRelLowerSet_faces.prop_of_mem hσ)
    · intro τ hτσ hτ
      exact K.isRelLowerSet_faces.mem_of_le hσ
        (Finset.image_mono _ hτσ) (hτ.image _)
  singleton_mem v := by
    simp only [Set.mem_ofPred_eq, Finset.image_singleton]
    exact K.singleton_mem v.1

/-- A face in the restriction is a face after forgetting the vertex-membership proofs. -/
@[simp]
theorem mem_restrict_iff (K : AbstractSimplicialComplex ι) (s : Set ι) (σ : Finset s) :
    σ ∈ K.restrict s ↔ σ.image Subtype.val ∈ K := (Iff.rfl)

/-- The canonical simplicial inclusion of a vertex restriction into the original complex. -/
def restrictInclusion (K : AbstractSimplicialComplex ι) (s : Set ι) :
    PreAbstractSimplicialComplex.SimplicialMap
      (K.restrict s).toPreAbstractSimplicialComplex K.toPreAbstractSimplicialComplex where
  toFun := Subtype.val
  map_face' := fun _ hσ => (mem_restrict_iff K s _).mp hσ

@[simp]
theorem coe_restrictInclusion (K : AbstractSimplicialComplex ι) (s : Set ι) :
    ⇑(K.restrictInclusion s) = Subtype.val := (rfl)

/-- The simplicial inclusion between vertex restrictions induced by an inclusion of vertex
sets. -/
def restrictInclusionOfSubset (K : AbstractSimplicialComplex ι) {s t : Set ι} (hst : s ⊆ t) :
    PreAbstractSimplicialComplex.SimplicialMap
      (K.restrict s).toPreAbstractSimplicialComplex
      (K.restrict t).toPreAbstractSimplicialComplex where
  toFun := Set.inclusion hst
  map_face' σ hσ := by
    rw [mem_toPreAbstractSimplicialComplex, mem_restrict_iff] at hσ ⊢
    rwa [Finset.image_image, Set.val_comp_inclusion]

/-- The inclusion between vertex restrictions acts on vertices by `Set.inclusion`. -/
@[simp]
theorem coe_restrictInclusionOfSubset (K : AbstractSimplicialComplex ι) {s t : Set ι}
    (hst : s ⊆ t) : ⇑(K.restrictInclusionOfSubset hst) = Set.inclusion hst := (rfl)

/-- Including a smaller vertex restriction into a larger one and then into the original complex
is the inclusion of the smaller restriction. -/
@[simp]
theorem restrictInclusion_comp_restrictInclusionOfSubset (K : AbstractSimplicialComplex ι)
    {s t : Set ι} (hst : s ⊆ t) :
    (K.restrictInclusion t).comp (K.restrictInclusionOfSubset hst) = K.restrictInclusion s :=
  DFunLike.ext _ _ fun x => PreAbstractSimplicialComplex.SimplicialMap.comp_apply _ _ x

/-- Relabeling the restricted complex into the original vertex type gives exactly the faces
of the original complex contained in the chosen set. -/
@[simp]
theorem mem_map_restrict_iff (K : AbstractSimplicialComplex ι) (s : Set ι) (σ : Finset ι) :
    σ ∈ (K.restrict s).toPreAbstractSimplicialComplex.map
      (Subtype.val : s → ι) ↔ σ ∈ K ∧ (σ : Set ι) ⊆ s := by
  classical
  constructor
  · intro hσ
    obtain ⟨τ, hτ, rfl⟩ := PreAbstractSimplicialComplex.mem_map_iff.mp hσ
    refine ⟨(mem_restrict_iff K s τ).mp hτ, ?_⟩
    rintro v hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact w.2
  · rintro ⟨hσ, hs⟩
    have heq : (σ.subtype (· ∈ s)).image Subtype.val = σ := by
      simpa only [Finset.map_eq_image, Function.Embedding.coe_subtype] using
        Finset.subtype_map_of_mem hs
    exact PreAbstractSimplicialComplex.mem_map_iff.mpr
      ⟨σ.subtype (· ∈ s), (mem_restrict_iff K s _).mpr (heq.symm ▸ hσ), heq⟩

end AbstractSimplicialComplex
