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
subtype inclusion is simplicial; in particular, finite vertex restrictions give finite
models inside arbitrary complexes without adjoining unused ambient vertices.
-/

public section

open Set TauCeti.SetLike

namespace PreAbstractSimplicialComplex

variable {ι : Type*}

/-- Restrict a precomplex to a set of vertices, changing the vertex type to that set. -/
def restrict (K : PreAbstractSimplicialComplex ι) (s : Set ι) :
    PreAbstractSimplicialComplex s where
  faces := {σ | σ.map (Function.Embedding.subtype (· ∈ s)) ∈ K}
  isRelLowerSet_faces := by
    intro σ hσ
    refine ⟨Finset.map_nonempty.mp (K.isRelLowerSet_faces hσ).1, fun {τ} hτσ hτ => ?_⟩
    exact (K.isRelLowerSet_faces hσ).2 (Finset.map_subset_map.mpr hτσ) hτ.map

/-- A face in the restriction is a face after forgetting the vertex-membership proofs. -/
@[simp]
theorem mem_restrict_iff [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) (s : Set ι)
    (σ : Finset s) :
    σ ∈ K.restrict s ↔ σ.image Subtype.val ∈ K := by
  have hmap : σ.map (Function.Embedding.subtype (· ∈ s)) = σ.image Subtype.val := by
    rw [Finset.map_eq_image, Function.Embedding.coe_subtype]
  exact hmap ▸ Iff.rfl

/-- The canonical simplicial inclusion of a vertex restriction into the original precomplex. -/
def restrictInclusion [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) (s : Set ι) :
    SimplicialMap (K.restrict s) K where
  toFun := Subtype.val
  map_face' := fun _ hσ => (mem_restrict_iff K s _).mp hσ

/-- The canonical inclusion of a vertex restriction acts on vertices by `Subtype.val`. -/
@[simp]
theorem coe_restrictInclusion [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) (s : Set ι) :
    ⇑(K.restrictInclusion s) = Subtype.val := (rfl)

/-- Relabeling the restricted precomplex into the original vertex type gives exactly the faces
of the original precomplex contained in the chosen set. -/
@[simp]
theorem mem_map_restrict_iff [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) (s : Set ι)
    (σ : Finset ι) :
    σ ∈ (K.restrict s).map (Subtype.val : s → ι) ↔ σ ∈ K ∧ (σ : Set ι) ⊆ s := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    refine ⟨(mem_restrict_iff K s τ).mp hτ, ?_⟩
    rintro v hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact w.2
  · rintro ⟨hσ, hs⟩
    classical
    have heq : (σ.subtype (· ∈ s)).image Subtype.val = σ := by
      simpa only [Finset.map_eq_image, Function.Embedding.coe_subtype] using
        Finset.subtype_map_of_mem hs
    exact mem_map_iff.mpr
      ⟨σ.subtype (· ∈ s), (mem_restrict_iff K s _).mpr (heq.symm ▸ hσ), heq⟩

/-- If every face of `K` lies in `s`, mapping `K.restrict s` along `Subtype.val` recovers `K`. -/
theorem map_restrict_eq_self [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {s : Set ι}
    (hs : ∀ σ ∈ K, (σ : Set ι) ⊆ s) :
    (K.restrict s).map (Subtype.val : s → ι) = K :=
  SetLike.ext fun σ => (mem_map_restrict_iff K s σ).trans ⟨And.left, fun hσ => ⟨hσ, hs σ hσ⟩⟩

end PreAbstractSimplicialComplex

noncomputable section

namespace AbstractSimplicialComplex

variable {ι : Type*}

attribute [local instance] Classical.decEq

/-- Restrict a complex to a set of vertices, changing the vertex type to that set. -/
def restrict (K : AbstractSimplicialComplex ι) (s : Set ι) : AbstractSimplicialComplex s where
  toPreAbstractSimplicialComplex := K.toPreAbstractSimplicialComplex.restrict s
  singleton_mem v := by
    simp only [PreAbstractSimplicialComplex.restrict, Set.mem_ofPred_eq, Finset.map_singleton,
      Function.Embedding.subtype_apply, mem_toPreAbstractSimplicialComplex]
    exact K.singleton_mem v.1

/-- Forgetting that a vertex restriction contains every singleton recovers the underlying
precomplex restriction. -/
theorem restrict_toPreAbstractSimplicialComplex (K : AbstractSimplicialComplex ι) (s : Set ι) :
    (K.restrict s).toPreAbstractSimplicialComplex = K.toPreAbstractSimplicialComplex.restrict s :=
  (rfl)

/-- A face in the restriction is a face after forgetting the vertex-membership proofs. -/
@[simp]
theorem mem_restrict_iff (K : AbstractSimplicialComplex ι) (s : Set ι) (σ : Finset s) :
    σ ∈ K.restrict s ↔ σ.image Subtype.val ∈ K :=
  PreAbstractSimplicialComplex.mem_restrict_iff K.toPreAbstractSimplicialComplex s σ

/-- The canonical simplicial inclusion of a vertex restriction into the original complex. -/
def restrictInclusion (K : AbstractSimplicialComplex ι) (s : Set ι) :
    PreAbstractSimplicialComplex.SimplicialMap
      (K.restrict s).toPreAbstractSimplicialComplex K.toPreAbstractSimplicialComplex :=
  K.toPreAbstractSimplicialComplex.restrictInclusion s

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
  DFunLike.ext _ _ fun x => by simp

/-- Relabeling the restricted complex into the original vertex type gives exactly the faces
of the original complex contained in the chosen set. -/
@[simp]
theorem mem_map_restrict_iff (K : AbstractSimplicialComplex ι) (s : Set ι) (σ : Finset ι) :
    σ ∈ (K.restrict s).toPreAbstractSimplicialComplex.map
      (Subtype.val : s → ι) ↔ σ ∈ K ∧ (σ : Set ι) ⊆ s :=
  PreAbstractSimplicialComplex.mem_map_restrict_iff K.toPreAbstractSimplicialComplex s σ

end AbstractSimplicialComplex

end
