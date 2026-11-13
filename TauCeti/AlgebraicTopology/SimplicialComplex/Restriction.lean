/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Maps

/-!
# Restricting the vertices of a simplicial complex

The restriction of a simplicial complex (or precomplex) to a set of vertices is a complex on
that set as a subtype. Its faces are precisely the original faces using only those vertices. The
subtype inclusion is simplicial; in particular, finite vertex restrictions give finite models
inside arbitrary complexes without adjoining unused ambient vertices, and restricting a
precomplex to its vertex set produces an `AbstractSimplicialComplex` with no extra singletons.
-/

public section

namespace PreAbstractSimplicialComplex

variable {ι : Type*}

/-- Restrict a precomplex to a set of vertices, changing the vertex type to that set. -/
def restrict (K : PreAbstractSimplicialComplex ι) (s : Set ι) :
    PreAbstractSimplicialComplex s where
  faces := {σ | σ.map (Function.Embedding.subtype (· ∈ s)) ∈ K}
  isRelLowerSet_faces := by
    intro σ hσ
    refine ⟨Finset.map_nonempty.mp (K.isRelLowerSet_faces hσ).1, fun {τ} hτσ hτ => ?_⟩
    exact (K.isRelLowerSet_faces hσ).2 (Finset.map_subset_map.mpr hτσ)
      (Finset.map_nonempty.mpr hτ)

/-- A face in the restriction is a face after forgetting the vertex-membership proofs. -/
@[simp]
theorem mem_restrict_iff (K : PreAbstractSimplicialComplex ι) (s : Set ι) (σ : Finset s) :
    σ ∈ K.restrict s ↔ σ.map (Function.Embedding.subtype (· ∈ s)) ∈ K :=
  Iff.rfl

/-- With decidable equality on the ambient type, membership in the vertex restriction is tested
by `Finset.image Subtype.val`. -/
theorem mem_restrict_iff_image [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) (s : Set ι)
    (σ : Finset s) : σ ∈ K.restrict s ↔ σ.image Subtype.val ∈ K := by
  rw [mem_restrict_iff, Finset.map_eq_image]
  rfl

/-- Relabeling a restricted precomplex into the original vertex type gives exactly the faces of
the original precomplex contained in the chosen vertex set. -/
@[simp]
theorem mem_map_restrict_iff [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) (s : Set ι)
    (σ : Finset ι) :
    σ ∈ (K.restrict s).map (Subtype.val : s → ι) ↔ σ ∈ K ∧ (σ : Set ι) ⊆ s := by
  constructor
  · intro hσ
    obtain ⟨τ, hτ, rfl⟩ := mem_map_iff.mp hσ
    refine ⟨(mem_restrict_iff_image K s τ).mp hτ, ?_⟩
    rintro v hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact w.2
  · rintro ⟨hσ, hs⟩
    classical
    have heq : (σ.subtype (· ∈ s)).image Subtype.val = σ := by
      simpa only [Finset.map_eq_image, Function.Embedding.coe_subtype] using
        Finset.subtype_map_of_mem (fun x hx => hs hx)
    exact mem_map_iff.mpr
      ⟨σ.subtype (· ∈ s), (mem_restrict_iff_image K s _).mpr (heq.symm ▸ hσ), heq⟩

/-- Relabeling a vertex restriction back into the ambient vertex type gives a subcomplex. -/
theorem map_restrict_le [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) (s : Set ι) :
    (K.restrict s).map (Subtype.val : s → ι) ≤ K :=
  fun _ hσ => ((mem_map_restrict_iff K s _).mp hσ).1

/-- If every face of `K` uses only vertices in `s`, relabeling `K.restrict s` back into `ι`
recovers `K`. -/
theorem map_restrict_eq_of_subset [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {s : Set ι}
    (hs : ∀ σ ∈ K, (σ : Set ι) ⊆ s) :
    (K.restrict s).map (Subtype.val : s → ι) = K := by
  refine SetLike.ext fun σ => ?_
  rw [mem_map_restrict_iff]
  exact ⟨And.left, fun hσ => ⟨hσ, hs σ hσ⟩⟩

/-- Mapping along an injective vertex map is injective on precomplexes. -/
theorem map_injective {κ : Type*} [DecidableEq κ] {f : ι → κ} (hf : Function.Injective f) :
    Function.Injective (fun K : PreAbstractSimplicialComplex ι => K.map f) := by
  intro K L hKL
  apply SetLike.ext'
  exact (Finset.image_injective hf).image_injective
    (congrArg PreAbstractSimplicialComplex.faces hKL)

/-- When `K` is already supported in `s` and `s ⊆ t`, mapping `K.restrict s` along
`Set.inclusion hst` gives `K.restrict t`. -/
theorem map_inclusion_restrict {K : PreAbstractSimplicialComplex ι} {s t : Set ι} [DecidableEq t]
    (hst : s ⊆ t) (hs : ∀ σ ∈ K, (σ : Set ι) ⊆ s) :
    (K.restrict s).map (Set.inclusion hst) = K.restrict t := by
  classical
  refine map_injective (Subtype.val_injective : Function.Injective (Subtype.val : t → ι)) ?_
  dsimp only
  rw [map_map, Set.val_comp_inclusion, map_restrict_eq_of_subset hs,
    map_restrict_eq_of_subset fun σ hσ => (hs σ hσ).trans hst]

/-- Restrict a precomplex to its set of vertices, producing an `AbstractSimplicialComplex` with
no extra isolated vertices. -/
def restrictVertices (K : PreAbstractSimplicialComplex ι) :
    AbstractSimplicialComplex ({v : ι | ({v} : Finset ι) ∈ K} : Set ι) :=
  { K.restrict {v : ι | ({v} : Finset ι) ∈ K} with
    singleton_mem v := by
      have hv : ({v.1} : Finset ι) ∈ K := v.2
      simpa only [restrict, Set.mem_ofPred_eq, Finset.map_singleton,
        Function.Embedding.coe_subtype] using hv }

/-- The underlying precomplex of `K.restrictVertices` is the restriction of `K` to its vertex
set. -/
theorem toPreAbstractSimplicialComplex_restrictVertices (K : PreAbstractSimplicialComplex ι) :
    K.restrictVertices.toPreAbstractSimplicialComplex =
      K.restrict {v : ι | ({v} : Finset ι) ∈ K} := by
  ext σ
  rfl

/-- Membership in `K.restrictVertices` is membership of the underlying vertex finset in `K`. -/
@[simp]
theorem mem_restrictVertices_iff (K : PreAbstractSimplicialComplex ι)
    (σ : Finset ({v : ι | ({v} : Finset ι) ∈ K} : Set ι)) :
    σ ∈ K.restrictVertices ↔
      σ.map (Function.Embedding.subtype (· ∈ ({v : ι | ({v} : Finset ι) ∈ K} : Set ι))) ∈ K := by
  rw [← AbstractSimplicialComplex.mem_toPreAbstractSimplicialComplex,
    toPreAbstractSimplicialComplex_restrictVertices, mem_restrict_iff]

/-- Relabeling `K.restrictVertices` back into the ambient vertex type recovers `K`. -/
theorem map_restrictVertices [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) :
    K.restrictVertices.toPreAbstractSimplicialComplex.map Subtype.val = K :=
  map_restrict_eq_of_subset fun _ hσ _ hv => singleton_mem_of_mem hσ hv

end PreAbstractSimplicialComplex

noncomputable section

open Set TauCeti.SetLike

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

/-- Restricting an abstract simplicial complex commutes with passing to the underlying
precomplex. -/
theorem toPreAbstractSimplicialComplex_restrict (K : AbstractSimplicialComplex ι) (s : Set ι) :
    (K.restrict s).toPreAbstractSimplicialComplex =
      K.toPreAbstractSimplicialComplex.restrict s := by
  refine SetLike.ext fun σ => ?_
  rw [mem_toPreAbstractSimplicialComplex, mem_restrict_iff,
    PreAbstractSimplicialComplex.mem_restrict_iff_image, mem_toPreAbstractSimplicialComplex]

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
  rw [toPreAbstractSimplicialComplex_restrict, PreAbstractSimplicialComplex.mem_map_restrict_iff,
    mem_toPreAbstractSimplicialComplex]

end AbstractSimplicialComplex
