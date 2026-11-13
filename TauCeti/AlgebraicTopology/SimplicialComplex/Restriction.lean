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

variable {ι : Type*}

/-- Restrict a precomplex to a set of vertices, changing the vertex type to that set. -/
def restrict (K : PreAbstractSimplicialComplex ι) (s : Set ι) :
    PreAbstractSimplicialComplex s where
  faces := {σ | σ.map (Function.Embedding.subtype (· ∈ s)) ∈ K}
  isRelLowerSet_faces := fun {_} hσ =>
    ⟨Finset.map_nonempty.mp (K.isRelLowerSet_faces hσ).1,
      fun {_} hτσ hτ =>
        (K.isRelLowerSet_faces hσ).2 (Finset.map_subset_map.mpr hτσ) (Finset.map_nonempty.mpr hτ)⟩

/-- A face in the vertex restriction is a face after forgetting the vertex-membership proofs. -/
@[simp]
theorem mem_restrict_iff [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) (s : Set ι)
    (σ : Finset s) : σ ∈ K.restrict s ↔ σ.image Subtype.val ∈ K := by
  change σ.map (Function.Embedding.subtype (· ∈ s)) ∈ K ↔ _
  rw [Finset.map_eq_image, Function.Embedding.coe_subtype]

/-- The canonical simplicial inclusion of a vertex restriction into the original precomplex. -/
def restrictInclusion [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) (s : Set ι) :
    SimplicialMap (K.restrict s) K where
  toFun := Subtype.val
  map_face' := fun _ hσ => (mem_restrict_iff K s _).mp hσ

/-- The inclusion of a vertex restriction acts on vertices by `Subtype.val`. -/
@[simp]
theorem coe_restrictInclusion [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) (s : Set ι) :
    ⇑(K.restrictInclusion s) = Subtype.val := (rfl)

/-- The simplicial inclusion between vertex restrictions induced by an inclusion of vertex sets. -/
def restrictInclusionOfSubset (K : PreAbstractSimplicialComplex ι) {s t : Set ι} [DecidableEq t]
    (hst : s ⊆ t) : SimplicialMap (K.restrict s) (K.restrict t) where
  toFun := Set.inclusion hst
  map_face' σ hσ := by
    let _ := Classical.decEq ι
    rw [mem_restrict_iff] at hσ ⊢
    rwa [Finset.image_image, Set.val_comp_inclusion]

/-- The inclusion between vertex restrictions acts on vertices by `Set.inclusion`. -/
@[simp]
theorem coe_restrictInclusionOfSubset (K : PreAbstractSimplicialComplex ι) {s t : Set ι}
    [DecidableEq t] (hst : s ⊆ t) :
    ⇑(K.restrictInclusionOfSubset hst) = Set.inclusion hst := (rfl)

/-- Including a smaller vertex restriction into a larger one and then into the original precomplex
is the inclusion of the smaller restriction. -/
@[simp]
theorem restrictInclusion_comp_restrictInclusionOfSubset [DecidableEq ι]
    (K : PreAbstractSimplicialComplex ι) {s t : Set ι} [DecidableEq t] (hst : s ⊆ t) :
    (K.restrictInclusion t).comp (K.restrictInclusionOfSubset hst) = K.restrictInclusion s :=
  DFunLike.ext _ _ fun x => SimplicialMap.comp_apply _ _ x

/-- Relabeling the restricted precomplex into the original vertex type gives exactly the faces of
the original precomplex contained in the chosen set. -/
@[simp]
theorem mem_map_restrict_iff [DecidableEq ι] (K : PreAbstractSimplicialComplex ι) (s : Set ι)
    (σ : Finset ι) :
    σ ∈ (K.restrict s).map (Subtype.val : s → ι) ↔ σ ∈ K ∧ (σ : Set ι) ⊆ s := by
  let _ := Classical.decPred (· ∈ s)
  constructor
  · intro hσ
    obtain ⟨τ, hτ, rfl⟩ := mem_map_iff.mp hσ
    refine ⟨(mem_restrict_iff K s τ).mp hτ, ?_⟩
    rintro v hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact w.2
  · rintro ⟨hσ, hs⟩
    have heq : (σ.subtype (· ∈ s)).image Subtype.val = σ := by
      simpa only [Finset.map_eq_image, Function.Embedding.coe_subtype] using
        Finset.subtype_map_of_mem hs
    exact mem_map_iff.mpr
      ⟨σ.subtype (· ∈ s), (mem_restrict_iff K s _).mpr (heq.symm ▸ hσ), heq⟩

/-- When every face of `K` is contained in `s`, relabeling `K.restrict s` along `Subtype.val`
recovers `K`. -/
theorem map_val_restrict [DecidableEq ι] {K : PreAbstractSimplicialComplex ι} {s : Set ι}
    (hs : ∀ τ ∈ K, (τ : Set ι) ⊆ s) :
    (K.restrict s).map (Subtype.val : s → ι) = K :=
  SetLike.ext fun τ => (mem_map_restrict_iff K s τ).trans ⟨And.left, fun hτ => ⟨hτ, hs τ hτ⟩⟩

/-- When every face of `K` is contained in `s` and `s ⊆ t`, mapping `K.restrict s` along
`Set.inclusion hst` gives `K.restrict t`. -/
theorem map_inclusion_restrict {K : PreAbstractSimplicialComplex ι} {s t : Set ι} [DecidableEq t]
    (hs : ∀ τ ∈ K, (τ : Set ι) ⊆ s) (hst : s ⊆ t) :
    (K.restrict s).map (Set.inclusion hst) = K.restrict t := by
  let _ := Classical.decEq ι
  rw [← map_inj_of_injective Subtype.val Subtype.val_injective, map_map, Set.val_comp_inclusion]
  exact (map_val_restrict hs).trans
    (map_val_restrict fun τ hτ => (hs τ hτ).trans hst).symm

end PreAbstractSimplicialComplex

noncomputable section

namespace AbstractSimplicialComplex

variable {ι : Type*}

attribute [local instance] Classical.decEq

/-- Restrict a complex to a set of vertices, changing the vertex type to that set. -/
def restrict (K : AbstractSimplicialComplex ι) (s : Set ι) : AbstractSimplicialComplex s :=
  PreAbstractSimplicialComplex.toAbstractSimplicialComplex s
    (PreAbstractSimplicialComplex.restrict K.toPreAbstractSimplicialComplex s) fun v => by
      change ({v} : Finset s) ∈
        PreAbstractSimplicialComplex.restrict K.toPreAbstractSimplicialComplex s
      rw [PreAbstractSimplicialComplex.mem_restrict_iff, Finset.image_singleton,
        mem_toPreAbstractSimplicialComplex]
      exact K.singleton_mem v.1

/-- Forgetting singletons commutes with restricting the vertex set. -/
@[simp]
theorem restrict_toPreAbstractSimplicialComplex (K : AbstractSimplicialComplex ι) (s : Set ι) :
    (K.restrict s).toPreAbstractSimplicialComplex =
      PreAbstractSimplicialComplex.restrict K.toPreAbstractSimplicialComplex s :=
  (rfl)

/-- A face in the restriction is a face after forgetting the vertex-membership proofs. -/
@[simp]
theorem mem_restrict_iff (K : AbstractSimplicialComplex ι) (s : Set ι) (σ : Finset s) :
    σ ∈ K.restrict s ↔ σ.image Subtype.val ∈ K := by
  rw [← mem_toPreAbstractSimplicialComplex, restrict_toPreAbstractSimplicialComplex,
    PreAbstractSimplicialComplex.mem_restrict_iff, mem_toPreAbstractSimplicialComplex]

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
      (K.restrict t).toPreAbstractSimplicialComplex :=
  K.toPreAbstractSimplicialComplex.restrictInclusionOfSubset hst

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
  K.toPreAbstractSimplicialComplex.restrictInclusion_comp_restrictInclusionOfSubset hst

/-- Relabeling the restricted complex into the original vertex type gives exactly the faces
of the original complex contained in the chosen set. -/
theorem mem_map_restrict_iff (K : AbstractSimplicialComplex ι) (s : Set ι) (σ : Finset ι) :
    σ ∈ (K.restrict s).toPreAbstractSimplicialComplex.map
      (Subtype.val : s → ι) ↔ σ ∈ K ∧ (σ : Set ι) ⊆ s := by
  rw [restrict_toPreAbstractSimplicialComplex, PreAbstractSimplicialComplex.mem_map_restrict_iff,
    mem_toPreAbstractSimplicialComplex]

end AbstractSimplicialComplex

end
