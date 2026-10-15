/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Maps

/-!
# Restricting the vertices of a simplicial complex

The restriction of an abstract simplicial complex to a set of vertices is a complex on that
set as a subtype. Its faces are precisely the original faces using only those vertices. The
subtype inclusion is simplicial; in particular, finite vertex restrictions give finite
models inside arbitrary complexes without adjoining unused ambient vertices.
-/

public section

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

/-- The canonical simplicial inclusion of a vertex restriction into the original complex. -/
def restrictInclusion (K : AbstractSimplicialComplex ι) (s : Set ι) :
    PreAbstractSimplicialComplex.SimplicialMap
      (K.restrict s).toPreAbstractSimplicialComplex K.toPreAbstractSimplicialComplex where
  toFun := Subtype.val
  map_face' := fun _ hσ => (mem_restrict_iff K s _).mp hσ

@[simp]
theorem coe_restrictInclusion (K : AbstractSimplicialComplex ι) (s : Set ι) :
    ⇑(K.restrictInclusion s) = Subtype.val := (rfl)

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
