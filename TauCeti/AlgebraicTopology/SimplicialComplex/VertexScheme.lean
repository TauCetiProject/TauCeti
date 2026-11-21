/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.SimplicialComplex.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Restriction

/-!
# The vertex scheme of a geometric simplicial complex

A geometric simplicial complex `K` in a module `E` over an ordered ring `𝕜` (Mathlib's
`Geometry.SimplicialComplex`) determines an abstract simplicial complex, its *vertex scheme*
`K.vertexScheme`: the vertices are the points of `K.vertices`, and a finite set of vertices is a
face exactly when it is a face of `K`. The faces of the vertex scheme correspond to the faces of
`K` (`Geometry.SimplicialComplex.vertexSchemeFaceEquiv`), the vertices of each face are affinely
independent, and a subcomplex `K ≤ L` induces a simplicial map of vertex schemes along the
inclusion of vertices.

## Main definitions

* `Geometry.SimplicialComplex.vertexScheme`: the abstract simplicial complex of a geometric one.
* `Geometry.SimplicialComplex.vertexSchemeFaceEquiv`: the faces of the vertex scheme are the faces
  of the geometric complex.
* `Geometry.SimplicialComplex.vertexSchemeInclusion`: the simplicial map of vertex schemes induced
  by a subcomplex.

## Main results

* `Geometry.SimplicialComplex.mem_faces_iff_exists_mem_vertexScheme`: the faces of `K` are exactly
  the faces of its vertex scheme.
* `Geometry.SimplicialComplex.affineIndependent_vertexScheme_face`: the vertices of a face of the
  vertex scheme are affinely independent.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (simplicial complexes and their vertex schemes).
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 3, Section 1 (the vertex scheme
  of a geometric complex).
-/

public section

open Set Function AbstractSimplicialComplex TauCeti.SetLike

namespace Geometry.SimplicialComplex

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  (K : SimplicialComplex 𝕜 E)

/-- The *vertex scheme* of a geometric simplicial complex `K`: the abstract simplicial complex on
the vertices of `K` whose faces are the faces of `K`. -/
def vertexScheme : AbstractSimplicialComplex K.vertices :=
  PreAbstractSimplicialComplex.toAbstractSimplicialComplex K.vertices
    (K.toPreAbstractSimplicialComplex.restrict K.vertices) fun v => by
      rw [PreAbstractSimplicialComplex.mem_faces,
        PreAbstractSimplicialComplex.mem_restrict_iff_map, Finset.map_singleton]
      exact v.property

/-- Forgetting singletons, the vertex scheme is the restriction of `K` to its vertices. -/
@[simp]
theorem vertexScheme_toPreAbstractSimplicialComplex :
    K.vertexScheme.toPreAbstractSimplicialComplex =
      K.toPreAbstractSimplicialComplex.restrict K.vertices :=
  (rfl)

variable {K}

/-- A finite set of vertices is a face of the vertex scheme exactly when, as a finite set of
points, it is a face of the geometric complex. -/
@[simp]
theorem mem_vertexScheme_iff {σ : Finset K.vertices} :
    σ ∈ K.vertexScheme ↔ σ.map (Embedding.subtype (· ∈ K.vertices)) ∈ K.faces := by
  rw [← mem_toPreAbstractSimplicialComplex, vertexScheme_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.mem_restrict_iff_map _ _ σ

variable (K) in
/-- The faces of the vertex scheme of `K` are the faces of `K`, read as finite sets of points. -/
noncomputable def vertexSchemeFaceEquiv : Face K.vertexScheme ≃ K.faces :=
  -- `Equiv.finsetSubtypeComm` sends a finite set of vertices to its points, mapped along the
  -- subtype embedding as in `mem_vertexScheme_iff`.
  ((Equiv.finsetSubtypeComm (· ∈ K.vertices)).subtypeEquiv fun _ => mem_vertexScheme_iff).trans
    (Equiv.subtypeSubtypeEquivSubtype fun hs _ => mem_vertices_of_mem_faces hs)

/-- The face of `K` corresponding to a face of the vertex scheme is its set of points. -/
@[simp]
theorem vertexSchemeFaceEquiv_apply_coe (σ : Face K.vertexScheme) :
    (K.vertexSchemeFaceEquiv σ : Finset E) = σ.val.map (Embedding.subtype (· ∈ K.vertices)) :=
  (rfl)

/-- The face of the vertex scheme corresponding to a face of `K` has the points of that face. -/
@[simp]
theorem map_vertexSchemeFaceEquiv_symm_apply_coe (s : K.faces) :
    (K.vertexSchemeFaceEquiv.symm s).val.map (Embedding.subtype (· ∈ K.vertices)) = s := by
  rw [← vertexSchemeFaceEquiv_apply_coe, Equiv.apply_symm_apply]

/-- The faces of a geometric complex are exactly the faces of its vertex scheme, read as finite
sets of points. -/
theorem mem_faces_iff_exists_mem_vertexScheme {s : Finset E} :
    s ∈ K.faces ↔ ∃ σ ∈ K.vertexScheme, σ.map (Embedding.subtype (· ∈ K.vertices)) = s :=
  ⟨fun hs => ⟨_, (K.vertexSchemeFaceEquiv.symm ⟨s, hs⟩).property,
      map_vertexSchemeFaceEquiv_symm_apply_coe ⟨s, hs⟩⟩,
    fun ⟨_, hσ, hs⟩ => hs ▸ mem_vertexScheme_iff.mp hσ⟩

/-- The points of a face of the vertex scheme are the points of the corresponding face of `K`. -/
theorem range_vertexScheme_face_coe (σ : Face K.vertexScheme) :
    range (fun a : σ.val => ((a : K.vertices) : E)) =
      (σ.val.map (Embedding.subtype (· ∈ K.vertices)) : Set E) := by
  ext x
  simp

/-- The vertices of a face of the vertex scheme are affinely independent points of `E`. -/
theorem affineIndependent_vertexScheme_face (σ : Face K.vertexScheme) :
    AffineIndependent 𝕜 fun a : σ.val => ((a : K.vertices) : E) :=
  (K.indep (mem_vertexScheme_iff.mp σ.property)).comp_embedding
    ⟨fun a => ⟨a.val.val, Finset.mem_map_of_mem _ a.property⟩, fun a b hab =>
      Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab))⟩

/-! ### Subcomplexes -/

attribute [local instance] Classical.decEq

/-- A subcomplex `K ≤ L` induces the simplicial map of vertex schemes sending each vertex of `K`
to itself, as a vertex of `L`. -/
noncomputable def vertexSchemeInclusion {L : SimplicialComplex 𝕜 E} (h : K ≤ L) :
    PreAbstractSimplicialComplex.SimplicialMap K.vertexScheme.toPreAbstractSimplicialComplex
      L.vertexScheme.toPreAbstractSimplicialComplex := by
  classical
  -- The vertex schemes forget to restrictions (`vertexScheme_toPreAbstractSimplicialComplex`).
  exact
    (L.toPreAbstractSimplicialComplex.restrictInclusionOfSubset (vertices_mono h)).domainRestrict
      (PreAbstractSimplicialComplex.restrict_mono h K.vertices)

/-- The simplicial map induced by a subcomplex is the inclusion of vertices. -/
@[simp]
theorem coe_vertexSchemeInclusion {L : SimplicialComplex 𝕜 E} (h : K ≤ L) :
    ⇑(vertexSchemeInclusion h) = inclusion (vertices_mono h) := by
  classical
  exact (PreAbstractSimplicialComplex.SimplicialMap.coe_domainRestrict _ _).trans
    (PreAbstractSimplicialComplex.coe_restrictInclusionOfSubset _ _)

/-- The reflexive subcomplex inclusion induces the identity vertex-scheme map. -/
@[simp]
theorem vertexSchemeInclusion_refl (h : K ≤ K) :
    vertexSchemeInclusion h = PreAbstractSimplicialComplex.SimplicialMap.id
      K.vertexScheme.toPreAbstractSimplicialComplex := by
  classical
  exact DFunLike.coe_injective (by
    rw [coe_vertexSchemeInclusion, PreAbstractSimplicialComplex.SimplicialMap.coe_id]
    exact inclusion_eq_id _)

/-- Composing subcomplex inclusions agrees with the inclusion for the transitive inequality. -/
@[simp]
theorem vertexSchemeInclusion_comp {L N : SimplicialComplex 𝕜 E}
    (hLN : L ≤ N) (hKL : K ≤ L) :
    (vertexSchemeInclusion hLN).comp (vertexSchemeInclusion hKL) =
      vertexSchemeInclusion (hKL.trans hLN) := by
  classical
  exact DFunLike.coe_injective (by
    rw [PreAbstractSimplicialComplex.SimplicialMap.coe_comp,
      coe_vertexSchemeInclusion, coe_vertexSchemeInclusion, coe_vertexSchemeInclusion]
    exact inclusion_comp_inclusion _ _)

end Geometry.SimplicialComplex
