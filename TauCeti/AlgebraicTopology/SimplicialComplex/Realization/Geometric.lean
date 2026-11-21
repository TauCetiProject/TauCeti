/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Topology.LocallyFinite
public import TauCeti.Topology.Triangulable.Basic
import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization

/-!
# Geometric simplicial complexes as realizations of their vertex schemes

A geometric simplicial complex `K` in a real vector space `E` has an underlying abstract
simplicial complex, its *vertex scheme* `K.vertexScheme`: the vertices are the vertices of `K`,
and a finite set of vertices is a face when it spans a face of `K`. The point of the abstract
realization `|K.vertexScheme|` with barycentric coordinates `x` is sent to the point
`∑ v, x v • v` of `E`. This map `K.realizationToSpace` takes values in the underlying space
`K.space` and carries each closed coordinate simplex onto the corresponding closed geometric
simplex (`Geometry.SimplicialComplex.range_realizationToSpace_faceInclusion`).

The map is a continuous bijection onto `K.space` with its subspace topology from `E`. Its inverse
need not be continuous: the realization carries the weak topology, which is finer than the
subspace topology when infinitely many simplices accumulate at a point of `K.space`. When the
closed simplices of `K` form a locally finite family in `E`, the map is closed, hence a
homeomorphism `K.realizationHomeomorph`. Thus a locally finite geometric complex triangulates
its underlying space in the abstract sense of `TauCeti.IsTriangulable`. This is how a
triangulation of a subset of an affine space by a locally finite geometric complex is turned
into a homeomorphism from the realization of an abstract simplicial complex.

## Main definitions

* `Geometry.SimplicialComplex.vertexScheme`: the abstract simplicial complex of a geometric one.
* `Geometry.SimplicialComplex.realizationToSpace`: the map from its realization to `K.space`.
* `Geometry.SimplicialComplex.realizationHomeomorph`: the homeomorphism onto `K.space`, for a
  locally finite complex.

## Main results

* `Geometry.SimplicialComplex.continuous_realizationToSpace`,
  `Geometry.SimplicialComplex.bijective_realizationToSpace`: the map is a continuous bijection.
* `Geometry.SimplicialComplex.isClosedMap_realizationToSpace`: it is closed if `K` is locally
  finite.
* `Geometry.SimplicialComplex.isTriangulable_space`: the space of a locally finite complex is
  triangulable.

## References

* J. R. Munkres, *Elements of Algebraic Topology*, Addison-Wesley (1984), §2 and §3.
-/

public section

noncomputable section

open Set Finsupp AbstractSimplicialComplex TauCeti.SetLike

namespace Geometry.SimplicialComplex

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] (K : SimplicialComplex ℝ E)

/-- The vertex scheme of a geometric simplicial complex `K`: the abstract simplicial complex on
the vertices of `K` whose faces are the vertex sets of the faces of `K`. -/
def vertexScheme : AbstractSimplicialComplex K.vertices where
  faces := {σ | σ.map (Function.Embedding.subtype _) ∈ K.faces}
  isRelLowerSet_faces σ hσ :=
    ⟨Finset.map_nonempty.1 (K.nonempty_of_mem_faces hσ), fun _ hτσ hτ =>
      K.down_closed hσ (Finset.map_subset_map.2 hτσ) (hτ.map)⟩
  singleton_mem v := by
    rw [mem_ofPred_eq, Finset.map_singleton]
    exact v.2

variable {K}

/-- A finite set of vertices is a face of the vertex scheme exactly when it spans a face. -/
@[simp]
theorem mem_vertexScheme {σ : Finset K.vertices} :
    σ ∈ K.vertexScheme ↔ σ.map (Function.Embedding.subtype _) ∈ K.faces :=
  (Iff.rfl)

/-- Every face of a geometric simplicial complex is spanned by a face of its vertex scheme. -/
theorem exists_mem_vertexScheme_map_eq {s : Finset E} (hs : s ∈ K.faces) :
    ∃ σ ∈ K.vertexScheme, σ.map (Function.Embedding.subtype _) = s := by
  classical
  have h : ∀ x ∈ s, x ∈ K.vertices := fun x hx =>
    K.down_closed hs (Finset.singleton_subset_iff.2 hx) (Finset.singleton_nonempty x)
  exact ⟨s.subtype (· ∈ K.vertices), by rwa [mem_vertexScheme, Finset.subtype_map_of_mem h],
    Finset.subtype_map_of_mem h⟩

/-- The vertices of a face of the vertex scheme are affinely independent. -/
private theorem affineIndependent_coe {σ : Finset K.vertices} (hσ : σ ∈ K.vertexScheme) :
    AffineIndependent ℝ (fun a : σ => (a.1 : E)) :=
  (K.indep hσ).comp_embedding ⟨fun a => ⟨a.1.1, Finset.mem_map_of_mem _ a.2⟩,
    fun _ _ h => Subtype.ext (Subtype.ext (Subtype.mk.inj h))⟩

/-- On a closed coordinate simplex, the vertex combination is a finite sum over its vertices. -/
private theorem linearCombination_eq_fintype {σ : Finset K.vertices} (y : StandardSimplex σ) :
    linearCombination ℝ ((↑) : K.vertices → E) y.1 =
      Fintype.linearCombination ℝ (fun a : σ => (a.1 : E)) fun a => y.1 a := by
  rw [linearCombination_apply_of_mem_supported ℝ
      ((mem_supported ℝ _).2 (Finset.coe_subset.2 (StandardSimplex.support_subset y))),
    Fintype.linearCombination_apply, ← Finset.sum_coe_sort σ]

/-- The vertex combination maps a closed coordinate simplex onto the closed geometric simplex
spanned by the same vertices. -/
private theorem range_linearCombination (σ : Finset K.vertices) :
    range (fun y : StandardSimplex σ => linearCombination ℝ ((↑) : K.vertices → E) y.1) =
      convexHull ℝ (σ.map (Function.Embedding.subtype _) : Set E) := by
  have h : range (fun a : σ => (a.1 : E)) = (σ.map (Function.Embedding.subtype _) : Set E) := by
    ext x
    simp
  simp_rw [linearCombination_eq_fintype, ← h]
  exact Finset.range_linearCombination_standardSimplex _

/-- The vertex combination is injective on the closed coordinate simplex of a face. -/
private theorem injective_linearCombination {σ : Finset K.vertices} (hσ : σ ∈ K.vertexScheme) :
    Function.Injective
      fun y : StandardSimplex σ => linearCombination ℝ ((↑) : K.vertices → E) y.1 := by
  simp_rw [linearCombination_eq_fintype]
  exact Finset.injective_linearCombination_standardSimplex (affineIndependent_coe hσ)

/-- A point of the realization lies in the closed coordinate simplex of its carrier. -/
private def toCarrier (x : Realization K.vertexScheme) :
    StandardSimplex (carrier K.vertexScheme x).1 :=
  ⟨x.1, mem_convexHull_carrier K.vertexScheme x⟩

variable (K) in
/-- The map from the realization of the vertex scheme of `K` to the underlying space of `K`,
sending the point with barycentric coordinates `x` to `∑ v, x v • v`. -/
def realizationToSpace (x : Realization K.vertexScheme) : K.space :=
  ⟨linearCombination ℝ ((↑) : K.vertices → E) x.1,
    convexHull_subset_space (carrier K.vertexScheme x).2 <|
      range_linearCombination (carrier K.vertexScheme x).1 ▸ mem_range_self (toCarrier x)⟩

/-- A point of the realization goes to the combination of the vertices with its barycentric
coordinates as weights. -/
@[simp]
theorem coe_realizationToSpace (x : Realization K.vertexScheme) :
    (K.realizationToSpace x : E) = linearCombination ℝ ((↑) : K.vertices → E) x.1 :=
  (rfl)

/-- Each vertex of the realization goes to the corresponding vertex of `K`. -/
@[simp]
theorem realizationToSpace_vertex (v : K.vertices) :
    K.realizationToSpace (vertex K.vertexScheme v) = ⟨v, vertices_subset_space v.2⟩ := by
  ext
  simp

/-- The closed coordinate simplex of a face of the vertex scheme goes onto the closed geometric
simplex spanned by the same vertices. -/
theorem range_realizationToSpace_faceInclusion (σ : Face K.vertexScheme) :
    range (fun y => (K.realizationToSpace (faceInclusion K.vertexScheme σ y) : E)) =
      convexHull ℝ (σ.1.map (Function.Embedding.subtype _) : Set E) := by
  simp_rw [coe_realizationToSpace, faceInclusion_val]
  exact range_linearCombination σ.1

/-- The map from the realization of the vertex scheme to the space of `K` is bijective. -/
theorem bijective_realizationToSpace : Function.Bijective K.realizationToSpace := by
  classical
  -- The coordinate simplices are spanned using classical equality of vertices.
  let : DecidableEq K.vertices := Classical.decEq _
  refine ⟨fun x x' hxx' => ?_, fun y => ?_⟩
  · -- Both points are carried by the face spanned by the intersection of their carriers.
    let σ := carrier K.vertexScheme x
    let τ := carrier K.vertexScheme x'
    have hxx'' : linearCombination ℝ ((↑) : K.vertices → E) x.1 =
        linearCombination ℝ ((↑) : K.vertices → E) x'.1 :=
      congrArg Subtype.val hxx'
    have hy : linearCombination ℝ ((↑) : K.vertices → E) x.1 ∈
        convexHull ℝ ((σ.1 ∩ τ.1).map (Function.Embedding.subtype _) : Set E) := by
      rw [Finset.map_inter, Finset.coe_inter, ← K.convexHull_inter_convexHull σ.2 τ.2]
      refine ⟨range_linearCombination σ.1 ▸ mem_range_self (toCarrier x), ?_⟩
      rw [← range_linearCombination τ.1, hxx'']
      exact mem_range_self (toCarrier x')
    obtain ⟨z, hz⟩ := range_linearCombination (σ.1 ∩ τ.1) ▸ hy
    have hσ : x.1 = z.1 := congrArg Subtype.val <| injective_linearCombination σ.2
      (a₁ := toCarrier x) (a₂ := ⟨z.1, convexHull_mono
        (Finset.coe_subset.2 (Finset.image_subset_image Finset.inter_subset_left)) z.2⟩) hz.symm
    have hτ : x'.1 = z.1 := congrArg Subtype.val <| injective_linearCombination τ.2
      (a₁ := toCarrier x') (a₂ := ⟨z.1, convexHull_mono
        (Finset.coe_subset.2 (Finset.image_subset_image Finset.inter_subset_right)) z.2⟩)
      (hz.trans hxx'').symm
    exact Subtype.ext (hσ.trans hτ.symm)
  · obtain ⟨s, hs, hys⟩ := mem_space_iff.1 y.2
    obtain ⟨σ, hσ, rfl⟩ := exists_mem_vertexScheme_map_eq hs
    obtain ⟨z, hz⟩ := range_realizationToSpace_faceInclusion ⟨σ, hσ⟩ ▸ hys
    exact ⟨_, Subtype.ext hz⟩

variable [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- The map from the realization of the vertex scheme to the space of `K` is continuous for the
weak topology on the realization. -/
@[fun_prop]
theorem continuous_realizationToSpace : Continuous K.realizationToSpace := by
  refine continuous_iff_faceInclusion.2 fun σ => continuous_induced_rng.2 ?_
  have h : Subtype.val ∘ K.realizationToSpace ∘ faceInclusion K.vertexScheme σ =
      fun y => ∑ a : σ.1, y.1 a • (a.1 : E) := by
    ext y
    simp [linearCombination_eq_fintype, Fintype.linearCombination_apply]
  have hc (v : K.vertices) : Continuous fun y : StandardSimplex σ.1 => y.1 v :=
    (continuous_apply v).comp continuous_induced_dom
  rw [h]
  exact continuous_finsetSum _ fun a _ => (hc a).smul continuous_const

variable [T2Space E]

/-- If the closed simplices of `K` form a locally finite family, then the map from the
realization of the vertex scheme to the space of `K` is closed. -/
theorem isClosedMap_realizationToSpace
    (hK : LocallyFinite fun s : K.faces => convexHull ℝ (s : Set E)) :
    IsClosedMap K.realizationToSpace := by
  intro C hC
  let g (σ : Face K.vertexScheme) := K.realizationToSpace ∘ faceInclusion K.vertexScheme σ
  -- The image of `C` is the union of the images of its traces on the closed simplices.
  have hunion : K.realizationToSpace '' C =
      ⋃ σ : Face K.vertexScheme, g σ '' (faceInclusion K.vertexScheme σ ⁻¹' C) := by
    refine Subset.antisymm ?_ (iUnion_subset fun σ => ?_)
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : faceInclusion K.vertexScheme _ (toCarrier x) = x :=
        Subtype.ext (faceInclusion_val _ _ _)
      exact mem_iUnion.2 ⟨carrier K.vertexScheme x, toCarrier x, by rwa [mem_preimage, hx'],
        by simp only [g, Function.comp_apply, hx']⟩
    · rw [image_comp]
      exact image_mono (image_preimage_subset _ _)
  -- Each trace lands in the closed geometric simplex of its face, and these are locally finite.
  have hlf : LocallyFinite fun σ : Face K.vertexScheme =>
      ((↑) : K.space → E) ⁻¹' convexHull ℝ (σ.1.map (Function.Embedding.subtype _) : Set E) := by
    have hinj : Function.Injective fun σ : Face K.vertexScheme =>
        (⟨σ.1.map (Function.Embedding.subtype _), mem_vertexScheme.1 σ.2⟩ : K.faces) :=
      fun σ τ h => Subtype.ext (Finset.map_injective _ (congrArg Subtype.val h))
    exact (hK.comp_injective hinj).preimage_continuous continuous_subtype_val
  rw [hunion]
  refine (hlf.subset fun σ => ?_).isClosed_iUnion fun σ => ?_
  · rintro _ ⟨y, -, rfl⟩
    rw [mem_preimage, ← range_realizationToSpace_faceInclusion σ]
    exact mem_range_self y
  · have : CompactSpace (StandardSimplex σ.1) :=
      (Finset.standardSimplexHomeomorph σ.1).symm.compactSpace
    exact ((hC.preimage (continuous_faceInclusion _ σ)).isCompact.image
      (continuous_realizationToSpace.comp (continuous_faceInclusion _ σ))).isClosed

variable (K) in
/-- A locally finite geometric simplicial complex is homeomorphic to the realization of its
vertex scheme, with the subspace topology on its space. -/
def realizationHomeomorph (hK : LocallyFinite fun s : K.faces => convexHull ℝ (s : Set E)) :
    Realization K.vertexScheme ≃ₜ K.space :=
  (Equiv.ofBijective _ bijective_realizationToSpace).toHomeomorphOfContinuousClosed
    continuous_realizationToSpace (isClosedMap_realizationToSpace hK)

/-- The homeomorphism is the map `K.realizationToSpace`. -/
@[simp]
theorem coe_realizationHomeomorph
    (hK : LocallyFinite fun s : K.faces => convexHull ℝ (s : Set E)) :
    ⇑(K.realizationHomeomorph hK) = K.realizationToSpace :=
  (rfl)

/-- The inverse homeomorphism sends each vertex of `K` to the corresponding vertex of the
realization. -/
@[simp]
theorem realizationHomeomorph_symm_apply_vertex
    (hK : LocallyFinite fun s : K.faces => convexHull ℝ (s : Set E)) (v : K.vertices) :
    (K.realizationHomeomorph hK).symm ⟨v, vertices_subset_space v.2⟩ =
      vertex K.vertexScheme v :=
  (Homeomorph.symm_apply_eq _).2 (realizationToSpace_vertex v).symm

variable (K) in
/-- The underlying space of a locally finite geometric simplicial complex is triangulable. -/
theorem isTriangulable_space (hK : LocallyFinite fun s : K.faces => convexHull ℝ (s : Set E)) :
    TauCeti.IsTriangulable.{u} K.space :=
  (TauCeti.isTriangulable_iff _).2 ⟨K.vertices, K.vertexScheme, ⟨K.realizationHomeomorph hK⟩⟩

end Geometry.SimplicialComplex
