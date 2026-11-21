/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyFinite
public import TauCeti.AlgebraicTopology.SimplicialComplex.Restriction
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization

/-!
# Realizations of geometric simplicial complexes

A geometric simplicial complex `K` in a real vector space `E` (Mathlib's
`Geometry.SimplicialComplex`) determines an abstract simplicial complex, its *vertex scheme*
`K.vertexScheme`: the vertices are the points of `K.vertices`, and a finite set of vertices is a
face exactly when it is a face of `K`. This file compares the weak realization of the vertex scheme
with the underlying space `K.space ⊆ E`.

The comparison map `K.realizationToSpace` sends a point with barycentric coordinates `x` to the
combination `∑ v, x v • v` of the vertices. It is linear in barycentric coordinates on every closed
simplex, continuous, injective, and has range `K.space`. Injectivity combines the affine
independence of the vertices of each face with the fact that the closed simplices of `K` meet in
common faces. When `K.space` is Hausdorff and the closed simplices of `K` form a locally finite
family in `K.space`, the map is a closed map onto `K.space` and gives a homeomorphism
`K.realizationHomeomorph hK : |K.vertexScheme| ≃ₜ K.space`; this covers complexes such as the
dyadic subdivision of an open ray, which accumulate only outside their underlying space. When `E`
is Hausdorff and the family is locally finite in `E` itself, the map is moreover a closed embedding
into `E`. Without local finiteness the weak topology is in general strictly finer than the subspace
topology of `K.space`: for the infinitely many edges `[0, eᵢ]` of a fan in `ℓ²`, the points at
parameter `1 / i` on the `i`-th edge converge to `0` in `E`, but form a closed set in the weak
topology.

This is how polyhedra built inside a vector space, by subdividing, intersecting or gluing geometric
complexes, become triangulations in the sense of `TauCeti.IsTriangulable`, whose domain is the
realization of an abstract complex. In particular the rectilinear complexes in coordinate charts
from which a smooth triangulation of a manifold is assembled are read as abstract complexes this
way.

## Main definitions

* `Geometry.SimplicialComplex.vertexScheme`: the abstract simplicial complex of a geometric one.
* `Geometry.SimplicialComplex.realizationToSpace`: the map from the realization of the vertex
  scheme into the ambient space.
* `Geometry.SimplicialComplex.realizationHomeomorph`: for a complex locally finite in its
  underlying space, the homeomorphism from the realization of its vertex scheme onto that space.

## Main results

* `Geometry.SimplicialComplex.mem_faces_iff_exists_mem_vertexScheme`: the faces of `K` are exactly
  the faces of its vertex scheme.
* `Geometry.SimplicialComplex.injective_realizationToSpace`,
  `Geometry.SimplicialComplex.range_realizationToSpace`: the comparison map is a bijection onto
  `K.space`.
* `Geometry.SimplicialComplex.isClosedMap_codRestrict_realizationToSpace`: for a complex locally
  finite in its underlying space, the comparison map onto `K.space` is closed.
* `Geometry.SimplicialComplex.isClosedEmbedding_realizationToSpace`: for a complex locally finite
  in `E`, the comparison map is a closed embedding.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (simplicial complexes, their vertex schemes and their polyhedra).
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 3, Section 1 (the vertex scheme
  of a geometric complex and its realization).
-/

public section

noncomputable section

open Set Function Topology AbstractSimplicialComplex TauCeti.SetLike

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (K : SimplicialComplex ℝ E)

/-! ### The vertex scheme -/

/-- The *vertex scheme* of a geometric simplicial complex `K`: the abstract simplicial complex on
the vertices of `K` whose faces are the faces of `K`. -/
def vertexScheme : AbstractSimplicialComplex K.vertices :=
  PreAbstractSimplicialComplex.toAbstractSimplicialComplex K.vertices
    (K.toPreAbstractSimplicialComplex.restrict K.vertices) fun v => by
      rw [PreAbstractSimplicialComplex.mem_faces,
        PreAbstractSimplicialComplex.mem_restrict_iff_map, Finset.map_singleton]
      exact v.property

variable {K}

/-- A finite set of vertices is a face of the vertex scheme exactly when, as a finite set of
points, it is a face of the geometric complex. -/
@[simp]
theorem mem_vertexScheme_iff {σ : Finset K.vertices} :
    σ ∈ K.vertexScheme ↔ σ.map (Embedding.subtype (· ∈ K.vertices)) ∈ K.faces := by
  rw [← mem_toPreAbstractSimplicialComplex]
  exact PreAbstractSimplicialComplex.mem_restrict_iff_map _ _ σ

/-- The faces of a geometric complex are exactly the faces of its vertex scheme, read as finite
sets of points. -/
theorem mem_faces_iff_exists_mem_vertexScheme {s : Finset E} :
    s ∈ K.faces ↔ ∃ σ ∈ K.vertexScheme, σ.map (Embedding.subtype (· ∈ K.vertices)) = s := by
  classical
  refine ⟨fun hs => ?_, ?_⟩
  · -- Every point of a face is a vertex.
    have hv (x : E) (hx : x ∈ s) : x ∈ K.vertices :=
      K.down_closed hs (Finset.singleton_subset_iff.mpr hx) (Finset.singleton_nonempty x)
    refine ⟨s.subtype (· ∈ K.vertices), ?_, Finset.subtype_map_of_mem hv⟩
    rw [mem_vertexScheme_iff, Finset.subtype_map_of_mem hv]
    exact hs
  · rintro ⟨σ, hσ, rfl⟩
    exact mem_vertexScheme_iff.mp hσ

/-- The vertices of a face of the vertex scheme are affinely independent points of `E`. -/
theorem affineIndependent_vertexScheme (σ : Face K.vertexScheme) :
    AffineIndependent ℝ fun a : σ.val => ((a : K.vertices) : E) :=
  (K.indep (mem_vertexScheme_iff.mp σ.property)).comp_embedding
    ⟨fun a => ⟨a.val.val, Finset.mem_map_of_mem _ a.property⟩, fun a b hab =>
      Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab))⟩

/-! ### The comparison map -/

variable (K) in
/-- The map from the realization of the vertex scheme of `K` to the ambient space, sending a point
with barycentric coordinates `x` to the combination `∑ v, x v • v` of the vertices. Its range is
`K.space` (`Geometry.SimplicialComplex.range_realizationToSpace`). -/
def realizationToSpace (x : Realization K.vertexScheme) : E :=
  Finsupp.linearCombination ℝ (Subtype.val : K.vertices → E) x.val

/-- The comparison map evaluates barycentric coordinates as a combination of the vertices. -/
theorem realizationToSpace_apply (x : Realization K.vertexScheme) :
    K.realizationToSpace x = Finsupp.linearCombination ℝ (Subtype.val : K.vertices → E) x.val :=
  (rfl)

/-- The comparison map sends each vertex of the realization to the corresponding point. -/
@[simp]
theorem realizationToSpace_vertex (v : K.vertices) :
    K.realizationToSpace (vertex K.vertexScheme v) = v := by
  simp [realizationToSpace_apply]

/-- On a closed simplex, the comparison map is the combination of the vertices of that simplex,
weighted by the barycentric coordinates. -/
theorem realizationToSpace_faceInclusion (σ : Face K.vertexScheme) (y : StandardSimplex σ.val) :
    K.realizationToSpace (faceInclusion K.vertexScheme σ y) =
      Fintype.linearCombination ℝ (fun a : σ.val => ((a : K.vertices) : E)) fun a => y.val a := by
  rw [realizationToSpace_apply, faceInclusion_val, Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset y.val (StandardSimplex.support_subset y)
      (fun v t => t • (v : E)) fun _ _ => zero_smul ℝ _,
    Fintype.linearCombination_apply]
  exact (Finset.sum_coe_sort σ.val fun a => y.val a • (a : E)).symm

/-- The comparison map carries the closed simplex of a face of the vertex scheme onto the convex
hull of that face in `E`. -/
theorem range_realizationToSpace_comp_faceInclusion (σ : Face K.vertexScheme) :
    range (K.realizationToSpace ∘ faceInclusion K.vertexScheme σ) =
      convexHull ℝ (σ.val.map (Embedding.subtype (· ∈ K.vertices)) : Set E) := by
  have hp : range (fun a : σ.val => ((a : K.vertices) : E)) =
      (σ.val.map (Embedding.subtype (· ∈ K.vertices)) : Set E) := by
    ext x
    simp
  rw [← hp, ← Finset.range_linearCombination_standardSimplex]
  exact congrArg range (funext (realizationToSpace_faceInclusion σ))

/-- The comparison map sends a point of the realization into the closed simplex of `K` spanned by
the carrier of the point. -/
private theorem realizationToSpace_mem_convexHull_carrier (x : Realization K.vertexScheme) :
    K.realizationToSpace x ∈ convexHull ℝ
      ((carrier K.vertexScheme x).val.map (Embedding.subtype (· ∈ K.vertices)) : Set E) := by
  have hx : faceInclusion K.vertexScheme (carrier K.vertexScheme x)
      ⟨x.val, mem_convexHull_carrier _ x⟩ = x :=
    Subtype.ext (faceInclusion_val _ _ _)
  rw [← range_realizationToSpace_comp_faceInclusion]
  exact ⟨_, by rw [comp_apply, hx]⟩

/-- Two points of the realization whose barycentric supports lie in a common face and which have
the same image under the comparison map are equal. -/
private theorem eq_of_realizationToSpace_eq {σ : Face K.vertexScheme}
    {x y : Realization K.vertexScheme} (hx : x.val.support ⊆ σ.val) (hy : y.val.support ⊆ σ.val)
    (hxy : K.realizationToSpace x = K.realizationToSpace y) : x = y := by
  -- Both are affine combinations of the affinely independent vertices of `σ`.
  have hsum (z : Realization K.vertexScheme) (hz : z.val.support ⊆ σ.val) :
      ∑ a : σ.val, z.val a = 1 := by
    rw [Finset.sum_coe_sort σ.val fun a => z.val a,
      ← Finsupp.sum_of_support_subset z.val hz (fun _ t => t) fun _ _ => rfl]
    exact Realization.sum_eq_one _ z
  have hcomb (z : Realization K.vertexScheme) (hz : z.val.support ⊆ σ.val) :
      ∑ a : σ.val, z.val a • ((a : K.vertices) : E) = K.realizationToSpace z := by
    rw [realizationToSpace_apply, Finsupp.linearCombination_apply,
      Finsupp.sum_of_support_subset z.val hz (fun v t => t • (v : E)) fun _ _ => zero_smul ℝ _]
    exact Finset.sum_coe_sort σ.val fun a => z.val a • (a : E)
  have h := (affineIndependent_vertexScheme σ).eq_of_sum_eq_sum (s := Finset.univ)
    (w₁ := fun a : σ.val => x.val a) (w₂ := fun a : σ.val => y.val a) (by rw [hsum x hx, hsum y hy])
    (by rw [hcomb x hx, hcomb y hy, hxy])
  refine Subtype.ext (Finsupp.ext fun v => ?_)
  by_cases hv : v ∈ σ.val
  · exact h ⟨v, hv⟩ (Finset.mem_univ _)
  · rw [Finsupp.notMem_support_iff.mp fun h => hv (hx h),
      Finsupp.notMem_support_iff.mp fun h => hv (hy h)]

/-- The comparison map is injective: distinct points of the realization of the vertex scheme
have distinct images in `E`. -/
theorem injective_realizationToSpace : Injective K.realizationToSpace := by
  classical
  intro x y hxy
  have hσ := carrier_val K.vertexScheme x
  have hτ := carrier_val K.vertexScheme y
  -- The common image lies in the convex hull of the common face `ρ` of the two carriers.
  have hρ := K.inter_subset_convexHull
    (mem_vertexScheme_iff.mp (carrier K.vertexScheme x).property)
    (mem_vertexScheme_iff.mp (carrier K.vertexScheme y).property)
    ⟨realizationToSpace_mem_convexHull_carrier x,
      hxy ▸ realizationToSpace_mem_convexHull_carrier y⟩
  rw [← Finset.coe_inter, ← Finset.map_inter] at hρ
  have hne : ((carrier K.vertexScheme x).val ∩ (carrier K.vertexScheme y).val).Nonempty :=
    Finset.map_nonempty.mp (Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨_, hρ⟩))
  let ρ : Face K.vertexScheme :=
    ⟨_, K.vertexScheme.isRelLowerSet_faces.mem_of_le (carrier K.vertexScheme x).property
      Finset.inter_subset_left hne⟩
  rw [← range_realizationToSpace_comp_faceInclusion ρ] at hρ
  obtain ⟨z, hz⟩ := hρ
  -- The point of `ρ` with the common image lies in both carriers, so it is `x` and it is `y`.
  have hzρ : (faceInclusion K.vertexScheme ρ z).val.support ⊆ ρ.val := by
    rw [faceInclusion_val]
    exact StandardSimplex.support_subset z
  have hxz := eq_of_realizationToSpace_eq hσ.symm.subset
    (hzρ.trans Finset.inter_subset_left) hz.symm
  have hyz := eq_of_realizationToSpace_eq hτ.symm.subset
    (hzρ.trans Finset.inter_subset_right) (hz.trans hxy).symm
  exact hxz.trans hyz.symm

/-- The range of the comparison map is the underlying space of `K`. -/
@[simp]
theorem range_realizationToSpace : range K.realizationToSpace = K.space := by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact convexHull_subset_space (mem_vertexScheme_iff.mp (carrier K.vertexScheme x).property)
      (realizationToSpace_mem_convexHull_carrier x)
  · intro p hp
    obtain ⟨s, hs, hps⟩ := mem_space_iff.mp hp
    obtain ⟨σ, hσ, rfl⟩ := mem_faces_iff_exists_mem_vertexScheme.mp hs
    rw [← range_realizationToSpace_comp_faceInclusion ⟨σ, hσ⟩] at hps
    exact range_comp_subset_range _ _ hps

/-- The comparison map takes values in the underlying space of `K`. -/
theorem realizationToSpace_mem_space (x : Realization K.vertexScheme) :
    K.realizationToSpace x ∈ K.space :=
  range_realizationToSpace (K := K) ▸ mem_range_self x

/-! ### Topology -/

variable [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- The comparison map is continuous for the weak topology on the realization. -/
theorem continuous_realizationToSpace :
    Continuous K.realizationToSpace := by
  refine continuous_iff_faceInclusion.mpr fun σ => ?_
  have hcoord (a : K.vertices) : Continuous fun y : StandardSimplex σ.val => y.val a :=
    (continuous_apply a).comp continuous_induced_dom
  simp_rw [comp_def, realizationToSpace_faceInclusion, Fintype.linearCombination_apply]
  exact continuous_finsetSum _ fun a _ => (hcoord a).smul continuous_const

/-- If `K.space` is Hausdorff and the closed simplices of `K` form a locally finite family in
`K.space`, the comparison map, read as a map onto `K.space`, is closed. -/
theorem isClosedMap_codRestrict_realizationToSpace [T2Space K.space]
    (hK : LocallyFinite fun s : K.faces => ((↑) : K.space → E) ⁻¹' convexHull ℝ (s : Set E)) :
    IsClosedMap (codRestrict K.realizationToSpace K.space realizationToSpace_mem_space) := by
  intro C hC
  set g := codRestrict K.realizationToSpace K.space realizationToSpace_mem_space
  -- The image of `C` is the union of the images of its traces on the closed simplices.
  have hC' : g '' C = ⋃ σ : Face K.vertexScheme,
      (g ∘ faceInclusion K.vertexScheme σ) '' (faceInclusion K.vertexScheme σ ⁻¹' C) := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      -- Every point of the realization lies in the closed simplex of its carrier.
      have hx' : faceInclusion K.vertexScheme (carrier K.vertexScheme x)
          ⟨x.val, mem_convexHull_carrier _ x⟩ = x :=
        Subtype.ext (faceInclusion_val _ _ _)
      refine mem_iUnion.mpr ⟨carrier K.vertexScheme x, _, ?_, by rw [comp_apply, hx']⟩
      rwa [mem_preimage, hx']
    · exact iUnion_subset fun σ => by
        rw [image_comp]
        exact image_mono (image_preimage_subset _ _)
  rw [hC']
  refine LocallyFinite.isClosed_iUnion ?_ fun σ =>
    (((isClosed_iff_faceInclusion.mp hC σ).isCompact.image
      ((continuous_realizationToSpace.codRestrict _).comp (continuous_faceInclusion _ σ))).isClosed)
  -- Each image lies in a closed simplex of `K`, and distinct faces give distinct simplices.
  refine (hK.comp_injective (g := fun σ : Face K.vertexScheme =>
    (⟨σ.val.map (Embedding.subtype (· ∈ K.vertices)), mem_vertexScheme_iff.mp σ.property⟩ :
      K.faces)) fun σ τ hστ => Subtype.ext (Finset.map_injective _ (congrArg Subtype.val hστ)))
    |>.subset fun σ => ?_
  rintro _ ⟨y, -, rfl⟩
  change K.realizationToSpace (faceInclusion K.vertexScheme σ y) ∈
    convexHull ℝ (σ.val.map (Embedding.subtype (· ∈ K.vertices)) : Set E)
  rw [← range_realizationToSpace_comp_faceInclusion σ]
  exact mem_range_self y

/-- If the closed simplices of `K` form a locally finite family in `E`, the comparison map is
closed. -/
theorem isClosedMap_realizationToSpace [T2Space E]
    (hK : LocallyFinite fun s : K.faces => convexHull ℝ (s : Set E)) :
    IsClosedMap K.realizationToSpace := by
  -- The underlying space is a locally finite union of compact simplices, hence closed.
  have hspace : IsClosed K.space := by
    rw [space, biUnion_eq_iUnion]
    refine hK.isClosed_iUnion fun s => ?_
    obtain ⟨σ, hσ, hs⟩ := mem_faces_iff_exists_mem_vertexScheme.mp s.property
    rw [← hs, ← range_realizationToSpace_comp_faceInclusion ⟨σ, hσ⟩]
    exact (isCompact_range
      (continuous_realizationToSpace.comp (continuous_faceInclusion _ _))).isClosed
  exact hspace.isClosedMap_subtypeVal.comp
    (isClosedMap_codRestrict_realizationToSpace (hK.preimage_continuous continuous_subtypeVal))

/-- If the closed simplices of `K` form a locally finite family in `E`, the comparison map is a
closed embedding of the realization of the vertex scheme into `E`. -/
theorem isClosedEmbedding_realizationToSpace [T2Space E]
    (hK : LocallyFinite fun s : K.faces => convexHull ℝ (s : Set E)) :
    IsClosedEmbedding K.realizationToSpace :=
  .of_continuous_injective_isClosedMap continuous_realizationToSpace injective_realizationToSpace
    (isClosedMap_realizationToSpace hK)

variable (K) in
/-- For a geometric complex with Hausdorff underlying space, whose closed simplices form a locally
finite family in that space, the homeomorphism from the realization of its vertex scheme onto its
underlying space. A family locally finite in `E` is locally finite in `K.space`, by
`LocallyFinite.preimage_continuous` along `continuous_subtypeVal`. -/
def realizationHomeomorph [T2Space K.space]
    (hK : LocallyFinite fun s : K.faces => ((↑) : K.space → E) ⁻¹' convexHull ℝ (s : Set E)) :
    Realization K.vertexScheme ≃ₜ K.space :=
  (Equiv.ofBijective _ ⟨(injective_codRestrict _).mpr injective_realizationToSpace,
    (surjective_codRestrict _).mpr range_realizationToSpace⟩).toHomeomorphOfContinuousClosed
    (continuous_realizationToSpace.codRestrict _) (isClosedMap_codRestrict_realizationToSpace hK)

/-- The homeomorphism onto the underlying space is the comparison map. -/
@[simp]
theorem coe_realizationHomeomorph_apply [T2Space K.space]
    (hK : LocallyFinite fun s : K.faces => ((↑) : K.space → E) ⁻¹' convexHull ℝ (s : Set E))
    (x : Realization K.vertexScheme) :
    (K.realizationHomeomorph hK x : E) = K.realizationToSpace x :=
  (rfl)

end Geometry.SimplicialComplex
