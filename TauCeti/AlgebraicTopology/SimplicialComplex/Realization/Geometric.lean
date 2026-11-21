/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.Map
public import TauCeti.AlgebraicTopology.SimplicialComplex.VertexScheme

/-!
# Realizations of geometric simplicial complexes

A geometric simplicial complex `K` in a real vector space `E` (Mathlib's
`Geometry.SimplicialComplex`) determines an abstract simplicial complex, its vertex scheme
`K.vertexScheme` (`TauCeti.AlgebraicTopology.SimplicialComplex.VertexScheme`). This file compares
the weak realization of the vertex scheme with the underlying space `K.space ⊆ E`.

The comparison map `K.realizationToAmbient : |K.vertexScheme| → E` sends a point with barycentric
coordinates `x` to the combination `∑ v, x v • v` of the vertices: it is the linear extension of
the inclusion of the vertices. It is linear in barycentric coordinates on every closed simplex,
injective, and has range `K.space`; it is continuous when addition and real scalar multiplication
on `E` are continuous. Injectivity combines the affine independence of the vertices of each face
with the fact that the closed simplices of `K` meet in common faces. Assuming these continuity
hypotheses, when `K.space` is Hausdorff
and the closed simplices of `K` form a locally finite family in `K.space`, the map is a closed map
onto `K.space` and gives a homeomorphism `K.realizationHomeomorph hK : |K.vertexScheme| ≃ₜ K.space`;
this covers complexes such as the dyadic subdivision of an open ray, which accumulate only outside
their underlying space. When `E` is Hausdorff and the family is locally finite in `E` itself, the
map is moreover a closed embedding into `E`. Without local finiteness the weak topology is in
general strictly finer than the subspace topology of `K.space`: for the infinitely many edges
`[0, eᵢ]` of a fan in `ℓ²`, the points at parameter `1 / i` on the `i`-th edge converge to `0` in
`E`, but form a closed set in the weak topology. For a subcomplex `K ≤ L`, the comparison map of
`K` factors through the realization of the inclusion of vertex schemes and the comparison map of
`L`.

This is how polyhedra built inside a vector space, by subdividing, intersecting or gluing geometric
complexes, become triangulations in the sense of `TauCeti.IsTriangulable`, whose domain is the
realization of an abstract complex. In particular the rectilinear complexes in coordinate charts
from which a smooth triangulation of a manifold is assembled are read as abstract complexes this
way.

## Main definitions

* `Geometry.SimplicialComplex.realizationToAmbient`: the map from the realization of the vertex
  scheme into the ambient space.
* `Geometry.SimplicialComplex.realizationHomeomorph`: for a complex with Hausdorff underlying
  space, locally finite in that space, and continuous ambient addition and real scalar
  multiplication, the homeomorphism from the realization of its vertex scheme
  onto that space.

## Main results

* `Geometry.SimplicialComplex.realizationToAmbient_injective`,
  `Geometry.SimplicialComplex.range_realizationToAmbient`: the comparison map is a bijection onto
  `K.space`.
* `Geometry.SimplicialComplex.secantMap_realizationToAmbient`: the comparison map is its own secant
  map.
* `Geometry.SimplicialComplex.realizationToAmbient_comp_realizationMap_vertexSchemeInclusion`:
  the comparison maps are compatible with the inclusion of a subcomplex.
* `Geometry.SimplicialComplex.isClosedMap_codRestrict_realizationToAmbient`: for a complex with
  Hausdorff underlying space, locally finite in that space, and continuous ambient addition and
  real scalar multiplication, the comparison map onto `K.space` is
  closed.
* `Geometry.SimplicialComplex.isClosedEmbedding_realizationToAmbient`: for a complex locally
  finite in a Hausdorff space `E` with continuous addition and real scalar multiplication, the
  comparison map is a closed embedding.

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

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {K : SimplicialComplex ℝ E}

/-! ### The comparison map -/

variable (K) in
/-- The map from the realization of the vertex scheme of `K` to the ambient space, sending a point
with barycentric coordinates `x` to the combination `∑ v, x v • v` of the vertices: the linear
extension of the inclusion of the vertices. Its values lie in `K.space`
(`Geometry.SimplicialComplex.range_realizationToAmbient`); `K.realizationHomeomorph` is its
corestriction to `K.space` when that space is Hausdorff, `K` is locally finite in it, and ambient
addition and real scalar multiplication are continuous. -/
def realizationToAmbient : Realization K.vertexScheme → E :=
  K.vertexScheme.linearExtension Subtype.val

/-- The comparison map evaluates barycentric coordinates as a combination of the vertices. -/
theorem realizationToAmbient_apply (x : Realization K.vertexScheme) :
    K.realizationToAmbient x = Finsupp.linearCombination ℝ (Subtype.val : K.vertices → E) x.val :=
  linearExtension_apply _ x

/-- The comparison map sends each vertex of the realization to the corresponding point. -/
@[simp]
theorem realizationToAmbient_vertex (v : K.vertices) :
    K.realizationToAmbient (vertex K.vertexScheme v) = v :=
  linearExtension_vertex _ v

/-- On a closed simplex, the comparison map is the combination of the vertices of that simplex,
weighted by the barycentric coordinates. -/
theorem realizationToAmbient_faceInclusion (σ : Face K.vertexScheme) (y : StandardSimplex σ.val) :
    K.realizationToAmbient (faceInclusion K.vertexScheme σ y) =
      Fintype.linearCombination ℝ (fun a : σ.val => ((a : K.vertices) : E)) fun a => y.val a := by
  rw [Fintype.linearCombination_apply]
  exact linearExtension_faceInclusion _ σ y

/-- The comparison map carries the closed simplex of a face of the vertex scheme onto the convex
hull of that face in `E`. -/
@[simp]
theorem range_realizationToAmbient_comp_faceInclusion (σ : Face K.vertexScheme) :
    range (K.realizationToAmbient ∘ faceInclusion K.vertexScheme σ) =
      convexHull ℝ (σ.val.map (Embedding.subtype (· ∈ K.vertices)) : Set E) := by
  rw [← range_vertexScheme_face_coe]
  exact range_linearExtension_comp_faceInclusion _ σ

/-- The comparison map sends a point of the realization into the closed simplex of `K` spanned by
the carrier of the point. -/
private theorem realizationToAmbient_mem_convexHull_carrier (x : Realization K.vertexScheme) :
    K.realizationToAmbient x ∈ convexHull ℝ
      ((carrier K.vertexScheme x).val.map (Embedding.subtype (· ∈ K.vertices)) : Set E) := by
  rw [← range_realizationToAmbient_comp_faceInclusion]
  obtain ⟨y, hy⟩ := mem_range_faceInclusion_carrier K.vertexScheme x
  exact ⟨y, congrArg K.realizationToAmbient hy⟩

/-- Two points of the realization whose barycentric supports lie in a common face and which have
the same image under the comparison map are equal. -/
private theorem eq_of_realizationToAmbient_eq {σ : Face K.vertexScheme}
    {x y : Realization K.vertexScheme} (hx : x.val.support ⊆ σ.val) (hy : y.val.support ⊆ σ.val)
    (hxy : K.realizationToAmbient x = K.realizationToAmbient y) : x = y := by
  -- Both points lie in the closed simplex of `σ`, on which the comparison map is injective.
  obtain ⟨x', rfl⟩ := (mem_range_faceInclusion_iff _ σ x).mpr hx
  obtain ⟨y', rfl⟩ := (mem_range_faceInclusion_iff _ σ y).mpr hy
  rw [realizationToAmbient_faceInclusion, realizationToAmbient_faceInclusion] at hxy
  exact congrArg (faceInclusion K.vertexScheme σ)
    (Finset.injective_linearCombination_standardSimplex (affineIndependent_vertexScheme_face σ) hxy)

/-- The comparison map is injective: distinct points of the realization of the vertex scheme
have distinct images in `E`. -/
theorem realizationToAmbient_injective : Injective K.realizationToAmbient := by
  classical
  intro x y hxy
  have hσ := carrier_val K.vertexScheme x
  have hτ := carrier_val K.vertexScheme y
  -- The common image lies in the convex hull of the common face `ρ` of the two carriers.
  have hρ := K.inter_subset_convexHull
    (mem_vertexScheme_iff.mp (carrier K.vertexScheme x).property)
    (mem_vertexScheme_iff.mp (carrier K.vertexScheme y).property)
    ⟨realizationToAmbient_mem_convexHull_carrier x,
      hxy ▸ realizationToAmbient_mem_convexHull_carrier y⟩
  rw [← Finset.coe_inter, ← Finset.map_inter] at hρ
  have hne : ((carrier K.vertexScheme x).val ∩ (carrier K.vertexScheme y).val).Nonempty :=
    Finset.map_nonempty.mp (Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨_, hρ⟩))
  let ρ : Face K.vertexScheme :=
    ⟨_, K.vertexScheme.isRelLowerSet_faces.mem_of_le (carrier K.vertexScheme x).property
      Finset.inter_subset_left hne⟩
  rw [← range_realizationToAmbient_comp_faceInclusion ρ] at hρ
  obtain ⟨z, hz⟩ := hρ
  -- The point of `ρ` with the common image lies in both carriers, so it is `x` and it is `y`.
  have hzρ := (mem_range_faceInclusion_iff _ ρ _).mp (mem_range_self z)
  have hxz := eq_of_realizationToAmbient_eq hσ.symm.subset
    (hzρ.trans Finset.inter_subset_left) hz.symm
  have hyz := eq_of_realizationToAmbient_eq hτ.symm.subset
    (hzρ.trans Finset.inter_subset_right) (hz.trans hxy).symm
  exact hxz.trans hyz.symm

/-- The range of the comparison map is the underlying space of `K`. -/
@[simp]
theorem range_realizationToAmbient : range K.realizationToAmbient = K.space := by
  apply Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    exact convexHull_subset_space (mem_vertexScheme_iff.mp (carrier K.vertexScheme x).property)
      (realizationToAmbient_mem_convexHull_carrier x)
  · intro p hp
    obtain ⟨s, hs, hps⟩ := mem_space_iff.mp hp
    obtain ⟨σ, hσ, rfl⟩ := mem_faces_iff_exists_mem_vertexScheme.mp hs
    rw [← range_realizationToAmbient_comp_faceInclusion ⟨σ, hσ⟩] at hps
    exact range_comp_subset_range _ _ hps

/-- The comparison map takes values in the underlying space of `K`. -/
@[simp]
theorem realizationToAmbient_mem_space (x : Realization K.vertexScheme) :
    K.realizationToAmbient x ∈ K.space :=
  range_realizationToAmbient (K := K) ▸ mem_range_self x

/-- The comparison point belongs to the convex hull of a face exactly when its barycentric
support is contained in that face. -/
@[simp]
theorem realizationToAmbient_mem_convexHull_iff (σ : Face K.vertexScheme)
    (x : Realization K.vertexScheme) :
    K.realizationToAmbient x ∈
      convexHull ℝ (Subtype.val '' (σ.val : Set K.vertices)) ↔
        x.val.support ⊆ σ.val := by
  have h : K.realizationToAmbient x ∈
      convexHull ℝ (σ.val.map (Embedding.subtype (· ∈ K.vertices)) : Set E) ↔
        x.val.support ⊆ σ.val := by
    rw [← range_realizationToAmbient_comp_faceInclusion, range_comp,
      (realizationToAmbient_injective).mem_set_image, mem_range_faceInclusion_iff]
  simpa only [Finset.coe_map, Embedding.coe_subtype] using h

/-- The comparison point belongs to the convex hull of a face of `K` exactly when its barycentric
support is contained in the corresponding face of the vertex scheme. -/
@[simp]
theorem realizationToAmbient_mem_convexHull_face_iff (s : K.faces)
    (x : Realization K.vertexScheme) :
    K.realizationToAmbient x ∈ convexHull ℝ (s : Set E) ↔
      x.val.support ⊆ (K.vertexSchemeFaceEquiv.symm s).val := by
  conv_lhs => rw [← map_vertexSchemeFaceEquiv_symm_apply_coe s]
  rw [← range_realizationToAmbient_comp_faceInclusion, range_comp,
    realizationToAmbient_injective.mem_set_image, mem_range_faceInclusion_iff]

/-- The comparison map is its own secant map, since it linearly extends the vertex inclusion. -/
@[simp]
theorem secantMap_realizationToAmbient :
    K.vertexScheme.secantMap K.realizationToAmbient = K.realizationToAmbient :=
  secantMap_linearExtension _

/-! ### Subcomplexes -/

attribute [local instance] Classical.decEq

/-- For a subcomplex `K ≤ L`, the realization of the inclusion of vertex schemes followed by the
comparison map of `L` is the comparison map of `K`. -/
@[simp]
theorem realizationToAmbient_realizationMap_vertexSchemeInclusion
    {L : SimplicialComplex ℝ E} (h : K ≤ L) (x : Realization K.vertexScheme) :
    L.realizationToAmbient ((vertexSchemeInclusion h).realizationMap x) =
      K.realizationToAmbient x := by
  simp only [realizationToAmbient, linearExtension_realizationMap, coe_vertexSchemeInclusion,
    val_comp_inclusion]

/-- For a subcomplex `K ≤ L`, the comparison map of `K` factors through the realization of the
inclusion of vertex schemes and the comparison map of `L`. -/
theorem realizationToAmbient_comp_realizationMap_vertexSchemeInclusion
    {L : SimplicialComplex ℝ E} (h : K ≤ L) :
    L.realizationToAmbient ∘ (vertexSchemeInclusion h).realizationMap = K.realizationToAmbient :=
  funext (realizationToAmbient_realizationMap_vertexSchemeInclusion h)

/-! ### Topology -/

variable [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- If addition and real scalar multiplication on `E` are continuous, the comparison map is
continuous for the weak topology on the realization. -/
theorem continuous_realizationToAmbient : Continuous K.realizationToAmbient :=
  continuous_linearExtension _

/-- If ambient addition and real scalar multiplication are continuous, `K.space` is Hausdorff,
and the closed simplices of `K` form a locally finite family in
`K.space`, the comparison map, read as a map onto `K.space`, is closed. -/
theorem isClosedMap_codRestrict_realizationToAmbient [T2Space K.space]
    (hK : LocallyFinite fun s : K.faces => ((↑) : K.space → E) ⁻¹' convexHull ℝ (s : Set E)) :
    IsClosedMap (codRestrict K.realizationToAmbient K.space realizationToAmbient_mem_space) := by
  refine isClosedMap_of_locallyFinite_faceInclusion (continuous_realizationToAmbient.codRestrict _)
    ((hK.comp_injective K.vertexSchemeFaceEquiv.injective).subset fun σ => ?_)
  -- Each closed simplex is carried into the closed simplex of the corresponding face of `K`.
  rintro _ ⟨y, rfl⟩
  simp only [comp_apply, mem_preimage, val_codRestrict_apply, vertexSchemeFaceEquiv_apply_coe]
  rw [← range_realizationToAmbient_comp_faceInclusion σ]
  exact mem_range_self y

/-- If addition and real scalar multiplication on `E` are continuous, `E` is Hausdorff, and the
closed simplices of `K` form a locally finite family in `E`, the
comparison map is closed. -/
theorem isClosedMap_realizationToAmbient [T2Space E]
    (hK : LocallyFinite fun s : K.faces => convexHull ℝ (s : Set E)) :
    IsClosedMap K.realizationToAmbient := by
  refine isClosedMap_of_locallyFinite_faceInclusion continuous_realizationToAmbient
    ((hK.comp_injective K.vertexSchemeFaceEquiv.injective).subset fun σ => ?_)
  -- Each closed simplex is carried onto the closed simplex of the corresponding face of `K`.
  rw [range_realizationToAmbient_comp_faceInclusion, comp_apply, vertexSchemeFaceEquiv_apply_coe]

/-- If addition and real scalar multiplication on `E` are continuous, `E` is Hausdorff, and the
closed simplices of `K` form a locally finite family in `E`, the
comparison map is a closed embedding of the realization of the vertex scheme into `E`. -/
theorem isClosedEmbedding_realizationToAmbient [T2Space E]
    (hK : LocallyFinite fun s : K.faces => convexHull ℝ (s : Set E)) :
    IsClosedEmbedding K.realizationToAmbient :=
  .of_continuous_injective_isClosedMap continuous_realizationToAmbient
    realizationToAmbient_injective (isClosedMap_realizationToAmbient hK)

variable (K) in
/-- For a geometric complex in a space with continuous addition and real scalar multiplication,
with Hausdorff underlying space, whose closed simplices form a locally
finite family in that space, the homeomorphism from the realization of its vertex scheme onto its
underlying space. A family locally finite in `E` is locally finite in `K.space`, by
`LocallyFinite.preimage_continuous` along `continuous_subtypeVal`. -/
def realizationHomeomorph [T2Space K.space]
    (hK : LocallyFinite fun s : K.faces => ((↑) : K.space → E) ⁻¹' convexHull ℝ (s : Set E)) :
    Realization K.vertexScheme ≃ₜ K.space :=
  (Equiv.ofBijective _ ⟨(injective_codRestrict _).mpr realizationToAmbient_injective,
    (surjective_codRestrict _).mpr range_realizationToAmbient⟩).toHomeomorphOfContinuousClosed
    (continuous_realizationToAmbient.codRestrict _)
    (isClosedMap_codRestrict_realizationToAmbient hK)

/-- The homeomorphism onto the underlying space is the comparison map. -/
@[simp]
theorem coe_realizationHomeomorph_apply [T2Space K.space]
    (hK : LocallyFinite fun s : K.faces => ((↑) : K.space → E) ⁻¹' convexHull ℝ (s : Set E))
    (x : Realization K.vertexScheme) :
    (K.realizationHomeomorph hK x : E) = K.realizationToAmbient x := by
  unfold realizationHomeomorph
  rw [Equiv.toHomeomorphOfContinuousClosed_apply]
  exact (congrArg Subtype.val (congrFun (Equiv.coe_ofBijective _ _) x)).trans
    (val_codRestrict_apply _ _ _ _)

/-- Transporting a point of the underlying space back to the realization preserves its ambient
coordinates. -/
@[simp]
theorem realizationToAmbient_realizationHomeomorph_symm_apply [T2Space K.space]
    (hK : LocallyFinite fun s : K.faces => ((↑) : K.space → E) ⁻¹' convexHull ℝ (s : Set E))
    (p : K.space) :
    K.realizationToAmbient ((K.realizationHomeomorph hK).symm p) = (p : E) := by
  rw [← coe_realizationHomeomorph_apply hK, Homeomorph.apply_symm_apply]

end Geometry.SimplicialComplex
