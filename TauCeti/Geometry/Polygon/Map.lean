/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Polygon.DoublePoint

/-!
# Images of polygons under affine maps

The image `poly.map f` of a polygon `poly : Polygon P n` under a map `f : P → P'` is the polygon
whose vertices are the images of those of `poly`. For an affine map `f`, its edges are the images
of the edges of `poly` (`Polygon.edgeSet_map`), and its boundary parametrization is that of `poly`
followed by `f` (`Polygon.boundaryParam_map`). An injective affine map keeps a polygon simple
(`Polygon.isSimple_map_iff`), carries its double points under `π ∘ f` onto the double points of the
image under `π` (`Polygon.doublePoints_map`), and preserves regularity of projections
(`Polygon.isRegularProjection_map_iff`).

For the projection along a direction (`Polygon.projAlong`), an affine map `f` whose linear part is
injective carries the lines parallel to `d` onto lines parallel to `f.linear d` without identifying
two of them (`Polygon.projAlong_map_eq_projAlong_map_iff`). So the projection of `poly.map f`
along `f.linear d` is regular exactly when the projection of `poly` along `d` is
(`Polygon.isRegularProjection_map_projAlong_iff`), and its double points are the images of those
of `poly` (`Polygon.doublePoints_map_projAlong`). This is the input for comparing the knot
diagrams of a polygonal knot and of its image under an affine equivalence, such as a rotation of
`ℝ³`.

## Main definitions

* `Polygon.map f poly`: the polygon with vertices `f (poly i)`.

## Main results

* `Polygon.boundary_map`: the boundary of the image is the image of the boundary.
* `Polygon.boundaryParam_map`: the boundary parametrization of the image.
* `Polygon.isSimple_map_iff`: an injective affine map preserves and reflects simplicity.
* `Polygon.doublePoints_map`, `Polygon.isRegularProjection_map_iff`: double points and regular
  projections of the image.
* `Polygon.isRegularProjection_map_projAlong_iff`, `Polygon.doublePoints_map_projAlong`: the same
  for the projection along the image of a direction.
-/

public section

open Set Function AffineMap

namespace Polygon

variable {R V V' P P' Q : Type*} {n : ℕ}

/-- The **image of a polygon** under a map `f`: the polygon with vertices `f (poly i)`. -/
def map (f : P → P') (poly : Polygon P n) : Polygon P' n :=
  ⟨fun i ↦ f (poly i)⟩

/-- The vertices of the image of a polygon are the images of its vertices. -/
@[simp]
theorem map_apply (f : P → P') (poly : Polygon P n) (i : Fin n) : poly.map f i = f (poly i) :=
  (rfl)

/-- The image of a polygon under the identity is the polygon itself. -/
@[simp]
theorem map_id (poly : Polygon P n) : poly.map id = poly :=
  (rfl)

/-- Taking images of polygons is compatible with composition of maps. -/
theorem map_map {P'' : Type*} (f : P → P') (g : P' → P'') (poly : Polygon P n) :
    (poly.map f).map g = poly.map (g ∘ f) :=
  (rfl)

section Affine

variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V']
  [AddTorsor V' P'] (f : P →ᵃ[R] P') (poly : Polygon P n)

/-- The edges of the image of a polygon under an affine map are the images of its edges. -/
theorem edgePath_map (i : Fin n) : (poly.map f).edgePath R i = f.comp (poly.edgePath R i) :=
  (f.comp_lineMap _ _).symm

variable [PartialOrder R]

/-- The edge sets of the image of a polygon under an affine map are the images of its edge
sets. -/
@[simp]
theorem edgeSet_map (i : Fin n) : (poly.map f).edgeSet R i = f '' poly.edgeSet R i := by
  rw [edgeSet_eq_image_edgePath, edgeSet_eq_image_edgePath, edgePath_map, coe_comp, image_comp]

/-- The boundary of the image of a polygon under an affine map is the image of its boundary. -/
@[simp]
theorem boundary_map : (poly.map f).boundary R = f '' poly.boundary R := by
  simp only [boundary, edgeSet_map, image_iUnion]

variable {f} {poly}

/-- An injective affine map preserves and reflects simplicity of polygons. -/
@[simp]
theorem isSimple_map_iff (hf : Injective f) :
    (poly.map f).IsSimple R ↔ poly.IsSimple R := by
  refine ⟨fun h ↦ ⟨fun i hi ↦ h.hasNondegenerateEdges i (by simp [hi]), fun i j x hij hi hj ↦ ?_⟩,
    fun h ↦ ⟨fun i hi ↦ h.hasNondegenerateEdges i (hf hi), fun i j x hij hi hj ↦ ?_⟩⟩
  · have := h.eq_vertex_of_mem_edgeSet hij (x := f x)
      (by rw [edgeSet_map]; exact mem_image_of_mem f hi)
      (by rw [edgeSet_map]; exact mem_image_of_mem f hj)
    simpa only [map_apply, hf.eq_iff] using this
  · rw [edgeSet_map] at hi hj
    obtain ⟨y, hy, rfl⟩ := hi
    obtain ⟨y', hy', hyy'⟩ := hj
    obtain rfl := hf hyy'
    simpa only [map_apply, hf.eq_iff] using h.eq_vertex_of_mem_edgeSet hij hy hy'

/-- An injective affine map keeps a polygon simple. -/
theorem IsSimple.map (h : poly.IsSimple R) (hf : Injective f) :
    (poly.map f).IsSimple R :=
  (isSimple_map_iff hf).2 h

/-- The double points of the image of a polygon under an injective affine map `f`, for a map `π`,
are the images of the double points of the polygon for `π ∘ f`. -/
theorem doublePoints_map (hf : Injective f) (π : P' → Q) :
    (poly.map f).doublePoints R π = f '' poly.doublePoints R (π ∘ f) :=
  doublePoints_eq_image_of_boundary_eq_image hf (boundary_map f poly) π

/-- A map `π` is a regular projection of the image of a polygon under an injective affine map `f`
exactly when `π ∘ f` is a regular projection of the polygon. -/
theorem isRegularProjection_map_iff (hf : Injective f) {π : P' → Q} :
    (poly.map f).IsRegularProjection R π ↔ poly.IsRegularProjection R (π ∘ f) := by
  refine ⟨fun h ↦ ⟨fun x y z hx hy hz hxy hxz ↦ ?_, fun i x hx hxi ↦ ?_⟩,
    fun h ↦ ⟨fun x y z hx hy hz hxy hxz ↦ ?_, fun i x hx hxi ↦ ?_⟩⟩
  · simpa only [hf.eq_iff] using h.eq_or_eq_or_eq_of_apply_eq (x := f x) (y := f y) (z := f z)
      (boundary_map f poly ▸ mem_image_of_mem f hx) (boundary_map f poly ▸ mem_image_of_mem f hy)
      (boundary_map f poly ▸ mem_image_of_mem f hz) hxy hxz
  · exact hf (h.eq_vertex_of_apply_eq i (boundary_map f poly ▸ mem_image_of_mem f hx) hxi)
  · rw [boundary_map] at hx hy hz
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    obtain ⟨z, hz, rfl⟩ := hz
    simpa only [hf.eq_iff] using h.eq_or_eq_or_eq_of_apply_eq hx hy hz hxy hxz
  · rw [boundary_map] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    exact congrArg f (h.eq_vertex_of_apply_eq i hx hxi)

end Affine

section ProjAlong

variable [Ring R] [AddCommGroup V] [Module R V] [AddTorsor V P] [AddCommGroup V'] [Module R V']
  [AddTorsor V' P'] {f : P →ᵃ[R] P'}

/-- An affine map `f` with injective linear part carries the lines parallel to `d` onto lines
parallel to `f.linear d`, and does not identify two such lines. -/
theorem projAlong_map_eq_projAlong_map_iff (hf : Injective f.linear) (q₀ : P') (p₀ : P) (d : V)
    {x y : P} : projAlong R q₀ (f.linear d) (f x) = projAlong R q₀ (f.linear d) (f y) ↔
      projAlong R p₀ d x = projAlong R p₀ d y := by
  simp only [projAlong_eq_projAlong_iff, ← f.linear_apply_vsub, ← LinearMap.map_smul, hf.eq_iff]

variable [PartialOrder R] {poly : Polygon P n}

/-- The double points of the projection of the image of a polygon along the image of a direction
`d` are the images of the double points of its projection along `d`. -/
theorem doublePoints_map_projAlong (hf : Injective f.linear) (q₀ : P') (p₀ : P) (d : V) :
    (poly.map f).doublePoints R (projAlong R q₀ (f.linear d)) =
      f '' poly.doublePoints R (projAlong R p₀ d) := by
  rw [doublePoints_map ((linear_injective_iff f).1 hf)]
  exact congrArg _ (doublePoints_congr fun x _ y _ ↦
    projAlong_map_eq_projAlong_map_iff hf q₀ p₀ d)

/-- The projection of the image of a polygon along the image of a direction `d` is regular exactly
when the projection of the polygon along `d` is. -/
theorem isRegularProjection_map_projAlong_iff (hf : Injective f.linear)
    (q₀ : P') (p₀ : P) (d : V) :
    (poly.map f).IsRegularProjection R (projAlong R q₀ (f.linear d)) ↔
      poly.IsRegularProjection R (projAlong R p₀ d) := by
  rw [isRegularProjection_map_iff ((linear_injective_iff f).1 hf)]
  exact isRegularProjection_congr fun x _ y _ ↦ projAlong_map_eq_projAlong_map_iff hf q₀ p₀ d

end ProjAlong

section Param

variable [AddCommGroup V] [Module ℝ V] [AddTorsor V P] [AddCommGroup V'] [Module ℝ V']
  [AddTorsor V' P'] [NeZero n]

/-- The boundary parametrization of the image of a polygon under an affine map `f` is that of the
polygon followed by `f`. -/
@[simp]
theorem boundaryParam_map (f : P →ᵃ[ℝ] P') (poly : Polygon P n) (t : ℝ) :
    (poly.map f).boundaryParam t = f (poly.boundaryParam t) := by
  rw [boundaryParam_eq_edgePath_edgeIndexAt, boundaryParam_eq_edgePath_edgeIndexAt, edgePath_map,
    coe_comp, comp_apply]

end Param

end Polygon
