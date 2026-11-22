/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.KreinMilman
public import TauCeti.Geometry.Convex.Cone.Face.Exposed
public import TauCeti.Geometry.Toric.Algebraic.Ray.Face
public import TauCeti.Geometry.Toric.Algebraic.Regular
public import TauCeti.Geometry.Toric.Delzant.Face

/-!
# The normal fan of a Delzant polytope

Let `Δ = {x ∈ V* | c j ≤ ⟨x, u j⟩ for every j}` be the polyhedron of a facet presentation `(u, c)`
in a lattice map `i : N →+ V`. The *normal cone* of the presentation at a point `x` of `V*`
(`TauCeti.Toric.normalCone i u c x`) is the cone in `V` spanned by the inward normals `i (u j)`
of the facets through `x`. The normal cones at the vertices of a Delzant polytope are the maximal
cones of a complete regular fan, the *normal fan* of the polytope
(`TauCeti.Toric.IsDelzant.normalFan`). In toric geometry this is the fan of the smooth projective
toric variety of the polytope, the complex counterpart of the symplectic toric manifold that
Delzant's construction attaches to it; the normal fan is the combinatorial side of that
comparison.

* **Normal cones are minimizing directions.** If `w` lies in the normal cone at `x`, the pairing
  `z ↦ ⟨z, w⟩` attains its minimum over `Δ` at `x`
  (`TauCeti.Toric.apply_le_apply_of_mem_normalCone`). At a smooth vertex the converse holds
  (`TauCeti.Toric.IsSmoothVertex.mem_normalCone_iff`): if some coefficient of `w` in the basis of
  active normals were negative, moving from the vertex along the corresponding edge would lower
  the pairing.
* **Intersections.** For two points `x` and `y` of `Δ`, the pairing with `y - x` is nonnegative
  on the normal cone at `x` and nonpositive on the one at `y`. So the two normal cones meet in the
  face of the first one cut out by `y - x`, which is spanned by the normals of the facets through
  both points (`TauCeti.Toric.normalCone_inf_normalCone`,
  `TauCeti.Toric.normalCone_inf_isFaceOf_left`). No Delzant hypothesis is needed here.
* **Regularity.** At a smooth vertex the active normals form an integral basis, so the normal cone
  is a regular cone (`TauCeti.Toric.IsSmoothVertex.isRegularCone_normalCone`).
* **Completeness.** A linear functional on the compact polytope attains its minimum at a vertex
  (`IsCompact.exists_mem_extremePoints_isMinOn`), so every direction lies in the normal cone at
  some vertex (`TauCeti.Toric.IsDelzant.isComplete_normalFan`).
* **The face dictionary.** The cones of the normal fan are exactly the normal cones at the points
  of `Δ` (`TauCeti.Toric.IsDelzant.mem_normalFan_cones_iff`), and for points of a Delzant polytope
  the normal cone at `x` lies in the one at `y` exactly when every facet through `x` passes
  through `y` (`TauCeti.Toric.IsDelzant.normalCone_le_normalCone_iff`). The face dictionary of
  `TauCeti.Geometry.Toric.Delzant.Face` indexes the nonempty faces of `Δ` by the sets of facets
  through their relative interior points, reversing inclusion; read through it, these two
  statements match the faces of `Δ` with the cones of the normal fan. In particular distinct
  vertices have distinct normal cones (`TauCeti.Toric.IsDelzant.injOn_normalCone`).
* **Translations.** Translating the polytope, which shifts the moment map by a constant, does not
  change its normal fan (`TauCeti.Toric.IsDelzant.normalFan_add`).

## Main definitions

* `TauCeti.Toric.normalCone i u c x`: the cone spanned by the normals of the facets through `x`.
* `TauCeti.Toric.IsDelzant.normalFan`: the normal fan of a Delzant polytope.

## Main results

* `TauCeti.Toric.IsSmoothVertex.mem_normalCone_iff`: at a smooth vertex, the normal cone is the
  set of directions minimized there.
* `TauCeti.Toric.normalCone_inf_normalCone`: intersections of normal cones.
* `TauCeti.Toric.IsDelzant.mem_normalFan_cones_iff`: the cones of the normal fan are the normal
  cones at the points of the polytope.
* `TauCeti.Toric.IsDelzant.isRegular_normalFan`, `TauCeti.Toric.IsDelzant.isComplete_normalFan`:
  the normal fan of a Delzant polytope is regular and complete.

## References

* W. Fulton, *Introduction to Toric Varieties*, Annals of Mathematics Studies 131, Princeton
  University Press, 1993, Section 1.5.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, Graduate Studies in Mathematics 124,
  American Mathematical Society, 2011, Section 2.3 (normal fans of polytopes).
-/

public section

noncomputable section

open Set

namespace TauCeti.Toric

variable {ι N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {u : ι → N} {c : ι → ℝ} {x y z : StrongDual ℝ V} {w : V}

/-! ### Normal cones -/

variable (i u c) in
/-- The *normal cone* of the facet presentation `(u, c)` at a point `x` of `V*`: the cone in `V`
spanned by the inward normals `i (u j)` of the facets through `x`. At a smooth vertex of the
polyhedron it is the set of directions whose pairing attains its minimum over the polyhedron at
`x` (`TauCeti.Toric.IsSmoothVertex.mem_normalCone_iff`). -/
def normalCone (x : StrongDual ℝ V) : PointedCone ℝ V :=
  PointedCone.hull ℝ ((fun j ↦ i (u j)) '' activeSet (facetPairing i u) c x)

theorem normalCone_def :
    normalCone i u c x =
      PointedCone.hull ℝ ((fun j ↦ i (u j)) '' activeSet (facetPairing i u) c x) :=
  (rfl)

/-- The normal of a facet through `x` lies in the normal cone at `x`. -/
theorem apply_mem_normalCone {j : ι} (hj : j ∈ activeSet (facetPairing i u) c x) :
    i (u j) ∈ normalCone i u c x :=
  PointedCone.subset_hull ⟨j, hj, rfl⟩

/-- A point on more facets has a larger normal cone. -/
theorem normalCone_mono
    (h : activeSet (facetPairing i u) c x ⊆ activeSet (facetPairing i u) c y) :
    normalCone i u c x ≤ normalCone i u c y :=
  Submodule.span_mono (image_mono h)

/-- **Directions of a normal cone are minimized at its point.** If `w` lies in the normal cone at
`x`, then `⟨x, w⟩ ≤ ⟨z, w⟩` for every point `z` of the polyhedron. -/
theorem apply_le_apply_of_mem_normalCone (hz : z ∈ facetPolyhedron i u c)
    (hw : w ∈ normalCone i u c x) : x w ≤ z w := by
  have h : ((z - x : StrongDual ℝ V) : V →ₗ[ℝ] ℝ) ∈
      PointedCone.dual (Module.Dual.eval ℝ V) (normalCone i u c x) := by
    rw [normalCone_def, PointedCone.dual_hull]
    rintro _ ⟨j, hj, rfl⟩
    rw [mem_activeSet, facetPairing_apply] at hj
    simpa [hj] using mem_facetPolyhedron.1 hz j
  simpa using h hw

/-- For `y` in the polyhedron, the pairing with `y - x` is nonnegative on the normal cone at `x`,
and the face of that cone on which it vanishes is spanned by the normals of the facets through
both `x` and `y`. -/
private theorem normalCone_inf_ker (hy : y ∈ facetPolyhedron i u c) :
    normalCone i u c x ⊓
        PointedCone.ofSubmodule (LinearMap.ker ((y - x : StrongDual ℝ V) : V →ₗ[ℝ] ℝ)) =
      PointedCone.hull ℝ ((fun j ↦ i (u j)) ''
        (activeSet (facetPairing i u) c x ∩ activeSet (facetPairing i u) c y)) := by
  have hφ : ∀ w ∈ normalCone i u c x, 0 ≤ ((y - x : StrongDual ℝ V) : V →ₗ[ℝ] ℝ) w :=
    fun w hw ↦ sub_nonneg.2 (apply_le_apply_of_mem_normalCone hy hw)
  rw [(PointedCone.isFaceOf_inf_ker hφ).eq_hull_inter_of_eq_hull normalCone_def]
  congr 1
  ext w
  simp only [mem_inter_iff, mem_image, SetLike.mem_coe, Submodule.mem_inf,
    PointedCone.mem_ofSubmodule_iff, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sub_apply, sub_eq_zero]
  constructor
  · rintro ⟨⟨j, hjx, rfl⟩, -, hj⟩
    refine ⟨j, ⟨hjx, ?_⟩, rfl⟩
    rw [mem_activeSet, facetPairing_apply] at hjx ⊢
    rw [hj, hjx]
  · rintro ⟨j, ⟨hjx, hjy⟩, rfl⟩
    refine ⟨⟨j, hjx, rfl⟩, apply_mem_normalCone hjx, ?_⟩
    rw [mem_activeSet, facetPairing_apply] at hjx hjy
    rw [hjx, hjy]

/-- **Intersections of normal cones.** The normal cones at two points `x` and `y` of the
polyhedron meet in the cone spanned by the normals of the facets through both points. -/
theorem normalCone_inf_normalCone (hx : x ∈ facetPolyhedron i u c)
    (hy : y ∈ facetPolyhedron i u c) :
    normalCone i u c x ⊓ normalCone i u c y =
      PointedCone.hull ℝ ((fun j ↦ i (u j)) ''
        (activeSet (facetPairing i u) c x ∩ activeSet (facetPairing i u) c y)) := by
  refine le_antisymm (fun w hw ↦ ?_) (le_inf (Submodule.span_mono (image_mono inter_subset_left))
    (Submodule.span_mono (image_mono inter_subset_right)))
  obtain ⟨hwx, hwy⟩ := Submodule.mem_inf.1 hw
  -- The pairing with `y - x` is nonnegative on the first cone and nonpositive on the second.
  have h₁ := apply_le_apply_of_mem_normalCone hy hwx
  have h₂ := apply_le_apply_of_mem_normalCone hx hwy
  rw [← normalCone_inf_ker hy]
  refine Submodule.mem_inf.2 ⟨hwx, ?_⟩
  simp only [PointedCone.mem_ofSubmodule_iff, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sub_apply]
  linarith

/-- The intersection of the normal cones at two points `x` and `y` of the polyhedron is a face of
the normal cone at `x`: the face cut out by the pairing with `y - x`. -/
theorem normalCone_inf_isFaceOf_left (hx : x ∈ facetPolyhedron i u c)
    (hy : y ∈ facetPolyhedron i u c) :
    (normalCone i u c x ⊓ normalCone i u c y).IsFaceOf (normalCone i u c x) := by
  rw [normalCone_inf_normalCone hx hy, ← normalCone_inf_ker hy]
  exact PointedCone.isFaceOf_inf_ker fun w hw ↦
    sub_nonneg.2 (apply_le_apply_of_mem_normalCone hy hw)

/-- Translating a facet presentation by `y` translates its normal cones: the normal cone at `y + x`
of the translated presentation is the normal cone at `x`. -/
@[simp]
theorem normalCone_add (y x : StrongDual ℝ V) :
    normalCone i u (fun j ↦ c j + y (i (u j))) (y + x) = normalCone i u c x := by
  rw [normalCone_def, normalCone_def, activeSet_add]

/-! ### Normal cones at smooth vertices -/

namespace IsSmoothVertex

/-- At a smooth vertex the normal cone is regular: it is spanned by the images of an integral
basis of the lattice. -/
theorem isRegularCone_normalCone (hx : IsSmoothVertex i u c x) (hi : IsIntegralLattice i) :
    IsRegularCone i (normalCone i u c x) := by
  obtain ⟨b, hb⟩ := isSmoothVertex_def.1 hx
  have h : (fun j ↦ i (u j)) '' activeSet (facetPairing i u) c x = i '' (b '' univ) := by
    ext w
    simp [hb]
  rw [normalCone_def, h]
  exact isRegularCone_hull_image_basis hi b univ

/-- At a smooth vertex, a direction lies in the normal cone exactly when its pairings with all the
inward edges are nonnegative: in the basis of active normals, the normal cone is the closed
positive orthant, and the edge basis gives the coordinates. -/
theorem mem_normalCone_iff_edgeBasis [Finite ι] (hx : IsSmoothVertex i u c x)
    (hi : IsIntegralLattice i) :
    w ∈ normalCone i u c x ↔ ∀ k, 0 ≤ hx.edgeBasis hi k w := by
  classical
  obtain ⟨b, hb⟩ := isSmoothVertex_def.1 hx
  -- The active normals form a real basis `B` of `V`, dual to the edge basis.
  set B := hi.isBaseChange.basis b
  have hB (k : activeSet (facetPairing i u) c x) : B k = i (u k) := by
    simpa [hb] using hi.isBaseChange.basis_apply b k
  have hcoord (k : activeSet (facetPairing i u) c x) :
      ((hx.edgeBasis hi k : StrongDual ℝ V) : V →ₗ[ℝ] ℝ) = B.coord k :=
    B.ext fun j ↦ by
      rw [ContinuousLinearMap.coe_coe, hB, hx.edgeBasis_apply, Module.Basis.coord_apply, ← hB j,
        Module.Basis.repr_self, Finsupp.single_apply]
      exact if_congr eq_comm rfl rfl
  have hcone : normalCone i u c x = PointedCone.hull ℝ (range B) := by
    rw [normalCone_def]
    congr 1
    ext w
    simp [hB]
  rw [hcone, B.mem_pointedCone_hull_range_iff]
  refine forall_congr' fun k ↦ ?_
  rw [← Module.Basis.coord_apply, ← hcoord, ContinuousLinearMap.coe_coe]

/-- **Normal cones at smooth vertices.** At a smooth vertex `x` of the polyhedron, a direction `w`
lies in the normal cone exactly when the pairing `z ↦ ⟨z, w⟩` attains its minimum over the
polyhedron at `x`. -/
theorem mem_normalCone_iff [Finite ι] (hx : IsSmoothVertex i u c x) (hi : IsIntegralLattice i)
    (hxP : x ∈ facetPolyhedron i u c) :
    w ∈ normalCone i u c x ↔ ∀ z ∈ facetPolyhedron i u c, x w ≤ z w := by
  classical
  refine ⟨fun hw z hz ↦ apply_le_apply_of_mem_normalCone hz hw, fun h ↦ ?_⟩
  rw [hx.mem_normalCone_iff_edgeBasis hi]
  refine fun k ↦ not_lt.1 fun hk ↦ ?_
  -- Moving from `x` along the edge `e_k` stays in the polyhedron and lowers the pairing with `w`.
  set e := hx.edgeBasis hi k
  obtain ⟨t, ht, hmove⟩ := exists_pos_forall_add_smul_mem_polyhedron
    (facetPolyhedron_eq_polyhedron (i := i) (u := u) (c := c) ▸ hxP) e
  have hmem : x + t • e ∈ facetPolyhedron i u c := by
    rw [facetPolyhedron_eq_polyhedron]
    refine hmove t (abs_of_pos ht).le fun j hj ↦ mul_nonneg ht.le ?_
    have he : e (i (u j)) = if k = ⟨j, hj⟩ then 1 else 0 := hx.edgeBasis_apply hi k ⟨j, hj⟩
    rw [facetPairing_apply, he]
    split_ifs <;> norm_num
  have hle := h _ hmem
  rw [add_apply, smul_apply, smul_eq_mul] at hle
  nlinarith

end IsSmoothVertex

/-! ### The normal fan of a Delzant polytope -/

namespace IsDelzant

variable (hΔ : IsDelzant i u c)
include hΔ

/-- **Normal cones determine the facets.** For points `x` and `y` of a Delzant polytope, the
normal cone at `x` lies in the normal cone at `y` exactly when every facet through `x` passes
through `y`. -/
theorem normalCone_le_normalCone_iff (hi : IsIntegralLattice i)
    (hx : x ∈ facetPolyhedron i u c) (hy : y ∈ facetPolyhedron i u c) :
    normalCone i u c x ≤ normalCone i u c y ↔
      activeSet (facetPairing i u) c x ⊆ activeSet (facetPairing i u) c y := by
  refine ⟨fun h j hj ↦ ?_, normalCone_mono⟩
  have hli := hΔ.linearIndepOn_real_activeSet hi hx
  -- The normal `i (u j)` lies in the span of the normals through both points, which are linearly
  -- independent together with it.
  have hmem : i (u j) ∈ PointedCone.hull ℝ ((fun j ↦ i (u j)) ''
      (activeSet (facetPairing i u) c x ∩ activeSet (facetPairing i u) c y)) := by
    rw [← normalCone_inf_normalCone hx hy, inf_eq_left.2 h]
    exact apply_mem_normalCone hj
  exact ((hli.mono inter_subset_left).mem_span_iff.1 (PointedCone.hull_le_span ℝ _ hmem)
    (hli.mono (insert_subset hj inter_subset_left))).2

/-- Two points of a Delzant polytope have the same normal cone exactly when they lie on the same
facets. -/
theorem normalCone_eq_normalCone_iff (hi : IsIntegralLattice i)
    (hx : x ∈ facetPolyhedron i u c) (hy : y ∈ facetPolyhedron i u c) :
    normalCone i u c x = normalCone i u c y ↔
      activeSet (facetPairing i u) c x = activeSet (facetPairing i u) c y := by
  rw [le_antisymm_iff, hΔ.normalCone_le_normalCone_iff hi hx hy,
    hΔ.normalCone_le_normalCone_iff hi hy hx, subset_antisymm_iff]

variable [Finite ι]

/-- Distinct vertices of a Delzant polytope have distinct normal cones. -/
theorem injOn_normalCone (hi : IsIntegralLattice i) :
    InjOn (normalCone i u c) ((facetPolyhedron i u c).extremePoints ℝ) := by
  intro v hv v' hv' h
  have hA := (hΔ.normalCone_eq_normalCone_iff hi (extremePoints_subset hv)
    (extremePoints_subset hv')).1 h
  -- A vertex is determined by the values `c j` it takes on the normals of the facets through it.
  refine sub_eq_zero.1 ((mem_extremePoints_facetPolyhedron_iff.1 hv).2 (v - v') fun j hj ↦ ?_)
  have hj' := hA ▸ hj
  rw [mem_activeSet, facetPairing_apply] at hj hj'
  rw [sub_apply, hj, hj', sub_self]

/-- The *normal fan* of a Delzant polytope: the fan generated by the normal cones at its vertices.
Its cones are the normal cones at all the points of the polytope
(`TauCeti.Toric.IsDelzant.mem_normalFan_cones_iff`), and it is regular and complete. -/
def normalFan (hi : IsIntegralLattice i) : Fan i :=
  Fan.ofCones hi (normalCone i u c '' (facetPolyhedron i u c).extremePoints ℝ)
    ((finite_range fun s : Set ι ↦ PointedCone.hull ℝ ((fun j ↦ i (u j)) '' s)).subset
      (by rintro _ ⟨x, -, rfl⟩; exact ⟨_, rfl⟩))
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact ((hΔ.isSmoothVertex x hx).isRegularCone_normalCone hi).toIsToricCone)
    (by
      rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      exact normalCone_inf_isFaceOf_left (extremePoints_subset hx) (extremePoints_subset hy))

/-- **The cones of the normal fan.** The cones of the normal fan of a Delzant polytope are exactly
the normal cones at the points of the polytope. -/
theorem mem_normalFan_cones_iff (hi : IsIntegralLattice i) {σ : PointedCone ℝ V} :
    σ ∈ (hΔ.normalFan hi).cones ↔ ∃ x ∈ facetPolyhedron i u c, normalCone i u c x = σ := by
  have := hi.finiteDimensional
  rw [normalFan, Fan.mem_ofCones_cones]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, hσ⟩
    -- A face of the normal cone at `v` is spanned by the normals at `v` that it contains, and some
    -- point of the polytope lies on exactly those facets.
    set s := activeSet (facetPairing i u) c v ∩ (fun j ↦ i (u j)) ⁻¹' σ
    have hσs : σ = PointedCone.hull ℝ ((fun j ↦ i (u j)) '' s) := by
      rw [hσ.eq_hull_inter_of_eq_hull normalCone_def, ← image_inter_preimage]
    have hs : (facetFace i u c s).Nonempty :=
      ⟨v, mem_facetFace.2 ⟨extremePoints_subset hv, fun j hj ↦ by
        simpa [mem_activeSet] using hj.1⟩⟩
    obtain ⟨x, hx, hxs⟩ := hΔ.exists_activeSet_eq hi hs
    exact ⟨x, hx, by rw [normalCone_def, hxs, hσs]⟩
  · rintro ⟨x, hx, rfl⟩
    -- The facets through `x` pass through a vertex `v`, and the normal cone at `x` is a face of
    -- the normal cone at `v`.
    obtain ⟨v, hv, hsub⟩ := exists_mem_extremePoints_activeSet_subset hΔ.isCompact hx
    refine ⟨_, ⟨v, hv, rfl⟩, ?_⟩
    have h := normalCone_inf_isFaceOf_left (extremePoints_subset hv) hx
    rwa [inf_eq_right.2 (normalCone_mono hsub)] at h

/-- The normal cone at every point of a Delzant polytope is a cone of its normal fan. -/
theorem normalCone_mem_normalFan_cones (hi : IsIntegralLattice i)
    (hx : x ∈ facetPolyhedron i u c) : normalCone i u c x ∈ (hΔ.normalFan hi).cones :=
  (hΔ.mem_normalFan_cones_iff hi).2 ⟨x, hx, rfl⟩

/-- **The normal fan is regular.** Every cone of the normal fan of a Delzant polytope is regular:
the normal cones at the vertices are spanned by integral bases. -/
theorem isRegular_normalFan (hi : IsIntegralLattice i) : (hΔ.normalFan hi).IsRegular := by
  rw [normalFan, Fan.isRegular_ofCones_iff]
  rintro _ ⟨v, hv, rfl⟩
  exact (hΔ.isSmoothVertex v hv).isRegularCone_normalCone hi

/-- **The normal fan is complete.** Every direction `w` lies in the normal cone at a vertex where
the pairing `z ↦ ⟨z, w⟩` attains its minimum over the polytope. -/
theorem isComplete_normalFan (hi : IsIntegralLattice i) : (hΔ.normalFan hi).IsComplete := by
  have := hi.finiteDimensional
  refine (Fan.isComplete_iff _).2 fun w ↦ ?_
  obtain ⟨v, hv, hmin⟩ := hΔ.isCompact.exists_mem_extremePoints_isMinOn hΔ.nonempty
    (ContinuousLinearMap.apply ℝ ℝ w)
  refine ⟨_, hΔ.normalCone_mem_normalFan_cones hi (extremePoints_subset hv), ?_⟩
  exact ((hΔ.isSmoothVertex v hv).mem_normalCone_iff hi (extremePoints_subset hv)).2
    fun z hz ↦ by simpa using hmin hz

/-! ### Translations -/

/-- Translating a Delzant polytope, which shifts the moment map by a constant, does not change its
normal fan. -/
theorem normalFan_add (hi : IsIntegralLattice i) (y : StrongDual ℝ V) :
    ((isDelzant_add_iff y).2 hΔ).normalFan hi = hΔ.normalFan hi := by
  ext σ
  rw [mem_normalFan_cones_iff, mem_normalFan_cones_iff, facetPolyhedron_add]
  simp only [mem_vadd_set, vadd_eq_add]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, (normalCone_add y x).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨y + x, ⟨x, hx, rfl⟩, normalCone_add y x⟩

end IsDelzant

end TauCeti.Toric
