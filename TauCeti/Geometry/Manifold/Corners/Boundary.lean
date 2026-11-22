/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.OfHomeomorph
public import TauCeti.Geometry.Manifold.Corners.Model

/-!
# The boundary of a manifold with corners is a topological manifold

The boundary of the quadrant `[0, ∞)^(m + 1)` consists of the points with a vanishing
coordinate. Although it has corners, it is homeomorphic to `ℝ^m`: every line parallel to the
diagonal `(1, …, 1)` meets it in exactly one point, the point of the line whose smallest
coordinate is `0`, so projecting along the diagonal identifies it with any hyperplane transverse
to the diagonal. This file uses the coordinates `z ↦ (z₁ - z₀, …, zₘ - z₀)`
(`TauCeti.euclideanQuadrantBoundaryProj`), whose inverse sends `y` to `(0, y₁, …, yₘ)` translated
along the diagonal until its smallest coordinate vanishes
(`TauCeti.euclideanQuadrantBoundaryParam`). The resulting homeomorphism is
`TauCeti.euclideanQuadrantBoundaryHomeomorph`.

Let `M` be a charted space modelled on the quadrant through `𝓡c (m + 1)`, a topological manifold
with corners. Every chart, in the atlas or not, detects its boundary points as the points read
with a vanishing coordinate (`TauCeti.ModelWithCorners.mem_boundary_euclideanQuadrant_iff`): this
is the topological invariance of the boundary, and it needs no condition on the transition maps.
So each chart of `M` restricts to the boundary, and followed by the homeomorphism above it becomes
a chart of the boundary with values in `ℝ^m`. These charts make the boundary of `M` a charted
space modelled on `EuclideanSpace ℝ (Fin m)` (`TauCeti.euclideanQuadrantBoundaryChartedSpace`), a
topological manifold without boundary of one dimension less. Its topology is the subspace topology,
since it is a structure on the subtype `(𝓡c (m + 1)).boundary M`. It is the instance of the general
construction `ModelWithCorners.boundaryChartedSpaceOfHomeomorph` for the homeomorphism above, and
its characteristic lemmas follow those of `TauCeti.halfSpaceBoundaryChartedSpace` in
`TauCeti/Geometry/Manifold/Boundary/ProductHalfSpace.lean`.

The corners of `M` are invisible in this structure: the boundary of the square `[0, 1]²` is a
topological circle. This is the structure under which statements about closed manifolds, such as
the characterization of fundamental classes by their local classes on a dense set, apply to the
boundary of a compact manifold with corners, whose faces are glued along their own boundaries.
The structure is only topological. The transition maps of the boundary charts are not smooth at
the corners, and the smooth manifold one dimension down is the abstract boundary
`ModelWithCorners.AbstractBoundary`, which separates the faces through a corner.

## Main definitions

* `TauCeti.euclideanQuadrantBoundaryProj`, `TauCeti.euclideanQuadrantBoundaryParam`: coordinates
  on the boundary of the quadrant and their inverse.
* `TauCeti.euclideanQuadrantBoundaryHomeomorph`: the boundary of the quadrant `[0, ∞)^(m + 1)` is
  homeomorphic to `ℝ^m`.
* `TauCeti.euclideanQuadrantBoundaryChartedSpace`: the charted-space structure on the boundary of
  a manifold modelled on `𝓡c (m + 1)`, modelled on `EuclideanSpace ℝ (Fin m)`.

## Main results

* `TauCeti.ModelWithCorners.mem_boundary_euclideanQuadrant_iff`: a point lies on the boundary
  exactly when any chart around it reads it with a vanishing coordinate.
* `TauCeti.euclideanQuadrantBoundaryChartedSpace_atlas` and the
  `euclideanQuadrantBoundaryChartedSpace_chartAt_*` lemmas: the atlas of the boundary and the
  source, target, values and inverse of its charts.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer (2013), Chapter 16, section *Manifolds with Corners*, where the quadrant is shown to be
  homeomorphic to the half-space, so that a manifold with corners is a topological manifold with
  boundary.
* D. Joyce, *On manifolds with corners*, in *Advances in Geometric Analysis*, Adv. Lect. Math. 21,
  International Press (2012), 225–258, Section 2, on the boundary of a manifold with corners and
  the abstract boundary. [arXiv:0910.3518](https://arxiv.org/abs/0910.3518)
-/

public section

open Set

open scoped Manifold

namespace TauCeti

/-! ### The boundary of the quadrant -/

section Model

variable {m : ℕ}

/-- The smallest coordinate of a point of `ℝ^(m + 1)`. -/
private noncomputable def minCoord (z : EuclideanSpace ℝ (Fin (m + 1))) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i ↦ z i

private theorem minCoord_le (z : EuclideanSpace ℝ (Fin (m + 1))) (i : Fin (m + 1)) :
    minCoord z ≤ z i :=
  Finset.inf'_le _ (Finset.mem_univ i)

private theorem exists_eq_minCoord (z : EuclideanSpace ℝ (Fin (m + 1))) :
    ∃ i, z i = minCoord z := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty fun i ↦ z i
  exact ⟨i, hi.symm⟩

private theorem continuous_minCoord : Continuous (minCoord (m := m)) :=
  Continuous.finset_inf'_apply Finset.univ_nonempty fun i _ ↦ PiLp.continuous_apply 2 _ i

variable (m) in
/-- Coordinates on the boundary of the quadrant `[0, ∞)^(m + 1)`: the differences
`(z₁ - z₀, …, zₘ - z₀)` of the coordinates with the zeroth one. This linear map is constant along
the diagonal `(1, …, 1)`, and it is injective on the boundary of the quadrant, which meets each
line parallel to the diagonal exactly once. -/
noncomputable def euclideanQuadrantBoundaryProj :
    EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap
    { toFun z := WithLp.toLp 2 fun i ↦ z i.succ - z 0
      map_add' z w := by ext i; simp only [PiLp.add_apply]; ring
      map_smul' c z := by ext i; simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }

@[simp]
theorem euclideanQuadrantBoundaryProj_apply (z : EuclideanSpace ℝ (Fin (m + 1))) (i : Fin m) :
    euclideanQuadrantBoundaryProj m z i = z i.succ - z 0 :=
  (rfl)

/-- The point `(0, y₁, …, yₘ)` translated along the diagonal until its smallest coordinate is
`0`. -/
private noncomputable def boundaryParamAux (y : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (Fin.cons 0 fun i ↦ y i)

private theorem continuous_boundaryParamAux : Continuous (boundaryParamAux (m := m)) :=
  (PiLp.continuous_toLp 2 _).comp <|
    continuous_const.finCons (continuous_pi fun i ↦ PiLp.continuous_apply 2 _ i)

variable (m) in
/-- The inverse of the boundary coordinates `TauCeti.euclideanQuadrantBoundaryProj`: the point
`(0, y₁, …, yₘ)` translated along the diagonal `(1, …, 1)` until its smallest coordinate is `0`.
It lies on the boundary of the quadrant (`TauCeti.exists_euclideanQuadrantBoundaryParam_eq_zero`).
-/
noncomputable def euclideanQuadrantBoundaryParam (y : EuclideanSpace ℝ (Fin m)) :
    EuclideanQuadrant (m + 1) :=
  ⟨WithLp.toLp 2 fun j ↦ boundaryParamAux y j - minCoord (boundaryParamAux y),
    fun j ↦ sub_nonneg.2 (minCoord_le _ j)⟩

theorem coe_euclideanQuadrantBoundaryParam_apply (y : EuclideanSpace ℝ (Fin m))
    (j : Fin (m + 1)) :
    (euclideanQuadrantBoundaryParam m y).val j =
      (Fin.cons 0 (fun i ↦ y i) : Fin (m + 1) → ℝ) j -
        Finset.univ.inf' Finset.univ_nonempty (Fin.cons 0 fun i ↦ y i : Fin (m + 1) → ℝ) :=
  (rfl)

/-- The boundary parametrization lands on the boundary of the quadrant. -/
theorem exists_euclideanQuadrantBoundaryParam_eq_zero (y : EuclideanSpace ℝ (Fin m)) :
    ∃ j, (euclideanQuadrantBoundaryParam m y).val j = 0 := by
  obtain ⟨j, hj⟩ := exists_eq_minCoord (boundaryParamAux y)
  exact ⟨j, sub_eq_zero.2 hj⟩

theorem continuous_euclideanQuadrantBoundaryParam :
    Continuous (euclideanQuadrantBoundaryParam m) :=
  Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp <| continuous_pi fun j ↦
    ((PiLp.continuous_apply 2 _ j).comp continuous_boundaryParamAux).sub
      (continuous_minCoord.comp continuous_boundaryParamAux)) _

/-- The boundary coordinates invert the boundary parametrization. -/
@[simp]
theorem euclideanQuadrantBoundaryProj_euclideanQuadrantBoundaryParam
    (y : EuclideanSpace ℝ (Fin m)) :
    euclideanQuadrantBoundaryProj m (euclideanQuadrantBoundaryParam m y).val = y := by
  ext i
  simp [euclideanQuadrantBoundaryParam, boundaryParamAux]

/-- On the boundary of the quadrant, the boundary parametrization inverts the boundary
coordinates. -/
theorem euclideanQuadrantBoundaryParam_euclideanQuadrantBoundaryProj
    {z : EuclideanQuadrant (m + 1)} (hz : ∃ j, z.val j = 0) :
    euclideanQuadrantBoundaryParam m (euclideanQuadrantBoundaryProj m z.val) = z := by
  -- The auxiliary point is `z` translated by `-z₀` along the diagonal.
  have haux : boundaryParamAux (euclideanQuadrantBoundaryProj m z.val) =
      WithLp.toLp 2 fun j ↦ z.val j - z.val 0 := by
    ext j
    refine Fin.cases ?_ (fun i ↦ ?_) j <;> simp [boundaryParamAux]
  -- Its smallest coordinate is `-z₀`, since the smallest coordinate of `z` is `0`.
  have hmin : minCoord (WithLp.toLp 2 fun j ↦ z.val j - z.val 0) = -z.val 0 := by
    obtain ⟨j, hj⟩ := hz
    refine le_antisymm ?_ (Finset.le_inf' _ _ fun k _ ↦ ?_)
    · simpa [hj] using minCoord_le (WithLp.toLp 2 fun j ↦ z.val j - z.val 0) j
    · simpa using z.property k
  ext j
  simp [euclideanQuadrantBoundaryParam, haux, hmin]

variable (m) in
/-- **The boundary of the quadrant is a Euclidean space.** The points of `[0, ∞)^(m + 1)` with a
vanishing coordinate form a space homeomorphic to `ℝ^m`, through the coordinates
`z ↦ (z₁ - z₀, …, zₘ - z₀)`. -/
noncomputable def euclideanQuadrantBoundaryHomeomorph :
    {z : EuclideanQuadrant (m + 1) // ∃ j, z.val j = 0} ≃ₜ EuclideanSpace ℝ (Fin m) where
  toFun z := euclideanQuadrantBoundaryProj m z.val.val
  invFun y := ⟨euclideanQuadrantBoundaryParam m y, exists_euclideanQuadrantBoundaryParam_eq_zero y⟩
  left_inv z :=
    Subtype.ext <| euclideanQuadrantBoundaryParam_euclideanQuadrantBoundaryProj z.property
  right_inv := euclideanQuadrantBoundaryProj_euclideanQuadrantBoundaryParam
  continuous_toFun := (euclideanQuadrantBoundaryProj m).continuous.comp <|
    continuous_subtypeVal.comp continuous_subtypeVal
  continuous_invFun := continuous_euclideanQuadrantBoundaryParam.subtype_mk _

@[simp]
theorem euclideanQuadrantBoundaryHomeomorph_apply
    (z : {z : EuclideanQuadrant (m + 1) // ∃ j, z.val j = 0}) :
    euclideanQuadrantBoundaryHomeomorph m z = euclideanQuadrantBoundaryProj m z.val.val :=
  (rfl)

@[simp]
theorem coe_euclideanQuadrantBoundaryHomeomorph_symm_apply (y : EuclideanSpace ℝ (Fin m)) :
    ((euclideanQuadrantBoundaryHomeomorph m).symm y : EuclideanQuadrant (m + 1)) =
      euclideanQuadrantBoundaryParam m y :=
  (rfl)

end Model

/-! ### The boundary of a manifold modelled on the quadrant -/

section Manifold

/-- **Topological invariance of the boundary.** A point of a charted space modelled on the
quadrant `[0, ∞)ⁿ` lies on the boundary exactly when any chart around it, in the atlas or not,
reads it with a vanishing coordinate. -/
theorem ModelWithCorners.mem_boundary_euclideanQuadrant_iff {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]
    {e : OpenPartialHomeomorph M (EuclideanQuadrant n)} {x : M} (hx : x ∈ e.source) :
    x ∈ (𝓡c n).boundary M ↔ ∃ i, (e x).val i = 0 := by
  rw [ModelWithCorners.boundary, mem_ofPred_eq,
    ModelWithCorners.isBoundaryPoint_iff_mem_frontier_range_of_finiteDimensional hx,
    modelWithCornersEuclideanQuadrant_mem_frontier_range_iff]

variable (m) in
/-- The boundary coordinates of the quadrant, on the points that the model sends to the frontier
of its range. -/
private noncomputable def euclideanQuadrantFrontierHomeomorph :
    {z : EuclideanQuadrant (m + 1) // (𝓡c (m + 1)) z ∈ frontier (range (𝓡c (m + 1)))} ≃ₜ
      EuclideanSpace ℝ (Fin m) :=
  ((Homeomorph.refl _).subtype modelWithCornersEuclideanQuadrant_mem_frontier_range_iff).trans
    (euclideanQuadrantBoundaryHomeomorph m)

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant (m + 1)) M]

variable (m M) in
/-- The charted-space structure on the boundary of a manifold modelled on the quadrant
`[0, ∞)^(m + 1)`, modelled on `ℝ^m`. Its charts are the charts of `M` restricted to the boundary,
followed by the boundary coordinates `TauCeti.euclideanQuadrantBoundaryProj` of the quadrant. The
implementation is opaque; use the characteristic lemmas below to reason about its charts. -/
@[irreducible, instance] noncomputable def euclideanQuadrantBoundaryChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin m)) ((𝓡c (m + 1)).boundary M) :=
  (𝓡c (m + 1)).boundaryChartedSpaceOfHomeomorph M (euclideanQuadrantFrontierHomeomorph m)
    (fun z ↦ euclideanQuadrantBoundaryProj m z.val) fun _ ↦ rfl

variable (m M) in
/-- The atlas of the boundary is the range of its preferred charts. -/
theorem euclideanQuadrantBoundaryChartedSpace_atlas :
    atlas (EuclideanSpace ℝ (Fin m)) ((𝓡c (m + 1)).boundary M) =
      range fun p : (𝓡c (m + 1)).boundary M ↦ chartAt (EuclideanSpace ℝ (Fin m)) p := by
  unfold euclideanQuadrantBoundaryChartedSpace
  exact ModelWithCorners.boundaryChartedSpaceOfHomeomorph_atlas _ _ _ _ _

/-- The source of the preferred boundary chart at `p` is the part of the boundary that the
preferred chart of `M` at `p` sees. -/
theorem euclideanQuadrantBoundaryChartedSpace_chartAt_source (p : (𝓡c (m + 1)).boundary M) :
    (chartAt (EuclideanSpace ℝ (Fin m)) p).source =
      Subtype.val ⁻¹' (chartAt (EuclideanQuadrant (m + 1)) (p : M)).source := by
  unfold euclideanQuadrantBoundaryChartedSpace
  exact ModelWithCorners.boundaryChartedSpaceOfHomeomorph_chartAt_source p

/-- The target of the preferred boundary chart at `p` is the target of the preferred chart of `M`
at `p`, pulled back along the boundary parametrization of the quadrant. -/
theorem euclideanQuadrantBoundaryChartedSpace_chartAt_target (p : (𝓡c (m + 1)).boundary M) :
    (chartAt (EuclideanSpace ℝ (Fin m)) p).target =
      {y | euclideanQuadrantBoundaryParam m y ∈
        (chartAt (EuclideanQuadrant (m + 1)) (p : M)).target} := by
  unfold euclideanQuadrantBoundaryChartedSpace
  exact ModelWithCorners.boundaryChartedSpaceOfHomeomorph_chartAt_target p

/-- The preferred boundary chart at `p` reads a point through the preferred chart of `M` at `p` and
takes its boundary coordinates in the quadrant. -/
theorem euclideanQuadrantBoundaryChartedSpace_chartAt_apply (p q : (𝓡c (m + 1)).boundary M) :
    chartAt (EuclideanSpace ℝ (Fin m)) p q =
      euclideanQuadrantBoundaryProj m (chartAt (EuclideanQuadrant (m + 1)) (p : M) q).val := by
  unfold euclideanQuadrantBoundaryChartedSpace
  exact ModelWithCorners.boundaryChartedSpaceOfHomeomorph_chartAt_apply p q

/-- On its target, the inverse of the preferred boundary chart at `p` is the inverse of the
preferred chart of `M` at `p`, applied to the boundary parametrization of the quadrant. -/
theorem coe_euclideanQuadrantBoundaryChartedSpace_chartAt_symm_apply
    (p : (𝓡c (m + 1)).boundary M) {y : EuclideanSpace ℝ (Fin m)}
    (hy : euclideanQuadrantBoundaryParam m y ∈
      (chartAt (EuclideanQuadrant (m + 1)) (p : M)).target) :
    ((chartAt (EuclideanSpace ℝ (Fin m)) p).symm y : M) =
      (chartAt (EuclideanQuadrant (m + 1)) (p : M)).symm (euclideanQuadrantBoundaryParam m y) := by
  unfold euclideanQuadrantBoundaryChartedSpace
  exact ModelWithCorners.coe_boundaryChartedSpaceOfHomeomorph_chartAt_symm_apply p hy

end Manifold

end TauCeti
