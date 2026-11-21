/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.Boundary.Collar.Topological

/-!
# The collar of the boundary of a manifold with corners

Let `M` be a charted space modelled on the quadrant `[0, ∞)ⁿ` (`𝓡c n`), a topological manifold
with corners. No smoothness of the transition maps is assumed. This file shows that the boundary
`∂M` of `M`, the points with a vanishing coordinate in a chart, is locally collared in `M`, and
hence collared when it is compact and `M` is Hausdorff: there is an open embedding
`c : ∂M × [0, 1) → M` with `c (x, 0) = x`. This is what the construction of the fundamental class
of a compact manifold relative to its boundary consumes
(`TauCeti.HomologicalOrientation.fundamentalClassRel`, which asks the complement of the interior to
be the image of a collared map). The half-space case is `TauCeti.isCollared_subtypeVal_boundary`.

At a corner the boundary is not a manifold, but it still has a collar. In the model, moving along
the diagonal `(1, …, 1)` identifies the product of the boundary of the quadrant, its points with a
vanishing coordinate, and the half-line `[0, ∞)` with the whole quadrant
(`TauCeti.euclideanQuadrantBoundaryProdHomeomorph`):

`(z, t) ↦ z + t • (1, …, 1)`,

with inverse sending `w` to `w - m • (1, …, 1)` and `m`, where `m` is the smallest coordinate of
`w`. So the boundary of the quadrant has a global collar
(`TauCeti.isCollared_subtypeVal_boundary_euclideanQuadrant`). On `M`, a chart `e` at a boundary
point reads the boundary in the boundary of the quadrant, by the topological invariance of the
boundary (`OpenPartialHomeomorph.isBoundaryPoint_iff`); near the image of the point, the collar of
the quadrant of small enough depth stays in the target of `e`, and `e.symm` carries it to a local
collar of `∂M`, whose points of positive collar depth are interior points of `M`. This transport
works for any finite-dimensional model with a collared boundary
(`TauCeti.isLocallyCollared_subtypeVal_boundary_of_isCollared`), and gives
`TauCeti.isLocallyCollared_subtypeVal_boundary_modelWithCornersEuclideanQuadrant`. Brown's
collaring theorem (`TauCeti.IsLocallyCollared.isCollared`, in the form
`TauCeti.isCollared_subtypeVal_boundary_of_isLocallyCollared`) assembles these local collars into a
global one. In the quadrant, the boundary points are those with a vanishing coordinate
(`TauCeti.ModelWithCorners.mem_boundary_euclideanQuadrant_iff`).

## Main definitions

* `TauCeti.euclideanQuadrantBoundaryProdHomeomorph n`: the homeomorphism
  `∂[0, ∞)ⁿ × [0, ∞) ≃ₜ [0, ∞)ⁿ`, `(z, t) ↦ z + t • (1, …, 1)`, for `n ≠ 0`.

## Main results

* `TauCeti.isCollared_subtypeVal_boundary_euclideanQuadrant`: the boundary of the quadrant is
  collared.
* `TauCeti.isLocallyCollared_subtypeVal_boundary_modelWithCornersEuclideanQuadrant`: the boundary
  of a manifold with corners is locally collared.
* `TauCeti.isCollared_subtypeVal_boundary_modelWithCornersEuclideanQuadrant`: a compact boundary of
  a Hausdorff manifold with corners is collared.
* `TauCeti.isCollared_subtypeVal_boundary_modelWithCornersEuclideanQuadrant_of_compactSpace`: the
  boundary of a compact Hausdorff manifold with corners is collared.

## References

* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
* D. Joyce, *On manifolds with corners*, in *Advances in Geometric Analysis*, Adv. Lect. Math. 21,
  International Press (2012), 225–258, Section 2 (the boundary of a manifold with corners).
  [arXiv:0910.3518](https://arxiv.org/abs/0910.3518)
-/

public section

open Set Topology
open scoped Manifold

namespace TauCeti

section Model

variable (n : ℕ)

/-- In the quadrant itself, the boundary points are the points with a vanishing coordinate. -/
private theorem mem_boundary_euclideanQuadrant_self_iff {z : EuclideanQuadrant n} :
    z ∈ (𝓡c n).boundary (EuclideanQuadrant n) ↔ ∃ i, z.val i = 0 :=
  ModelWithCorners.mem_boundary_euclideanQuadrant_iff (e := OpenPartialHomeomorph.refl _)
    (mem_univ z)

variable [NeZero n]

/-- The smallest coordinate of a point of `ℝⁿ`, for `n ≠ 0`. -/
private noncomputable def minCoord (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i ↦ z i

private theorem minCoord_le (z : EuclideanSpace ℝ (Fin n)) (i : Fin n) : minCoord n z ≤ z i :=
  Finset.inf'_le _ (Finset.mem_univ i)

private theorem exists_eq_minCoord (z : EuclideanSpace ℝ (Fin n)) : ∃ i, z i = minCoord n z :=
  let ⟨i, _, hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty fun i ↦ z i
  ⟨i, hi.symm⟩

private theorem minCoord_nonneg (z : EuclideanQuadrant n) : 0 ≤ minCoord n z.val :=
  Finset.le_inf' _ _ fun i _ ↦ z.property i

/-- The smallest coordinate of `z + t • (1, …, 1)` is `t` when `z` lies on the boundary of the
quadrant. -/
private theorem minCoord_add {z : EuclideanQuadrant n}
    (hz : z ∈ (𝓡c n).boundary (EuclideanQuadrant n)) (t : ℝ) :
    minCoord n (WithLp.toLp 2 fun i ↦ z.val i + t) = t := by
  obtain ⟨i, hi⟩ := (mem_boundary_euclideanQuadrant_self_iff n).1 hz
  refine le_antisymm ?_ (Finset.le_inf' _ _ fun j _ ↦ ?_)
  · simpa [hi] using minCoord_le n (WithLp.toLp 2 fun i ↦ z.val i + t) i
  · simpa using z.property j

/-- The translate `w - m • (1, …, 1)` of a point `w` of the quadrant by its smallest coordinate
`m`, a point of the boundary of the quadrant. -/
private noncomputable def boundaryProj (w : EuclideanQuadrant n) :
    (𝓡c n).boundary (EuclideanQuadrant n) :=
  ⟨⟨WithLp.toLp 2 fun i ↦ w.val i - minCoord n w.val, fun i ↦ sub_nonneg.2 (minCoord_le n _ i)⟩,
    (mem_boundary_euclideanQuadrant_self_iff n).2 <|
      let ⟨i, hi⟩ := exists_eq_minCoord n w.val
      ⟨i, by simp [hi]⟩⟩

/-- **The quadrant is its boundary times a half-line.** For `n ≠ 0`, moving along the diagonal,
`(z, t) ↦ z + t • (1, …, 1)`, identifies the product of the boundary of the quadrant `[0, ∞)ⁿ`
(its points with a vanishing coordinate) and the half-line `[0, ∞)` with the quadrant. The inverse
sends `w` to `w - m • (1, …, 1)` and `m`, where `m` is the smallest coordinate of `w`
(`TauCeti.euclideanQuadrantBoundaryProdHomeomorph_symm_apply_fst_coe`,
`TauCeti.euclideanQuadrantBoundaryProdHomeomorph_symm_apply_snd_coe`). -/
noncomputable def euclideanQuadrantBoundaryProdHomeomorph :
    (𝓡c n).boundary (EuclideanQuadrant n) × Ici (0 : ℝ) ≃ₜ EuclideanQuadrant n where
  toFun p := ⟨WithLp.toLp 2 fun i ↦ p.1.val.val i + p.2,
    fun i ↦ add_nonneg (p.1.val.property i) p.2.property⟩
  invFun w := (boundaryProj n w, ⟨minCoord n w.val, minCoord_nonneg n w⟩)
  left_inv p := by
    have h := minCoord_add n p.1.property p.2
    refine Prod.ext (Subtype.ext (EuclideanQuadrant.ext _ _ ?_)) (Subtype.ext h)
    ext i
    simp [boundaryProj, h]
  right_inv w := EuclideanQuadrant.ext _ _ (by ext i; simp [boundaryProj])
  continuous_toFun := by
    refine Continuous.subtype_mk ((PiLp.continuous_toLp 2 _).comp ?_) _
    exact continuous_pi fun i ↦ ((PiLp.continuous_apply 2 _ i).comp
      (continuous_subtypeVal.comp (continuous_subtypeVal.comp continuous_fst))).add
        (continuous_subtypeVal.comp continuous_snd)
  continuous_invFun := by
    have hm : Continuous fun w : EuclideanQuadrant n ↦ minCoord n w.val :=
      Continuous.finset_inf'_apply _ fun i _ ↦ (PiLp.continuous_apply 2 _ i).comp
        continuous_subtypeVal
    refine .prodMk (Continuous.subtype_mk (Continuous.subtype_mk
      ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦
        ((PiLp.continuous_apply 2 _ i).comp continuous_subtypeVal).sub hm)) _) _)
      (hm.subtype_mk _)

/-- The diagonal homeomorphism translates a boundary point `z` by `t` along the diagonal:
coordinate `i` of the image of `(z, t)` is `z i + t`. -/
@[simp]
theorem coe_euclideanQuadrantBoundaryProdHomeomorph_apply
    (p : (𝓡c n).boundary (EuclideanQuadrant n) × Ici (0 : ℝ)) (i : Fin n) :
    (euclideanQuadrantBoundaryProdHomeomorph n p).val i = p.1.val.val i + p.2 :=
  (rfl)

/-- The depth coordinate of the inverse of the diagonal homeomorphism is the smallest coordinate. -/
@[simp]
theorem euclideanQuadrantBoundaryProdHomeomorph_symm_apply_snd_coe (w : EuclideanQuadrant n) :
    ((euclideanQuadrantBoundaryProdHomeomorph n).symm w).2 =
      Finset.univ.inf' Finset.univ_nonempty fun i ↦ w.val i :=
  (rfl)

/-- The boundary coordinate of the inverse of the diagonal homeomorphism is the translate of a point
by minus its smallest coordinate along the diagonal. -/
@[simp]
theorem euclideanQuadrantBoundaryProdHomeomorph_symm_apply_fst_coe (w : EuclideanQuadrant n)
    (i : Fin n) :
    ((euclideanQuadrantBoundaryProdHomeomorph n).symm w).1.val.val i =
      w.val i - Finset.univ.inf' Finset.univ_nonempty fun i ↦ w.val i :=
  (rfl)

/-- The diagonal homeomorphism is the identity on the boundary at depth zero. -/
@[simp]
theorem euclideanQuadrantBoundaryProdHomeomorph_apply_zero
    (z : (𝓡c n).boundary (EuclideanQuadrant n)) :
    euclideanQuadrantBoundaryProdHomeomorph n (z, ⟨0, le_rfl⟩) = z :=
  EuclideanQuadrant.ext _ _ (by ext i; simp)

end Model

/-- **The boundary of the quadrant is collared.** For every `n`, the inclusion of the boundary of
the quadrant `[0, ∞)ⁿ`, its points with a vanishing coordinate, has a collar: for `n ≠ 0` the
diagonal homeomorphism `TauCeti.euclideanQuadrantBoundaryProdHomeomorph` restricted to depths in
`[0, 1)`, and for `n = 0` the boundary is empty. -/
theorem isCollared_subtypeVal_boundary_euclideanQuadrant (n : ℕ) :
    IsCollared (Subtype.val : (𝓡c n).boundary (EuclideanQuadrant n) → EuclideanQuadrant n) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · have : IsEmpty ((𝓡c 0).boundary (EuclideanQuadrant 0)) :=
      ⟨fun z ↦ let ⟨i, _⟩ := (mem_boundary_euclideanQuadrant_self_iff 0).1 z.property; i.elim0⟩
    exact IsCollar.isCollared ⟨.of_isEmpty (fun p ↦ isEmptyElim p.1), isEmptyElim⟩
  have : NeZero n := ⟨hn.ne'⟩
  -- Depths in `[0, 1)` form an open subset of `[0, ∞)`.
  have hIco : (Subtype.val ⁻¹' Ico (0 : ℝ) 1 : Set (Ici (0 : ℝ))) = Subtype.val ⁻¹' Iio 1 := by
    ext t
    exact and_iff_right t.property
  have hincl : IsOpenEmbedding (inclusion (Ico_subset_Ici_self : Ico (0 : ℝ) 1 ⊆ Ici 0)) :=
    .inclusion _ (hIco ▸ isOpen_Iio.preimage continuous_subtypeVal)
  exact IsCollar.isCollared ⟨(euclideanQuadrantBoundaryProdHomeomorph n).isOpenEmbedding.comp
    (IsOpenEmbedding.id.prodMap hincl), euclideanQuadrantBoundaryProdHomeomorph_apply_zero n⟩

section Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant n) M]

/-- **The boundary of a manifold with corners is locally collared.** For a charted space over the
quadrant `[0, ∞)ⁿ`, every boundary point has an open neighbourhood in the boundary with a collar in
`M` whose points of positive collar depth are interior points. -/
theorem isLocallyCollared_subtypeVal_boundary_modelWithCornersEuclideanQuadrant :
    IsLocallyCollared ((↑) : (𝓡c n).boundary M → M) :=
  isLocallyCollared_subtypeVal_boundary_of_isCollared
    (isCollared_subtypeVal_boundary_euclideanQuadrant n)

/-- **The collar of a compact boundary of a manifold with corners.** If the boundary of a Hausdorff
charted space over the quadrant is compact, then it is collared: there is an open embedding
`c : ∂M × [0, 1) → M` with `c (x, 0) = x`. This is Brown's collaring theorem applied to the local
collars. -/
theorem isCollared_subtypeVal_boundary_modelWithCornersEuclideanQuadrant [T2Space M]
    (hK : IsCompact ((𝓡c n).boundary M)) : IsCollared ((↑) : (𝓡c n).boundary M → M) :=
  isCollared_subtypeVal_boundary_of_isLocallyCollared
    isLocallyCollared_subtypeVal_boundary_modelWithCornersEuclideanQuadrant hK

/-- **The boundary of a compact manifold with corners is collared.** For a compact Hausdorff
charted space over the quadrant, there is an open embedding `c : ∂M × [0, 1) → M` with
`c (x, 0) = x`. -/
theorem isCollared_subtypeVal_boundary_modelWithCornersEuclideanQuadrant_of_compactSpace
    [CompactSpace M] [T2Space M] : IsCollared ((↑) : (𝓡c n).boundary M → M) :=
  isCollared_subtypeVal_boundary_of_isLocallyCollared_of_compactSpace
    isLocallyCollared_subtypeVal_boundary_modelWithCornersEuclideanQuadrant

end Manifold

end TauCeti
