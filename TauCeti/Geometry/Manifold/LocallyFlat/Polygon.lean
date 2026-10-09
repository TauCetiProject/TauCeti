/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import TauCeti.Geometry.Polygon.Simple
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.Topology.Algebra.Module.Equiv.Prod
import TauCeti.Analysis.Convex.Between
import TauCeti.Analysis.LocallyConvex.Separation
import TauCeti.Analysis.Normed.Affine.Ray
import TauCeti.Topology.Algebra.Affine.Ray
import TauCeti.Topology.Algebra.Affine.Coordinate

/-!
# Polygonal knots are locally flat

A simple closed polygon in a real normed affine space is a tame embedded circle: around each of its
points some chart of the ambient space carries it onto a coordinate line. This file proves that the
realization `TauCeti.SimplePolygon.realize` of a simple polygon is a locally flat embedding of the
circle, `TauCeti.IsLocallyFlat`, so that polygonal knots in `ℝ³`, the polygonal presentation of
knots (Burde and Zieschang, Definition 1.3), are among the locally flat embeddings to which the
topological notions of concordance and sliceness apply.

The flattening chart at a point `z` of the polygon comes from its local structure,
`Polygon.IsSimple.exists_mem_nhds_inter_boundary_eq`: near `z` the polygon is two segments from
`z`, to points `a` and `b`, meeting only at `z`. Hence `a - z` and `b - z` do not lie on a common
ray, and a continuous functional `ℓ` separates them, with `ℓ (a - z) < 0 < ℓ (b - z)`. Near `z` the
polygon is then the graph over the coordinate `ℓ (· - z)` of a piecewise affine map, running out
along `a - z` for negative values and along `b - z` for positive ones, and a graph is flattened by
shearing (`TauCeti.exists_isSliceChart_of_inter_eq_inter_range`). The complementary model of the
local flatness is any `F'` with `V ≃L[ℝ] ℝ × F'`, where `V` is the space of translations; for a knot
in `ℝ³` it is `ℝ²`.

That a polygonal curve is locally flat is special to curves. A piecewise-linear embedding of a
manifold of dimension at least two need not be locally flat in codimension two: the cone on a
knotted circle in `S³` is a piecewise-linear disc in the four-ball which is not locally flat at the
cone point. For a curve the link of a vertex is a pair of points in a sphere, which is never
knotted, and that is what the separating functional above uses.

## Main results

* `Polygon.IsSimple.exists_isSliceChart`: every point of a simple polygon has a chart with values in
  `ℝ × F'` carrying the polygon onto `ℝ × {0}`.
* `TauCeti.SimplePolygon.isLocallyFlat_realize`: the realization of a simple polygon is locally
  flat, with complementary model `F'`.
* `TauCeti.SimplePolygon.isLocallyFlat_realize_euclideanSpace`: a polygonal knot in `ℝᵐ⁺¹` is
  locally flat, with complementary model `ℝᵐ`.

## References

* G. Burde, H. Zieschang, *Knots*, 2nd ed., De Gruyter Studies in Mathematics 5 (2003),
  Chapter 1, Definition 1.3 (tame knots).
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 1, for stars and links of points of polyhedra.
-/

public section

open Set Topology

variable {V P F' : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P] [NormedAddCommGroup F'] [NormedSpace ℝ F']

namespace Polygon

open TauCeti

/-- **A simple polygon is flat at each of its points.** In a real normed affine space modelled on
`V ≃L[ℝ] ℝ × F'`, every point of a simple polygon lies in the source of a chart with values in
`ℝ × F'` carrying the polygon onto the line `ℝ × {0}`. -/
theorem IsSimple.exists_isSliceChart {n : ℕ} [NeZero n] {poly : Polygon P n}
    (h : poly.IsSimple ℝ) (e : V ≃L[ℝ] ℝ × F') {z : P} (hz : z ∈ poly.boundary ℝ) :
    ∃ φ : OpenPartialHomeomorph P (ℝ × F'), z ∈ φ.source ∧
      IsSliceChart φ ((univ : Set ℝ) ×ˢ ({0} : Set F')) (poly.boundary ℝ) := by
  obtain ⟨a, b, ha, hb, hab, U, hU, hUeq⟩ := h.exists_mem_nhds_inter_boundary_eq hz
  set d₁ := a -ᵥ z
  set d₂ := b -ᵥ z
  have hd₁ : 0 < ‖d₁‖ := norm_pos_iff.2 (vsub_ne_zero.2 ha)
  have hd₂ : 0 < ‖d₂‖ := norm_pos_iff.2 (vsub_ne_zero.2 hb)
  obtain ⟨ℓ, h₁, h₂, hℓ⟩ := exists_strongDual_neg_pos_ne_zero
    (zero_notMem_segment_of_affineSegment_inter_eq ha hb hab)
    ((ContinuousLinearMap.fst ℝ ℝ F').comp e.toContinuousLinearMap) (u := e.symm (1, 0))
    (by simp)
  obtain ⟨Φ, hΦ⟩ := e.exists_homeomorph_fst_eq ℓ hℓ z
  -- Near `z` the polygon is the union of the rays along `d₁` and `d₂`, a graph over `ℓ`.
  obtain ⟨g, hg, hℓg, hrange⟩ := ℓ.toLinearMap.exists_continuous_range_eq_rays h₁ h₂ z
  simp only [ContinuousLinearMap.coe_coe] at hℓg
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  set ρ := min r (min ‖d₁‖ ‖d₂‖)
  have hρ : 0 < ρ := lt_min hr (lt_min hd₁ hd₂)
  obtain ⟨φ, hφ, hslice⟩ := exists_isSliceChart_of_inter_eq_inter_range Φ hg (by simp [hΦ, hℓg])
    (U := Metric.ball z ρ) (A := poly.boundary ℝ) Metric.isOpen_ball <| by
      ext y
      refine and_congr_right fun hy => ?_
      have hyU : y ∈ U := hrU (Metric.ball_subset_ball (min_le_left _ _) hy)
      rw [Metric.mem_ball] at hy
      have hy₁ : dist y z < ‖a -ᵥ z‖ := hy.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      have hy₂ : dist y z < ‖b -ᵥ z‖ := hy.trans_le ((min_le_right _ _).trans (min_le_right _ _))
      have hb' : y ∈ poly.boundary ℝ ↔ y ∈ affineSegment ℝ z a ∪ affineSegment ℝ z b := by
        simpa [hyU] using congrArg (y ∈ ·) hUeq
      rw [hb', mem_union, mem_affineSegment_iff_of_dist_lt hy₁,
        mem_affineSegment_iff_of_dist_lt hy₂, hrange]
  exact ⟨φ, hφ ▸ Metric.mem_ball_self hρ, hslice⟩

end Polygon

namespace TauCeti.SimplePolygon

/-- **A polygonal knot is locally flat.** The realization of a simple polygon in a real normed
affine space modelled on `V ≃L[ℝ] ℝ × F'` is a locally flat embedding of the circle, with
complementary model `F'`. -/
theorem isLocallyFlat_realize (p : SimplePolygon ℝ P) (e : V ≃L[ℝ] ℝ × F') :
    IsLocallyFlat ℝ F' p.realize := by
  refine isLocallyFlat_iff_isSliceEmbedding.2 ⟨p.isClosedEmbedding_realize.isEmbedding, fun x => ?_⟩
  rw [p.range_realize]
  exact p.isSimple.exists_isSliceChart e (p.range_realize ▸ mem_range_self x)

/-- A polygonal knot in `ℝᵐ⁺¹` is locally flat, with complementary model `ℝᵐ`; for `m = 2` these
are the polygonal knots in `ℝ³`. -/
theorem isLocallyFlat_realize_euclideanSpace {m : ℕ}
    (p : SimplePolygon ℝ (EuclideanSpace ℝ (Fin (m + 1)))) :
    IsLocallyFlat ℝ (EuclideanSpace ℝ (Fin m)) p.realize :=
  p.isLocallyFlat_realize <| (EuclideanSpace.equiv (Fin (m + 1)) ℝ).trans <|
    (Fin.consEquivL ℝ fun _ => ℝ).symm.trans <|
      (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (EuclideanSpace.equiv (Fin m) ℝ).symm

end TauCeti.SimplePolygon
