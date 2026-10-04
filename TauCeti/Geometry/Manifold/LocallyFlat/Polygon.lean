/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import TauCeti.Geometry.Polygon.Simple
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Module.Equiv.Pi
import Mathlib.Topology.Algebra.Module.Equiv.Prod

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

namespace TauCeti

/-- Two vectors with `0 ∉ [-d₁, d₂]`, that is nonzero and not on a common ray from `0`, are
separated by a continuous functional which is negative on `d₁` and positive on `d₂`; it can be
chosen nonzero at any vector `u` on which some functional `ℓ₀` takes the value `1`. -/
private theorem exists_strongDual_neg_pos_ne_zero {d₁ d₂ : V} (h : (0 : V) ∉ segment ℝ (-d₁) d₂)
    (ℓ₀ : StrongDual ℝ V) {u : V} (hu : ℓ₀ u = 1) :
    ∃ ℓ : StrongDual ℝ V, ℓ d₁ < 0 ∧ 0 < ℓ d₂ ∧ ℓ u ≠ 0 := by
  have hclosed : IsClosed (segment ℝ (-d₁) d₂) := by
    rw [segment_eq_image_lineMap]
    exact (isCompact_Icc.image AffineMap.lineMap_continuous).isClosed
  obtain ⟨f, c, hf0, hfc⟩ := geometric_hahn_banach_point_closed (convex_segment _ _) hclosed h
  have h₁ : c < -f d₁ := by simpa using hfc _ (left_mem_segment ℝ _ _)
  have h₂ : c < f d₂ := hfc _ (right_mem_segment ℝ _ _)
  rw [map_zero] at hf0
  by_cases hfu : f u = 0
  · -- Perturb `f` by a small multiple of `ℓ₀`, small enough to keep both signs.
    set ε := c / (|ℓ₀ d₁| + |ℓ₀ d₂| + 1) with hε
    have hpos : 0 < |ℓ₀ d₁| + |ℓ₀ d₂| + 1 := by positivity
    have hεpos : 0 < ε := div_pos hf0 hpos
    have hεc : ε * (|ℓ₀ d₁| + |ℓ₀ d₂| + 1) = c := div_mul_cancel₀ _ hpos.ne'
    refine ⟨f + ε • ℓ₀, ?_, ?_, ?_⟩
    · simp only [add_apply, smul_apply, smul_eq_mul]
      nlinarith [le_abs_self (ℓ₀ d₁), abs_nonneg (ℓ₀ d₂)]
    · simp only [add_apply, smul_apply, smul_eq_mul]
      nlinarith [neg_abs_le (ℓ₀ d₂), abs_nonneg (ℓ₀ d₁)]
    · simp [hfu, hu, hεpos.ne']
  · exact ⟨f, by linarith, by linarith, hfu⟩

/-- If the segments from `z` to `a` and to `b` meet only at `z`, then `a - z` and `b - z` are
nonzero and do not lie on a common ray from `0`: `0 ∉ [-(a - z), b - z]`. -/
private theorem zero_notMem_segment_of_affineSegment_inter_eq {a b z : P} (ha : a ≠ z) (hb : b ≠ z)
    (hab : affineSegment ℝ z a ∩ affineSegment ℝ z b = {z}) :
    (0 : V) ∉ segment ℝ (-(a -ᵥ z)) (b -ᵥ z) := by
  rintro ⟨s, t, hs, ht, hst, he⟩
  rw [smul_neg, neg_add_eq_zero] at he
  have hm : t • (b -ᵥ z) +ᵥ z ∈ affineSegment ℝ z a ∩ affineSegment ℝ z b :=
    ⟨⟨s, ⟨hs, by linarith⟩, by rw [AffineMap.lineMap_apply, he]⟩,
      ⟨t, ⟨ht, by linarith⟩, by rw [AffineMap.lineMap_apply]⟩⟩
  rw [hab, mem_singleton_iff, ← vsub_eq_zero_iff_eq, vadd_vsub, smul_eq_zero] at hm
  rcases hm with rfl | hm
  · rw [zero_smul, smul_eq_zero] at he
    rcases he with rfl | he
    · linarith
    · exact ha (vsub_eq_zero_iff_eq.1 he)
  · exact hb (vsub_eq_zero_iff_eq.1 hm)

/-- Within distance `‖c - z‖` of `z`, the segment from `z` to `c` is the ray from `z` through
`c`. -/
private theorem mem_affineSegment_iff_of_dist_lt {c y z : P} (hy : dist y z < ‖c -ᵥ z‖) :
    y ∈ affineSegment ℝ z c ↔ ∃ t : ℝ, 0 ≤ t ∧ y = t • (c -ᵥ z) +ᵥ z := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht.1, AffineMap.lineMap_apply _ _ _⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t, ⟨ht, ?_⟩, AffineMap.lineMap_apply _ _ _⟩
    rw [dist_vadd_left, norm_smul, Real.norm_of_nonneg ht] at hy
    by_contra! ht1
    nlinarith [norm_nonneg (c -ᵥ z)]

/-- If `ℓ d₁ < 0 < ℓ d₂`, the union of the rays from `z` along `d₁` and along `d₂` is the range of
a continuous map `g` with `ℓ (g s - z) = s`: it runs out along `d₁` for negative parameters and
along `d₂` for positive ones. -/
private theorem exists_continuous_range_eq_rays (ℓ : StrongDual ℝ V) {d₁ d₂ : V} (h₁ : ℓ d₁ < 0)
    (h₂ : 0 < ℓ d₂) (z : P) : ∃ g : ℝ → P, Continuous g ∧ (∀ s, ℓ (g s -ᵥ z) = s) ∧
      ∀ y, y ∈ range g ↔
        (∃ t : ℝ, 0 ≤ t ∧ y = t • d₁ +ᵥ z) ∨ (∃ t : ℝ, 0 ≤ t ∧ y = t • d₂ +ᵥ z) := by
  refine ⟨fun s => ((max s 0 / ℓ d₂) • d₂ + (min s 0 / ℓ d₁) • d₁) +ᵥ z, by fun_prop,
    fun s => ?_, fun y => ⟨?_, ?_⟩⟩
  · rw [vadd_vsub, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
      div_mul_cancel₀ _ h₂.ne', div_mul_cancel₀ _ h₁.ne, max_add_min, add_zero]
  · rintro ⟨s, rfl⟩
    rcases le_total 0 s with hs | hs
    · exact .inr ⟨s / ℓ d₂, div_nonneg hs h₂.le, by simp [max_eq_left hs, min_eq_right hs]⟩
    · exact .inl ⟨s / ℓ d₁, div_nonneg_of_nonpos hs h₁.le,
        by simp [max_eq_right hs, min_eq_left hs]⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · have hs : t * ℓ d₁ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht h₁.le
      exact ⟨t * ℓ d₁, by simp [max_eq_right hs, min_eq_left hs, mul_div_cancel_right₀ _ h₁.ne]⟩
    · have hs : 0 ≤ t * ℓ d₂ := mul_nonneg ht h₂.le
      exact ⟨t * ℓ d₂, by simp [max_eq_left hs, min_eq_right hs, mul_div_cancel_right₀ _ h₂.ne']⟩

/-- A continuous linear equivalence `e : V ≃L[ℝ] ℝ × F'` can have its first coordinate replaced by
any continuous functional `ℓ` not vanishing on `e.symm (1, 0)`. Centred at `z`, this gives a
homeomorphism `P ≃ₜ ℝ × F'` whose first coordinate is `y ↦ ℓ (y -ᵥ z)`. -/
private theorem exists_homeomorph_fst_eq (e : V ≃L[ℝ] ℝ × F') (ℓ : StrongDual ℝ V)
    (hℓ : ℓ (e.symm (1, 0)) ≠ 0) (z : P) : ∃ Φ : P ≃ₜ ℝ × F', ∀ y, (Φ y).1 = ℓ (y -ᵥ z) := by
  set a := ℓ (e.symm (1, 0))
  have key (q : ℝ × F') : ℓ (e.symm q) = q.1 * a + ℓ (e.symm (0, q.2)) := by
    have hq : q = q.1 • ((1 : ℝ), (0 : F')) + (0, q.2) := by ext <;> simp
    calc ℓ (e.symm q) = ℓ (e.symm (q.1 • ((1 : ℝ), (0 : F')) + (0, q.2))) := by rw [← hq]
      _ = q.1 * a + ℓ (e.symm (0, q.2)) := by rw [map_add, map_add, map_smul, map_smul, smul_eq_mul]
  refine ⟨{ toFun := fun y => (ℓ (y -ᵥ z), (e (y -ᵥ z)).2)
            invFun := fun q => e.symm ((q.1 - ℓ (e.symm (0, q.2))) / a, q.2) +ᵥ z
            left_inv := fun y => ?_
            right_inv := fun q => ?_
            continuous_toFun := by fun_prop
            continuous_invFun := by fun_prop }, fun y => rfl⟩
  · have hy := key (e (y -ᵥ z))
    rw [e.symm_apply_apply] at hy
    have h1 : (ℓ (y -ᵥ z) - ℓ (e.symm (0, (e (y -ᵥ z)).2))) / a = (e (y -ᵥ z)).1 := by
      rw [div_eq_iff hℓ]
      linarith
    dsimp only
    rw [h1, Prod.mk.eta, e.symm_apply_apply, vsub_vadd]
  · have hq := key ((q.1 - ℓ (e.symm (0, q.2))) / a, q.2)
    simp only [vadd_vsub, e.apply_symm_apply]
    refine Prod.ext ?_ rfl
    rw [hq, div_mul_cancel₀ _ hℓ]
    ring

end TauCeti

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
  obtain ⟨Φ, hΦ⟩ := exists_homeomorph_fst_eq e ℓ hℓ z
  -- Near `z` the polygon is the union of the rays along `d₁` and `d₂`, a graph over `ℓ`.
  obtain ⟨g, hg, hℓg, hrange⟩ := exists_continuous_range_eq_rays ℓ h₁ h₂ z
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
