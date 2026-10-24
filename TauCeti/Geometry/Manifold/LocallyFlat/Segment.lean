/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Between
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
import TauCeti.Analysis.Convex.Between
import TauCeti.Analysis.LocallyConvex.Separation
import TauCeti.Topology.Algebra.Affine.Coordinate
import TauCeti.Topology.Algebra.Affine.Ray

/-!
# Two segments are flat at their common endpoint

Near each of its points a polygonal curve is two segments `[z, a]` and `[z, b]` from the point,
meeting only there. This file proves that such a configuration is flat at `z`: some chart of the
ambient space around `z` identifies it with a coordinate line. This is the local model behind the
local flatness of polygonal knots (`TauCeti.Geometry.Manifold.LocallyFlat.Polygon`) and of
piecewise-linear curves in charts (`TauCeti.Geometry.Manifold.LocallyFlat.PL`).

The two segments do not lie on a common ray, so a continuous functional `ℓ` separates them, with
`ℓ (a - z) < 0 < ℓ (b - z)`. Near `z` the union of the segments is then the graph over the
coordinate `ℓ (· - z)` of a piecewise affine map, running out along `a - z` for negative values and
along `b - z` for positive ones, and a graph is flattened by shearing
(`TauCeti.exists_isSliceChart_of_inter_eq_inter_range`). An open strip of values of `ℓ` between its
values at the two endpoints truncates the rays to the segments, without a norm or metrizability
assumption. The complementary model is any topological real module `F'` with `V ≃L[ℝ] ℝ × F'`,
where `V` is the space of translations.

That only two segments meet at the point is what makes this work in every codimension: the link of
`z` is a pair of points in a sphere, which is never knotted.

## Main results

* `TauCeti.exists_isSliceChart_of_inter_eq_union_affineSegment`: a set agreeing near `z` with the
  union of two segments from `z`, meeting only at `z`, is flattened by a chart around `z`.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 1, for stars and links of points of polyhedra.
-/

public section

open Set Topology

namespace TauCeti

variable {V P F' : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousSMul ℝ V] [LocallyConvexSpace ℝ V] [T2Space V]
  [AddTorsor V P] [TopologicalSpace P] [IsTopologicalAddTorsor P]
  [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']

/-- **Two segments are flat at their common endpoint.** In a real Hausdorff locally convex affine
space modelled on `V ≃L[ℝ] ℝ × F'`, let a set `A` agree near `z` with the union of two segments
from `z` to points `a` and `b` other than `z`, meeting only at `z`. Then some chart with values in
`ℝ × F'` around `z` identifies `A` in its source with the line `ℝ × {0}` in its target. -/
theorem exists_isSliceChart_of_inter_eq_union_affineSegment (e : V ≃L[ℝ] ℝ × F') {A : Set P}
    {z a b : P} (ha : a ≠ z) (hb : b ≠ z) (hab : affineSegment ℝ z a ∩ affineSegment ℝ z b = {z})
    {U : Set P} (hU : U ∈ 𝓝 z) (hUA : U ∩ A = U ∩ (affineSegment ℝ z a ∪ affineSegment ℝ z b)) :
    ∃ φ : OpenPartialHomeomorph P (ℝ × F'), z ∈ φ.source ∧
      IsSliceChart φ ((univ : Set ℝ) ×ˢ ({0} : Set F')) A := by
  have := IsTopologicalAddTorsor.to_isTopologicalAddGroup V P
  have : IsTopologicalAddGroup F' :=
    (e.symm.toHomeomorph.isInducing.comp (isInducing_prodMkRight (0 : ℝ))).isTopologicalAddGroup
      (e.symm.toLinearMap.comp (LinearMap.inr ℝ ℝ F')).toAddMonoidHom
  obtain ⟨ℓ, h₁, h₂, hℓ⟩ := exists_strongDual_neg_pos_ne_zero
    (zero_notMem_segment_of_affineSegment_inter_eq ha hb hab)
    ((ContinuousLinearMap.fst ℝ ℝ F').comp e.toContinuousLinearMap) (u := e.symm (1, 0))
    (by simp)
  obtain ⟨Φ, hΦ⟩ := e.exists_homeomorph_fst_eq ℓ hℓ z
  -- Near `z` the set is the union of the rays through `a` and `b`, a graph over `ℓ`.
  obtain ⟨g, hg, hℓg, hrange⟩ := ℓ.toLinearMap.exists_continuous_range_eq_rays h₁ h₂ z
  simp only [ContinuousLinearMap.coe_coe] at hℓg
  obtain ⟨U, hUsub, hUopen, hzU⟩ := mem_nhds_iff.1 hU
  -- The open strip between the endpoints truncates both rays to their segments.
  let W := U ∩ (fun y => ℓ (y -ᵥ z)) ⁻¹' Ioo (ℓ (a -ᵥ z)) (ℓ (b -ᵥ z))
  have hW : IsOpen W := hUopen.inter (isOpen_Ioo.preimage (by fun_prop))
  have hzW : z ∈ W := ⟨hzU, by simpa using And.intro h₁ h₂⟩
  obtain ⟨φ, hφ, hslice⟩ := exists_isSliceChart_of_inter_eq_inter_range Φ hg (by simp [hΦ, hℓg])
    (U := W) (A := A) hW <| by
      ext y
      refine and_congr_right fun hy => ?_
      have hb' : y ∈ A ↔ y ∈ affineSegment ℝ z a ∪ affineSegment ℝ z b := by
        simpa [hUsub hy.1] using congrArg (y ∈ ·) hUA
      rw [hb', hrange]
      constructor
      · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
        · exact .inl ⟨t, ht.1, AffineMap.lineMap_apply _ _ _⟩
        · exact .inr ⟨t, ht.1, AffineMap.lineMap_apply _ _ _⟩
      · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
        · refine .inl ⟨t, ⟨ht, ?_⟩, AffineMap.lineMap_apply _ _ _⟩
          have hy₁ := hy.2.1
          simp only [vadd_vsub, map_smul, smul_eq_mul] at hy₁
          nlinarith
        · refine .inr ⟨t, ⟨ht, ?_⟩, AffineMap.lineMap_apply _ _ _⟩
          have hy₂ := hy.2.2
          simp only [vadd_vsub, map_smul, smul_eq_mul] at hy₂
          nlinarith
  exact ⟨φ, hφ ▸ hzW, hslice⟩

end TauCeti
