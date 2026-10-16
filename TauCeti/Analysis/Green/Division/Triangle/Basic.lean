/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Division.Green
public import TauCeti.Analysis.Green.Polygonal.Basic
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The standard triangular division

The right triangle with vertices `0`, `1`, and `I` is simultaneously a vertical and a
horizontal graph cell. Its actual convex hull is identified with the graph region, and
its finite directional divisions compare geometrically with the three straight edges.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Green

/-- The standard closed positively oriented triangle. -/
def standardTriangle : Set ℂ := convexHull ℝ {0, 1, Complex.I}

/-- The triangle is the actual convex hull of its three vertices. -/
theorem standardTriangle_def : standardTriangle = convexHull ℝ {0, 1, Complex.I} := (rfl)

/-- Barycentric coordinates give the three half-plane inequalities of the standard triangle. -/
@[simp]
theorem mem_standardTriangle {z : ℂ} : z ∈ standardTriangle ↔
    0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re + z.im ≤ 1 := by
  let T : Set ℂ := {z | 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re + z.im ≤ 1}
  have hconv : Convex ℝ T :=
    ((convex_Ici (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).inter
      (((convex_Ici (0 : ℝ)).linear_preimage Complex.imCLM.toLinearMap).inter
        ((convex_Iic (1 : ℝ)).linear_preimage
          (Complex.reCLM + Complex.imCLM).toLinearMap))
  constructor
  · intro hz
    exact convexHull_min (s := ({0, 1, Complex.I} : Set ℂ))
      (by simp [T, insert_subset_iff]) hconv hz
  · rintro ⟨hx, hy, hxy⟩
    exact mem_convexHull_of_exists_fintype
      ![1 - z.re - z.im, z.re, z.im] ![0, 1, Complex.I]
      (by intro i; fin_cases i <;> simp <;> linarith)
      (by simp [Fin.sum_univ_succ])
      (by intro i; fin_cases i <;> simp)
      (by apply Complex.ext <;> simp [Fin.sum_univ_succ])

/-- The standard triangle is exactly its vertical graph cell, including the boundary. -/
theorem standardTriangle_eq_verticalRegion :
    standardTriangle = verticalRegion 0 1 (fun _ ↦ 0) (fun x ↦ 1 - x) := by
  ext z
  rw [mem_standardTriangle, mem_verticalRegion]
  constructor
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨⟨hx, by linarith⟩, ⟨hy, by linarith⟩⟩
  · rintro ⟨⟨hx, _⟩, ⟨hy, hxy⟩⟩
    exact ⟨hx, hy, by linarith⟩

/-- The same triangle has an independent horizontal graph-cell description. -/
theorem standardTriangle_eq_horizontalRegion :
    standardTriangle = horizontalRegion 0 1 (fun _ ↦ 0) (fun y ↦ 1 - y) := by
  ext z
  rw [mem_standardTriangle, mem_horizontalRegion]
  constructor
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨⟨hy, by linarith⟩, ⟨hx, by linarith⟩⟩
  · rintro ⟨⟨hy, _⟩, ⟨hx, hxy⟩⟩
    exact ⟨hx, hy, by linarith⟩

namespace GraphCell

/-- The continuous affine graphs presenting the standard triangle in either direction. -/
def standardTriangleCell : GraphCell :=
  ofFunctions 0 1 zero_lt_one (fun _ ↦ 0) (fun x ↦ 1 - x)
    continuousOn_const (continuous_const.sub continuous_id).continuousOn
    (fun _ hx ↦ sub_nonneg.mpr hx.2)
    ⟨∅, finite_empty, contDiffOn_const⟩
    ⟨∅, finite_empty, (contDiff_const.sub contDiff_id).contDiffOn⟩

@[simp]
theorem standardTriangleCell_a : standardTriangleCell.a = 0 := by
  simp [standardTriangleCell]

@[simp]
theorem standardTriangleCell_b : standardTriangleCell.b = 1 := by
  simp [standardTriangleCell]

-- Normalize concrete bounds before the general extension-to-subtype simplification.
@[simp high]
theorem standardTriangleCell_lowerFun {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    standardTriangleCell.lowerFun x = 0 := by
  simp [standardTriangleCell, hx]

@[simp high]
theorem standardTriangleCell_upperFun {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    standardTriangleCell.upperFun x = 1 - x := by
  simp [standardTriangleCell, hx]

/-- Both coordinate directions of the cell cover exactly the genuine triangle. -/
@[simp]
theorem region_standardTriangleCell (d : Coordinate) :
    standardTriangleCell.region d = standardTriangle := by
  cases d
  · rw [standardTriangle_eq_verticalRegion]
    ext z
    simp only [region_re, mem_verticalRegion, standardTriangleCell_a, standardTriangleCell_b]
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨hx, by simpa only [standardTriangleCell_lowerFun hx,
        standardTriangleCell_upperFun hx] using hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨hx, by simpa only [standardTriangleCell_lowerFun hx,
        standardTriangleCell_upperFun hx] using hy⟩
  · rw [standardTriangle_eq_horizontalRegion]
    ext z
    simp only [region_im, mem_horizontalRegion, standardTriangleCell_a, standardTriangleCell_b]
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨hx, by simpa only [standardTriangleCell_lowerFun hx,
        standardTriangleCell_upperFun hx] using hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨hx, by simpa only [standardTriangleCell_lowerFun hx,
        standardTriangleCell_upperFun hx] using hy⟩

private theorem graphPath_standardTriangleCell_lower (d : Coordinate) :
    BoundaryChain.ofPath (BoundaryChain.graphPath d standardTriangleCell.lowerFun 0 1
      standardTriangleCell.continuous_lowerFun.continuousOn) =
      BoundaryChain.ofPath (Path.segment (d.graph (fun _ ↦ 0) 0)
        (d.graph (fun _ ↦ 0) 1)) := by
  apply BoundaryChain.ofPath_congr
  intro t
  cases d <;> apply Complex.ext <;>
    simp only [BoundaryChain.graphPath_apply, AffineMap.lineMap_apply_module,
      smul_eq_mul, mul_zero, mul_one, zero_add, standardTriangleCell_lowerFun t.prop,
      Coordinate.graph_re_apply, Coordinate.graph_im_apply, Path.segment_apply,
      Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
      add_zero]

private theorem graphPath_standardTriangleCell_upper (d : Coordinate) :
    BoundaryChain.ofPath (BoundaryChain.graphPath d standardTriangleCell.upperFun 0 1
      standardTriangleCell.continuous_upperFun.continuousOn) =
      BoundaryChain.ofPath (Path.segment (d.graph (fun x ↦ 1 - x) 0)
        (d.graph (fun x ↦ 1 - x) 1)) := by
  apply BoundaryChain.ofPath_congr
  intro t
  cases d <;> apply Complex.ext <;>
    simp only [BoundaryChain.graphPath_apply, AffineMap.lineMap_apply_module,
      smul_eq_mul, mul_zero, mul_one, zero_add, standardTriangleCell_upperFun t.prop,
      Coordinate.graph_re_apply, Coordinate.graph_im_apply, Path.segment_apply,
      Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
      sub_zero, sub_self, add_zero]

private theorem boundary_standardTriangleCell_re :
    standardTriangleCell.boundary .re =
      BoundaryChain.ofPath (Path.segment 0 1) + BoundaryChain.ofPath (Path.segment 1 1) -
      BoundaryChain.ofPath (Path.segment Complex.I 1) -
      BoundaryChain.ofPath (Path.segment 0 Complex.I) := by
  rw [boundary_def, BoundaryChain.cellBoundary_def]
  rw [standardTriangleCell_a, standardTriangleCell_b]
  simp only [Coordinate.orientation_re, one_smul, BoundaryChain.quadrilateral_def]
  rw [graphPath_standardTriangleCell_lower, graphPath_standardTriangleCell_upper]
  have h₀ : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h₁ : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hL0 : Coordinate.re.graph standardTriangleCell.lowerFun 0 = 0 := by
    rw [Coordinate.graph_re_apply, standardTriangleCell_lowerFun h₀]
    apply Complex.ext <;> simp
  have hL1 : Coordinate.re.graph standardTriangleCell.lowerFun 1 = 1 := by
    rw [Coordinate.graph_re_apply, standardTriangleCell_lowerFun h₁]
    apply Complex.ext <;> simp
  have hU0 : Coordinate.re.graph standardTriangleCell.upperFun 0 = Complex.I := by
    rw [Coordinate.graph_re_apply, standardTriangleCell_upperFun h₀]
    apply Complex.ext <;> simp
  have hU1 : Coordinate.re.graph standardTriangleCell.upperFun 1 = 1 := by
    rw [Coordinate.graph_re_apply, standardTriangleCell_upperFun h₁]
    apply Complex.ext <;> simp
  have hr (g : ℝ → ℝ) : Coordinate.re.graph g = fun x ↦ (⟨x, g x⟩ : ℂ) :=
    funext (Coordinate.graph_re_apply g)
  rw [hL0, hL1, hU0, hU1, hr (fun _ ↦ 0), hr (fun x ↦ 1 - x)]
  dsimp only
  rw [sub_zero, sub_self]
  rfl

private theorem boundary_standardTriangleCell_im :
    standardTriangleCell.boundary .im =
      BoundaryChain.triangle 0 1 Complex.I -
      BoundaryChain.ofPath (Path.segment Complex.I Complex.I) := by
  rw [boundary_def, BoundaryChain.cellBoundary_def]
  rw [standardTriangleCell_a, standardTriangleCell_b]
  simp only [Coordinate.orientation_im, neg_smul, one_smul, BoundaryChain.quadrilateral_def]
  rw [graphPath_standardTriangleCell_lower, graphPath_standardTriangleCell_upper]
  have h₀ : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h₁ : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hL0 : Coordinate.im.graph standardTriangleCell.lowerFun 0 = 0 := by
    rw [Coordinate.graph_im_apply, standardTriangleCell_lowerFun h₀]
    apply Complex.ext <;> simp
  have hL1 : Coordinate.im.graph standardTriangleCell.lowerFun 1 = Complex.I := by
    rw [Coordinate.graph_im_apply, standardTriangleCell_lowerFun h₁]
    apply Complex.ext <;> simp
  have hU0 : Coordinate.im.graph standardTriangleCell.upperFun 0 = 1 := by
    rw [Coordinate.graph_im_apply, standardTriangleCell_upperFun h₀]
    apply Complex.ext <;> simp
  have hU1 : Coordinate.im.graph standardTriangleCell.upperFun 1 = Complex.I := by
    rw [Coordinate.graph_im_apply, standardTriangleCell_upperFun h₁]
    apply Complex.ext <;> simp
  have hi (g : ℝ → ℝ) : Coordinate.im.graph g = fun x ↦ (⟨g x, x⟩ : ℂ) :=
    funext (Coordinate.graph_im_apply g)
  rw [hL0, hL1, hU0, hU1, hi (fun _ ↦ 0), hi (fun x ↦ 1 - x)]
  dsimp only
  rw [sub_zero, sub_self, BoundaryChain.triangle_def]
  -- The signed quadrilateral and triangle definitions have the same three nonzero edges.
  change -(BoundaryChain.ofPath (Path.segment 0 Complex.I) +
    BoundaryChain.ofPath (Path.segment Complex.I Complex.I) -
    BoundaryChain.ofPath (Path.segment 1 Complex.I) -
    BoundaryChain.ofPath (Path.segment 0 1)) = _
  abel

end GraphCell

/-- The standard triangle is compact. -/
theorem isCompact_standardTriangle : IsCompact standardTriangle := by
  simpa only [GraphCell.region_standardTriangleCell] using
    GraphCell.standardTriangleCell.isCompact_region .re

namespace Division

/-- Independent singleton divisions of the standard triangle in either coordinate direction. -/
def standardTriangleDivision (d : Coordinate) : Division d Green.standardTriangle where
  cells := {GraphCell.standardTriangleCell}
  covers := by simp
  aedisjoint := by simp

@[simp]
theorem standardTriangleDivision_cells (d : Coordinate) :
    (standardTriangleDivision d).cells = {GraphCell.standardTriangleCell} := (rfl)

/-- The triangle division has the actual four-edge cell boundary. -/
@[simp]
theorem boundary_standardTriangleDivision (d : Coordinate) :
    (standardTriangleDivision d).boundary = GraphCell.standardTriangleCell.boundary d := by
  simp [boundary_def]

/-- The type-II cell differs from the three-edge cycle only by a collapsed constant edge. -/
theorem standardTriangle_null_im (U : Set ℂ) :
    BoundaryChain.NullChain .im U
      ((standardTriangleDivision .im).boundary - BoundaryChain.triangle 0 1 Complex.I) := by
  rw [boundary_standardTriangleDivision, GraphCell.boundary_standardTriangleCell_im,
    sub_sub_cancel_left]
  exact (BoundaryChain.NullChain.segment (by rfl)).neg

/-- The type-I cell compares with the same three-edge cycle by reversing the diagonal and
removing a collapsed edge. The graph used for reversal is contained in the triangle. -/
theorem standardTriangle_null_re {U : Set ℂ} (hU : Green.standardTriangle ⊆ U) :
    BoundaryChain.NullChain .re U
      ((standardTriangleDivision .re).boundary - BoundaryChain.triangle 0 1 Complex.I) := by
  let K := GraphCell.standardTriangleCell
  have h₀ : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h₁ : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hgraph : Coordinate.re.graph K.upperFun '' Icc 0 1 ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    apply hU
    rw [mem_standardTriangle, Coordinate.graph_re_apply]
    rw [GraphCell.standardTriangleCell_upperFun ht]
    exact ⟨ht.1, sub_nonneg.mpr ht.2, by simp⟩
  have hγ := BoundaryChain.graphArc_graphPath .re K.continuous_upperFun.continuousOn
    (by simpa [K] using K.exists_countable_differentiableAt_upperFun) h₀ h₁
  have hrev := BoundaryChain.NullChain.reverse (.graph hγ hgraph)
  have he : BoundaryChain.ofPath
      (BoundaryChain.graphPath .re K.upperFun 0 1 K.continuous_upperFun.continuousOn) =
      BoundaryChain.ofPath (Path.segment Complex.I 1) := by
    rw [GraphCell.graphPath_standardTriangleCell_upper]
    apply BoundaryChain.ofPath_congr
    intro t
    apply Complex.ext <;>
      simp [Path.segment_apply, AffineMap.lineMap_apply_module]
  have her : BoundaryChain.ofPath
      (BoundaryChain.graphPath .re K.upperFun 0 1
        K.continuous_upperFun.continuousOn).symm =
      BoundaryChain.ofPath (Path.segment 1 Complex.I) := by
    apply BoundaryChain.ofPath_congr
    intro t
    rw [Path.symm_apply, Function.comp_apply, BoundaryChain.graphPath_apply]
    simp only [AffineMap.lineMap_apply_module, smul_eq_mul, mul_zero, mul_one, zero_add]
    rw [Coordinate.graph_re_apply,
      GraphCell.standardTriangleCell_upperFun (unitInterval.symm t).prop]
    apply Complex.ext <;> simp [Path.segment_apply, AffineMap.lineMap_apply_module]
  rw [he, her] at hrev
  rw [boundary_standardTriangleDivision, GraphCell.boundary_standardTriangleCell_re,
    BoundaryChain.triangle_def]
  convert (BoundaryChain.NullChain.segment (d := .re) (U := U) (p := 1) (q := 1)
    rfl).add hrev.neg using 1
  abel

end Division

end TauCeti.Green
