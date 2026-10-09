/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Simplex.Basic
public import TauCeti.Geometry.Manifold.PLGroupoid.Basic

/-!
# A PL atlas on the boundary of a simplex

The coordinate simplex boundary has one chart for each vertex: its source is the complement
of the opposite facet. The origin chart uses coordinate differences and minimum subtraction;
the other charts transport it by the affine involution exchanging a vertex with the origin.
The sources cover the boundary and every transition is piecewise affine. This gives the
standard polyhedral sphere a PL structure, including the two-point zero-dimensional sphere.
These standard sphere charts are local models for triangulated manifolds.

Reference: C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology*,
Springer (1972), Chapters 1–2. The origin coordinates are those of
`coordinateSimplexBoundaryVertexHomeomorph`.
-/

public section

noncomputable section

open Set Topology
open scoped Manifold

namespace TauCeti

variable {ι : Type*} [Fintype ι]

private def chartSwap (v : Option (Option ι)) : (Option ι → ℝ) →ᴬ[ℝ] (Option ι → ℝ) :=
  match v with
  | none => ContinuousAffineMap.id ℝ _
  | some j => coordinateSimplexVertexSwap j

private theorem chartSwap_involutive (v : Option (Option ι)) (x : Option ι → ℝ) :
    chartSwap v (chartSwap v x) = x := by
  cases v <;> simp [chartSwap]

private theorem chartSwap_mem_frontier_iff (v : Option (Option ι)) (x : Option ι → ℝ) :
    chartSwap v x ∈ frontier (coordinateSimplex (Option ι)) ↔
      x ∈ frontier (coordinateSimplex (Option ι)) := by
  cases v with
  | none => rfl
  | some j => exact coordinateSimplexVertexSwap_mem_frontier_iff j x

/-- Ambient affine coordinates in the simplex boundary chart at vertex `v`. The index `none`
means the origin; `some j` means the coordinate vertex `j`. -/
def coordinateSimplexBoundaryChartProjection (v : Option (Option ι)) :
    (Option ι → ℝ) →ᴬ[ℝ] (ι → ℝ) :=
  (coordinateSimplexBoundaryProjection (ι := ι)).toContinuousAffineMap.comp (chartSwap v)

/-- At the origin vertex, the chart uses the coordinate-difference projection. -/
@[simp] theorem coordinateSimplexBoundaryChartProjection_none (x : Option ι → ℝ) :
    coordinateSimplexBoundaryChartProjection none x = coordinateSimplexBoundaryProjection x :=
  (rfl)

/-- At a coordinate vertex, first swap that vertex with the origin. -/
@[simp] theorem coordinateSimplexBoundaryChartProjection_some (j : Option ι)
    (x : Option ι → ℝ) :
    coordinateSimplexBoundaryChartProjection (some j) x =
      coordinateSimplexBoundaryProjection (coordinateSimplexVertexSwap j x) := (rfl)

/-- Ambient inverse coordinates in the simplex boundary chart at vertex `v`. -/
def coordinateSimplexBoundaryChartLift (v : Option (Option ι)) (y : ι → ℝ) : Option ι → ℝ :=
  chartSwap v (coordinateSimplexBoundaryLift y)

/-- The origin chart inverse is minimum subtraction. -/
@[simp] theorem coordinateSimplexBoundaryChartLift_none (y : ι → ℝ) :
    coordinateSimplexBoundaryChartLift none y = coordinateSimplexBoundaryLift y := (rfl)

/-- The other chart inverses swap the lifted point's origin vertex with the chosen vertex. -/
@[simp] theorem coordinateSimplexBoundaryChartLift_some (j : Option ι) (y : ι → ℝ) :
    coordinateSimplexBoundaryChartLift (some j) y =
      coordinateSimplexVertexSwap j (coordinateSimplexBoundaryLift y) := (rfl)

/-- The inverse coordinate formulas are piecewise affine on the entire model space. -/
theorem isPiecewiseAffineOn_coordinateSimplexBoundaryChartLift (v : Option (Option ι)) :
    IsPiecewiseAffineOn (coordinateSimplexBoundaryChartLift v) univ :=
  (isPiecewiseAffineOn_continuousAffineMap (chartSwap v) univ).comp
    isPiecewiseAffineOn_coordinateSimplexBoundaryLift (mapsTo_univ _ _)

/-- The ambient projection is a left inverse to the lifted chart coordinates. -/
@[simp] theorem coordinateSimplexBoundaryChartProjection_lift (v : Option (Option ι))
    (y : ι → ℝ) :
    coordinateSimplexBoundaryChartProjection v (coordinateSimplexBoundaryChartLift v y) = y := by
  simp only [coordinateSimplexBoundaryChartProjection, coordinateSimplexBoundaryChartLift,
    ContinuousAffineMap.comp_apply, ContinuousLinearMap.coe_toContinuousAffineMap,
    chartSwap_involutive, coordinateSimplexBoundaryProjection_lift]

/-- The chart source is the boundary with the facet opposite the chosen vertex deleted. -/
def coordinateSimplexBoundaryChartSource (v : Option (Option ι)) :
    Set (frontier (coordinateSimplex (Option ι))) :=
  match v with
  | none => {x | ∑ i, x.1 i < 1}
  | some j => {x | 0 < x.1 j}

/-- At the origin vertex, the deleted facet is the total-mass-one facet. -/
@[simp] theorem coordinateSimplexBoundaryChartSource_none :
    coordinateSimplexBoundaryChartSource (ι := ι) none = {x | ∑ i, x.1 i < 1} := (rfl)

/-- At a coordinate vertex, the deleted facet is where that coordinate vanishes. -/
@[simp] theorem coordinateSimplexBoundaryChartSource_some (j : Option ι) :
    coordinateSimplexBoundaryChartSource (some j) = {x | 0 < x.1 j} := (rfl)

private theorem mem_chartSource_iff (v : Option (Option ι))
    (x : frontier (coordinateSimplex (Option ι))) :
    x ∈ coordinateSimplexBoundaryChartSource v ↔ ∑ i, chartSwap v x.1 i < 1 := by
  cases v with
  | none => rfl
  | some j => simp only [coordinateSimplexBoundaryChartSource, mem_ofPred_eq, chartSwap,
      sum_coordinateSimplexVertexSwap]; constructor <;> intro h <;> linarith

/-- Projecting and lifting recover a boundary point in the chosen chart source. -/
theorem coordinateSimplexBoundaryChartLift_projection (v : Option (Option ι))
    (x : frontier (coordinateSimplex (Option ι)))
    (hx : x ∈ coordinateSimplexBoundaryChartSource v) :
    coordinateSimplexBoundaryChartLift v
      (coordinateSimplexBoundaryChartProjection v x.1) = x.1 := by
  simp only [coordinateSimplexBoundaryChartLift, coordinateSimplexBoundaryChartProjection,
    ContinuousAffineMap.comp_apply, ContinuousLinearMap.coe_toContinuousAffineMap]
  rw [coordinateSimplexBoundaryLift_projection ((chartSwap_mem_frontier_iff v x.1).2 x.2)
    ((mem_chartSource_iff v x).1 hx), chartSwap_involutive]

/-- Chart lifts with mass less than one lie on the geometric simplex boundary. -/
theorem coordinateSimplexBoundaryChartLift_mem_frontier (v : Option (Option ι)) {y : ι → ℝ}
    (hy : ∑ i, coordinateSimplexBoundaryLift y i < 1) :
    coordinateSimplexBoundaryChartLift v y ∈ frontier (coordinateSimplex (Option ι)) :=
  (chartSwap_mem_frontier_iff v _).2 (coordinateSimplexBoundaryLift_mem_frontier hy)

private theorem isOpen_chartSource (v : Option (Option ι)) :
    IsOpen (coordinateSimplexBoundaryChartSource v) := by
  cases v with
  | none => exact isOpen_coordinateSimplexBoundaryChartSource
  | some j =>
    exact isOpen_lt continuous_const ((continuous_apply j).comp continuous_subtype_val)

/-- The complements of the opposite facets cover the simplex boundary. -/
theorem exists_mem_coordinateSimplexBoundaryChartSource
    (x : frontier (coordinateSimplex (Option ι))) :
    ∃ v, x ∈ coordinateSimplexBoundaryChartSource v := by
  by_cases hx : ∑ i, x.1 i < 1
  · exact ⟨none, hx⟩
  · have hp : 0 < ∑ i, x.1 i := by linarith
    obtain ⟨j, -, hj⟩ := Finset.sum_pos_iff_of_nonneg
      (fun i _ => ((mem_frontier_coordinateSimplex _ _).1 x.2).1.1 i) |>.1 hp
    exact ⟨some j, hj⟩

private theorem chartProjection_mem_target (v : Option (Option ι))
    (x : frontier (coordinateSimplex (Option ι)))
    (hx : x ∈ coordinateSimplexBoundaryChartSource v) :
    ∑ i, coordinateSimplexBoundaryLift (coordinateSimplexBoundaryChartProjection v x.1) i < 1 := by
  have h := (mem_chartSource_iff v x).1 hx
  simpa only [coordinateSimplexBoundaryChartProjection, ContinuousAffineMap.comp_apply,
    ContinuousLinearMap.coe_toContinuousAffineMap,
    coordinateSimplexBoundaryLift_projection ((chartSwap_mem_frontier_iff v x.1).2 x.2) h]
    using h

private theorem zero_mem_frontier : (0 : Option ι → ℝ) ∈
    frontier (coordinateSimplex (Option ι)) := by
  simp only [mem_frontier_coordinateSimplex, Pi.zero_apply, Finset.sum_const_zero]
  exact ⟨⟨fun _ => le_rfl, zero_le_one⟩, Or.inl ⟨none, trivial⟩⟩

/-- The PL chart at a simplex vertex, with source the complement of its opposite facet.
Its target is the common open set whose minimum-subtraction lift has mass less than one. -/
def coordinateSimplexBoundaryChart (v : Option (Option ι)) :
    OpenPartialHomeomorph (frontier (coordinateSimplex (Option ι))) (ι → ℝ) where
  toFun x := coordinateSimplexBoundaryChartProjection v x.1
  invFun y := if hy : ∑ i, coordinateSimplexBoundaryLift y i < 1 then
    ⟨coordinateSimplexBoundaryChartLift v y, coordinateSimplexBoundaryChartLift_mem_frontier v hy⟩
    else ⟨0, zero_mem_frontier⟩
  source := coordinateSimplexBoundaryChartSource v
  target := {y | ∑ i, coordinateSimplexBoundaryLift y i < 1}
  map_source' x hx := chartProjection_mem_target v x hx
  map_target' y hy := by
    simp only [mem_ofPred_eq] at hy
    simp only [dite_eq_left hy]
    rw [mem_chartSource_iff]
    simpa only [coordinateSimplexBoundaryChartLift, chartSwap_involutive] using hy
  left_inv' x hx := by
    simp only [dite_eq_left (chartProjection_mem_target v x hx)]
    exact Subtype.ext (coordinateSimplexBoundaryChartLift_projection v x hx)
  right_inv' y hy := by
    simp only [mem_ofPred_eq] at hy
    simp only [dite_eq_left hy, coordinateSimplexBoundaryChartProjection_lift]
  open_source := isOpen_chartSource v
  open_target := isOpen_coordinateSimplexBoundaryChartTarget
  continuousOn_toFun := ((coordinateSimplexBoundaryChartProjection v).continuous.comp
    continuous_subtype_val).continuousOn
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine (isPiecewiseAffineOn_coordinateSimplexBoundaryChartLift v).continuousOn.mono
      (subset_univ _) |>.congr ?_
    intro y hy
    simp only [mem_ofPred_eq] at hy
    simp only [Function.comp_apply, dite_eq_left hy]

/-- The chart source is the specified complement of an opposite facet. -/
@[simp] theorem coordinateSimplexBoundaryChart_source (v : Option (Option ι)) :
    (coordinateSimplexBoundaryChart v).source = coordinateSimplexBoundaryChartSource v := (rfl)

/-- All simplex boundary charts have the same open model target. -/
@[simp] theorem coordinateSimplexBoundaryChart_target (v : Option (Option ι)) :
    (coordinateSimplexBoundaryChart v).target =
      {y | ∑ i, coordinateSimplexBoundaryLift y i < 1} := (rfl)

/-- The chart reads the ambient affine projection. -/
@[simp] theorem coordinateSimplexBoundaryChart_apply (v : Option (Option ι))
    (x : frontier (coordinateSimplex (Option ι))) :
    coordinateSimplexBoundaryChart v x = coordinateSimplexBoundaryChartProjection v x.1 := (rfl)

/-- On the chart target, its inverse has the ambient piecewise-affine lift formula. -/
theorem coe_coordinateSimplexBoundaryChart_symm_apply (v : Option (Option ι)) {y : ι → ℝ}
    (hy : ∑ i, coordinateSimplexBoundaryLift y i < 1) :
    ((coordinateSimplexBoundaryChart v).symm y).1 = coordinateSimplexBoundaryChartLift v y := by
  simp only [coordinateSimplexBoundaryChart, ← OpenPartialHomeomorph.invFun_eq_coe, dite_eq_left hy]

/-- The origin of each model chart lifts to its indexing simplex vertex. -/
@[simp] theorem coe_coordinateSimplexBoundaryChart_symm_zero [DecidableEq ι]
    (v : Option (Option ι)) :
    ((coordinateSimplexBoundaryChart v).symm 0).1 =
      match v with
      | none => 0
      | some j => Pi.single j 1 := by
  classical
  rw [coe_coordinateSimplexBoundaryChart_symm_apply v (by simp)]
  cases v with
  | none => simp
  | some j =>
    ext i
    simp [coordinateSimplexVertexSwap_apply, Pi.single_apply]

/-- Coordinate changes between simplex boundary charts are piecewise affine on their domains. -/
theorem isPiecewiseAffineOn_coordinateSimplexBoundaryChart_transition (v w : Option (Option ι)) :
    IsPiecewiseAffineOn
      ((coordinateSimplexBoundaryChart v).symm.trans (coordinateSimplexBoundaryChart w))
      ((coordinateSimplexBoundaryChart v).symm.trans
        (coordinateSimplexBoundaryChart w)).source := by
  refine ((isPiecewiseAffineOn_continuousAffineMap
    (coordinateSimplexBoundaryChartProjection w) univ).comp
    (isPiecewiseAffineOn_coordinateSimplexBoundaryChartLift v) (mapsTo_univ _ _)).mono
    (subset_univ _) |>.congr ?_
  intro y hy
  rw [OpenPartialHomeomorph.trans_source] at hy
  simp only [OpenPartialHomeomorph.trans_apply, coordinateSimplexBoundaryChart_apply,
    Function.comp_apply]
  rw [coe_coordinateSimplexBoundaryChart_symm_apply v hy.1]

/-- The finite vertex-chart atlas on the geometric boundary of a coordinate simplex. -/
@[instance_reducible] def coordinateSimplexBoundaryChartedSpace :
    ChartedSpace (ι → ℝ) (frontier (coordinateSimplex (Option ι))) where
  atlas := range coordinateSimplexBoundaryChart
  chartAt x := coordinateSimplexBoundaryChart
    (Classical.choose (exists_mem_coordinateSimplexBoundaryChartSource x))
  mem_chart_source x := Classical.choose_spec (exists_mem_coordinateSimplexBoundaryChartSource x)
  chart_mem_atlas _ := mem_range_self _

/-- The atlas consists exactly of the vertex charts. -/
@[simp] theorem coordinateSimplexBoundaryChartedSpace_atlas :
    @atlas (ι → ℝ) _ (frontier (coordinateSimplex (Option ι))) _
      coordinateSimplexBoundaryChartedSpace = range coordinateSimplexBoundaryChart := (rfl)

/-- The simplex boundary's vertex-chart atlas defines a PL manifold structure. -/
theorem coordinateSimplexBoundary_hasGroupoid :
    letI := coordinateSimplexBoundaryChartedSpace (ι := ι)
    HasGroupoid (frontier (coordinateSimplex (Option ι))) (PLGroupoid 𝓘(ℝ, ι → ℝ)) := by
  let := coordinateSimplexBoundaryChartedSpace (ι := ι)
  constructor
  rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
  rw [mem_PLGroupoid_iff]
  constructor
  · simpa only [mfld_simps] using
      (isPiecewiseAffineOn_coordinateSimplexBoundaryChart_transition v w).isPLOn
  · simpa only [mfld_simps, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
      using (isPiecewiseAffineOn_coordinateSimplexBoundaryChart_transition w v).isPLOn

end TauCeti
