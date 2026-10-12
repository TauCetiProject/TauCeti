/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.CoordinateSimplex
public import TauCeti.Topology.Algebra.Module.Equiv.Pi
public import TauCeti.Topology.PL.Orthant.HalfSpace
public import TauCeti.Geometry.Manifold.Instances.HalfSpace
public import TauCeti.Geometry.Manifold.PLGroupoid.Basic

/-!
# Half-space PL charts on a solid simplex

The solid coordinate simplex has a chart for each vertex, defined on the complement
of the opposite facet. Affine vertex swaps carry these regions to the region of mass
less than one. Orthant flattening then gives half-space coordinates, including at
corners. Both directions have ambient piecewise-affine extensions, so the vertex
charts define a PL manifold with boundary. These are the standard ball models used
to transport charts to combinatorially triangulated manifolds.

The normal coordinate vanishes exactly on the geometric boundary in each chart.
The construction includes the segment, with no tangential coordinates.

Reference: C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear
Topology*, Springer (1972), Chapters 1–2 (polyhedral local models). The construction
uses `coordinateSimplexVertexSwap` and `orthantFlattening`.
-/

public section

noncomputable section

open Set Topology
open scoped Manifold

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The ambient PL coordinates at a vertex of a solid simplex: swap that vertex with
the origin, split off a distinguished coordinate, and flatten the solid orthant. -/
def coordinateSimplexHalfSpaceMap (v : Option (Option ι)) :
    (Option ι → ℝ) ≃ₜ ((ι → ℝ) × ℝ) :=
  (v.elim (Homeomorph.refl _) coordinateSimplexVertexSwapHomeomorph).trans
    (((ContinuousLinearEquiv.piOptionEquivProd (M := fun _ : Option ι => ℝ) ℝ).trans
      (ContinuousLinearEquiv.prodComm ℝ ℝ (ι → ℝ))).toHomeomorph.trans orthantFlattening)

/-- In the origin chart, split the coordinates and flatten the orthant. -/
@[simp] theorem coordinateSimplexHalfSpaceMap_none (x : Option ι → ℝ) :
    coordinateSimplexHalfSpaceMap none x =
      orthantFlattening ((fun i => x (some i)), x none) := by
  simp [coordinateSimplexHalfSpaceMap]

/-- The remaining vertex maps first exchange their vertex with the origin. -/
@[simp] theorem coordinateSimplexHalfSpaceMap_some (j : Option ι) (x : Option ι → ℝ) :
    coordinateSimplexHalfSpaceMap (some j) x =
      coordinateSimplexHalfSpaceMap none (coordinateSimplexVertexSwap j x) := by
  simp [coordinateSimplexHalfSpaceMap]

/-- The inverse origin coordinates undo orthant flattening and reassemble the coordinates. -/
@[simp] theorem coordinateSimplexHalfSpaceMap_symm_none (q : (ι → ℝ) × ℝ) :
    (coordinateSimplexHalfSpaceMap (ι := ι) none).symm q =
      Option.elim' (orthantFlattening.symm q).2 (orthantFlattening.symm q).1 := by
  funext i
  cases i <;> simp [coordinateSimplexHalfSpaceMap]

/-- The other inverse coordinate maps exchange the origin with their indexing vertex. -/
@[simp] theorem coordinateSimplexHalfSpaceMap_symm_some (j : Option ι) (q : (ι → ℝ) × ℝ) :
    (coordinateSimplexHalfSpaceMap (some j)).symm q =
      coordinateSimplexVertexSwap j ((coordinateSimplexHalfSpaceMap none).symm q) := by
  simp [coordinateSimplexHalfSpaceMap]

private theorem halfSpaceMap_apply (v : Option (Option ι)) (x : Option ι → ℝ) :
    coordinateSimplexHalfSpaceMap v x = orthantFlattening
      ((fun i => coordinateSimplexChartSwap v x (some i)),
        coordinateSimplexChartSwap v x none) := by
  cases v <;> simp

private theorem halfSpaceMap_symm_apply (v : Option (Option ι)) (q : (ι → ℝ) × ℝ) :
    (coordinateSimplexHalfSpaceMap v).symm q =
      coordinateSimplexChartSwap v
        (Option.elim' (orthantFlattening.symm q).2 (orthantFlattening.symm q).1) := by
  cases v <;> simp

/-- The simplex half-space coordinate map has a finite affine decomposition globally. -/
theorem isPiecewiseAffineOn_coordinateSimplexHalfSpaceMap (v : Option (Option ι)) :
    IsPiecewiseAffineOn (coordinateSimplexHalfSpaceMap v) univ := by
  let e := (ContinuousLinearEquiv.piOptionEquivProd (M := fun _ : Option ι => ℝ) ℝ).trans
    (ContinuousLinearEquiv.prodComm ℝ ℝ (ι → ℝ))
  exact (isPiecewiseAffineOn_orthantFlattening.comp
    (isPiecewiseAffineOn_continuousAffineMap
      (e.toContinuousLinearMap.toContinuousAffineMap.comp (coordinateSimplexChartSwap v)) univ)
    (mapsTo_univ _ _)).congr (fun x _ => by
      simpa only [e, Function.comp_apply, ContinuousAffineMap.comp_apply,
        ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.piOptionEquivProd_apply,
        ContinuousLinearEquiv.prodComm_apply, Prod.swap_prod_mk] using halfSpaceMap_apply v x)

/-- The inverse coordinate map also has a finite affine decomposition globally. -/
theorem isPiecewiseAffineOn_coordinateSimplexHalfSpaceMap_symm (v : Option (Option ι)) :
    IsPiecewiseAffineOn (coordinateSimplexHalfSpaceMap v).symm univ := by
  let e := (ContinuousLinearEquiv.piOptionEquivProd (M := fun _ : Option ι => ℝ) ℝ).trans
    (ContinuousLinearEquiv.prodComm ℝ ℝ (ι → ℝ))
  exact ((isPiecewiseAffineOn_continuousAffineMap
    ((coordinateSimplexChartSwap v).comp e.symm.toContinuousLinearMap.toContinuousAffineMap)
      univ).comp
    isPiecewiseAffineOn_orthantFlattening_symm (mapsTo_univ _ _)).congr (fun q _ => by
      simp only [Function.comp_apply, ContinuousAffineMap.comp_apply,
        ContinuousLinearMap.coe_toContinuousAffineMap, ContinuousLinearEquiv.coe_coe]
      rw [halfSpaceMap_symm_apply]
      congr 1
      funext i
      cases i <;> simp [e])

/-- The vertex-chart source is the simplex with the opposite facet deleted. -/
def coordinateSimplexHalfSpaceChartSource (v : Option (Option ι)) :
    Set (coordinateSimplex (Option ι)) :=
  {x | ∑ i, coordinateSimplexChartSwap v x.1 i < 1}

/-- The origin-vertex source excludes the total-mass-one facet. -/
@[simp] theorem coordinateSimplexHalfSpaceChartSource_none :
    coordinateSimplexHalfSpaceChartSource (ι := ι) none = {x | ∑ i, x.1 i < 1} := by
  ext x
  simp only [coordinateSimplexHalfSpaceChartSource, coordinateSimplexChartSwap_none, mem_ofPred_eq]

/-- A coordinate-vertex source excludes the facet on which its coordinate is zero. -/
@[simp] theorem coordinateSimplexHalfSpaceChartSource_some (j : Option ι) :
    coordinateSimplexHalfSpaceChartSource (some j) = {x | 0 < x.1 j} := by
  ext x
  simp only [coordinateSimplexHalfSpaceChartSource, coordinateSimplexChartSwap_some,
    sum_coordinateSimplexVertexSwap, mem_ofPred_eq]
  constructor <;> intro h <;> linarith

private theorem halfSpaceMap_nonneg (v : Option (Option ι))
    (x : coordinateSimplex (Option ι)) : 0 ≤ (coordinateSimplexHalfSpaceMap v x.1).2 := by
  rw [halfSpaceMap_apply]
  apply (mem_nonnegOrthant_iff_nonneg_orthantFlattening_snd _).mp
  have h := (mem_coordinateSimplex _ _).mp ((coordinateSimplexChartSwap_mem_iff v x.1).mpr x.2)
  exact ⟨fun i => h.1 (some i), h.1 none⟩

private theorem inverse_mem_simplex (v : Option (Option ι))
    (q : {q : (ι → ℝ) × ℝ | 0 ≤ q.2})
    (hq : ∑ i, (coordinateSimplexHalfSpaceMap none).symm q.1 i < 1) :
    (coordinateSimplexHalfSpaceMap v).symm q.1 ∈ coordinateSimplex (Option ι) := by
  rw [halfSpaceMap_symm_apply, coordinateSimplexChartSwap_mem_iff]
  have hn := (mem_nonnegOrthant_iff_nonneg_orthantFlattening_snd
    (orthantFlattening.symm q.1)).mpr (by rw [Homeomorph.apply_symm_apply]; exact q.2)
  rw [mem_coordinateSimplex]
  rw [coordinateSimplexHalfSpaceMap_symm_none] at hq
  refine ⟨?_, hq.le⟩
  intro i
  cases i with
  | none => exact hn.2
  | some i => exact hn.1 i

private theorem source_to_target (v : Option (Option ι))
    (x : coordinateSimplex (Option ι)) (hx : x ∈ coordinateSimplexHalfSpaceChartSource v) :
    ∑ i, (coordinateSimplexHalfSpaceMap none).symm (coordinateSimplexHalfSpaceMap v x.1) i < 1 := by
  have he : Option.elim' (coordinateSimplexChartSwap v x.1 none)
      (fun i => coordinateSimplexChartSwap v x.1 (some i)) = coordinateSimplexChartSwap v x.1 :=
    Option.elim'_none_some _
  simpa only [coordinateSimplexHalfSpaceChartSource, mem_ofPred_eq, halfSpaceMap_apply,
    halfSpaceMap_symm_apply, coordinateSimplexChartSwap_none,
    Homeomorph.symm_apply_apply, he] using hx

/-- The half-space chart at a simplex vertex. Its common target consists of the points
whose inverse origin coordinates have total mass less than one. -/
def coordinateSimplexHalfSpaceChart (v : Option (Option ι)) :
    OpenPartialHomeomorph (coordinateSimplex (Option ι)) {q : (ι → ℝ) × ℝ | 0 ≤ q.2} where
  toFun x := ⟨coordinateSimplexHalfSpaceMap v x.1, halfSpaceMap_nonneg v x⟩
  invFun q := if hq : ∑ i, (coordinateSimplexHalfSpaceMap none).symm q.1 i < 1 then
    ⟨(coordinateSimplexHalfSpaceMap v).symm q.1, inverse_mem_simplex v q hq⟩
    else ⟨0, by simp⟩
  source := coordinateSimplexHalfSpaceChartSource v
  target := {q | ∑ i, (coordinateSimplexHalfSpaceMap none).symm q.1 i < 1}
  map_source' := source_to_target v
  map_target' q hq := by
    simp only [mem_ofPred_eq] at hq
    rw [dite_eq_left hq]
    simp only [coordinateSimplexHalfSpaceChartSource, mem_ofPred_eq,
      halfSpaceMap_symm_apply, coordinateSimplexChartSwap_involutive]
    simpa only [halfSpaceMap_symm_apply, coordinateSimplexChartSwap_none] using hq
  left_inv' x hx := by
    simp only [dite_eq_left (source_to_target v x hx), Homeomorph.symm_apply_apply]
  right_inv' q hq := by
    simp only [mem_ofPred_eq] at hq
    rw [dite_eq_left hq]
    exact Subtype.ext ((coordinateSimplexHalfSpaceMap v).apply_symm_apply q.1)
  open_source := isOpen_lt
    (continuous_finsetSum _ fun i _ => (continuous_apply i).comp
      ((coordinateSimplexChartSwap v).continuous.comp continuous_subtype_val)) continuous_const
  open_target := isOpen_lt
    (continuous_finsetSum _ fun i _ => (continuous_apply i).comp
      ((coordinateSimplexHalfSpaceMap none).symm.continuous.comp continuous_subtype_val))
    continuous_const
  continuousOn_toFun :=
    ((coordinateSimplexHalfSpaceMap v).continuous.comp continuous_subtype_val).subtype_mk _
      |>.continuousOn
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine ((coordinateSimplexHalfSpaceMap v).symm.continuous.comp continuous_subtype_val)
      |>.continuousOn.congr ?_
    intro q hq
    simp only [Function.comp_apply]
    have hq' : ∑ i, (coordinateSimplexHalfSpaceMap none).symm q.1 i < 1 := hq
    rw [dite_eq_left hq']

/-- The chart has the specified vertex region as its source. -/
@[simp] theorem coordinateSimplexHalfSpaceChart_source (v : Option (Option ι)) :
    (coordinateSimplexHalfSpaceChart v).source = coordinateSimplexHalfSpaceChartSource v := (rfl)

/-- All vertex charts share the same target: the half-space points whose inverse origin
coordinates have total mass less than one. -/
@[simp] theorem coordinateSimplexHalfSpaceChart_target (v : Option (Option ι)) :
    (coordinateSimplexHalfSpaceChart v).target =
      {q | ∑ i, (coordinateSimplexHalfSpaceMap none).symm q.1 i < 1} := (rfl)

/-- The chart is the restriction of its ambient coordinate map. -/
@[simp] theorem coe_coordinateSimplexHalfSpaceChart_apply (v : Option (Option ι))
    (x : coordinateSimplex (Option ι)) :
    (coordinateSimplexHalfSpaceChart v x).1 = coordinateSimplexHalfSpaceMap v x.1 := (rfl)

/-- On the target, the inverse chart agrees with its ambient PL inverse formula. -/
theorem coe_coordinateSimplexHalfSpaceChart_symm_apply (v : Option (Option ι))
    {q : {q : (ι → ℝ) × ℝ | 0 ≤ q.2}}
    (hq : q ∈ (coordinateSimplexHalfSpaceChart v).target) :
    ((coordinateSimplexHalfSpaceChart v).symm q).1 =
      (coordinateSimplexHalfSpaceMap v).symm q.1 := by
  simp only [coordinateSimplexHalfSpaceChart_target, mem_ofPred_eq] at hq
  simp only [coordinateSimplexHalfSpaceChart, ← OpenPartialHomeomorph.invFun_eq_coe,
    dite_eq_left hq]

/-- The complements of the opposite facets cover the solid simplex. -/
theorem exists_mem_coordinateSimplexHalfSpaceChartSource
    (x : coordinateSimplex (Option ι)) :
    ∃ v, x ∈ coordinateSimplexHalfSpaceChartSource v := by
  exact (sum_lt_one_or_exists_pos_of_mem_coordinateSimplex _ x.2).elim
    (fun h => ⟨none, by simpa using h⟩) (fun ⟨j, h⟩ => ⟨some j, by simpa using h⟩)

/-- In a vertex chart the geometric simplex boundary is exactly height zero. -/
theorem mem_frontier_coordinateSimplex_iff_halfSpaceChart_snd_eq_zero
    (v : Option (Option ι)) (x : coordinateSimplex (Option ι))
    (hx : x ∈ coordinateSimplexHalfSpaceChartSource v) :
    x.1 ∈ frontier (coordinateSimplex (Option ι)) ↔
      (coordinateSimplexHalfSpaceChart v x).1.2 = 0 := by
  have hsum : ∑ i, coordinateSimplexChartSwap v x.1 i < 1 := hx
  have hmem := (mem_coordinateSimplex _ _).mp ((coordinateSimplexChartSwap_mem_iff v x.1).mpr x.2)
  rw [← coordinateSimplexChartSwap_mem_frontier_iff v x.1, mem_frontier_coordinateSimplex,
    coe_coordinateSimplexHalfSpaceChart_apply,
    halfSpaceMap_apply,
    ← mem_frontier_nonnegOrthant_iff_orthantFlattening_snd_eq_zero,
    mem_frontier_nonnegOrthant_iff]
  simp only [hmem, hsum.ne, or_false, implies_true, true_and]
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | none => exact Or.inl hi
    | some i => exact Or.inr ⟨i, hi⟩
  · rintro (hi | ⟨i, hi⟩)
    · exact ⟨none, hi⟩
    · exact ⟨some i, hi⟩

/-- The simplex vertex charts, with a chart chosen from the cover at each point. -/
@[instance_reducible] def coordinateSimplexHalfSpaceChartedSpace :
    ChartedSpace {q : (ι → ℝ) × ℝ | 0 ≤ q.2} (coordinateSimplex (Option ι)) where
  atlas := range coordinateSimplexHalfSpaceChart
  chartAt x := coordinateSimplexHalfSpaceChart
    (Classical.choose (exists_mem_coordinateSimplexHalfSpaceChartSource x))
  mem_chart_source x := Classical.choose_spec (exists_mem_coordinateSimplexHalfSpaceChartSource x)
  chart_mem_atlas _ := mem_range_self _

/-- The atlas consists exactly of the vertex charts. -/
@[simp] theorem coordinateSimplexHalfSpaceChartedSpace_atlas :
    @atlas {q : (ι → ℝ) × ℝ | 0 ≤ q.2} _ (coordinateSimplex (Option ι)) _
      coordinateSimplexHalfSpaceChartedSpace = range coordinateSimplexHalfSpaceChart := (rfl)

/-- Coordinate changes are piecewise affine when read in the product half-space model. -/
theorem isPiecewiseAffineOn_coordinateSimplexHalfSpaceChart_transition
    (v w : Option (Option ι)) :
    let I := modelWithCornersHalfSpace (ι → ℝ)
    let e := (coordinateSimplexHalfSpaceChart v).symm.trans (coordinateSimplexHalfSpaceChart w)
    IsPiecewiseAffineOn (I ∘ e ∘ I.symm) (I.symm ⁻¹' e.source ∩ range I) := by
  let I := modelWithCornersHalfSpace (ι → ℝ)
  let e := (coordinateSimplexHalfSpaceChart v).symm.trans (coordinateSimplexHalfSpaceChart w)
  refine ((isPiecewiseAffineOn_coordinateSimplexHalfSpaceMap w).comp
    (isPiecewiseAffineOn_coordinateSimplexHalfSpaceMap_symm v)
    (mapsTo_univ _ _)).mono (subset_univ _) |>.congr ?_
  intro y hy
  have hnonneg : 0 ≤ y.2 := by simpa [I] using hy.2
  have hsource := hy.1
  rw [OpenPartialHomeomorph.trans_source] at hsource
  simp only [Function.comp_apply, modelWithCornersHalfSpace_apply,
    OpenPartialHomeomorph.trans_apply, coe_coordinateSimplexHalfSpaceChart_apply]
  rw [coe_coordinateSimplexHalfSpaceChart_symm_apply v hsource.1,
    coe_modelWithCornersHalfSpace_symm_apply _ hnonneg]

/-- The solid simplex's vertex charts define a PL manifold with boundary. -/
theorem coordinateSimplexHalfSpace_hasGroupoid :
    letI := coordinateSimplexHalfSpaceChartedSpace (ι := ι)
    HasGroupoid (coordinateSimplex (Option ι))
      (PLGroupoid (modelWithCornersHalfSpace (ι → ℝ))) := by
  let := coordinateSimplexHalfSpaceChartedSpace (ι := ι)
  constructor
  rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
  rw [mem_PLGroupoid_iff]
  constructor
  · exact (isPiecewiseAffineOn_coordinateSimplexHalfSpaceChart_transition v w).isPLOn
  · simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm, ← OpenPartialHomeomorph.symm_source] using
      (isPiecewiseAffineOn_coordinateSimplexHalfSpaceChart_transition w v).isPLOn

end TauCeti
