/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Topology.Sets.Opens

/-!
# Lipschitz domains

This file defines Lipschitz boundary charts and Lipschitz domains in a finite-dimensional real
inner product space. A chart at `x ∈ frontier Ω` chooses a unit inward normal `ν` and writes the
domain, inside a product cylinder centred at `x`, as the region above the graph of a Lipschitz
function on the tangential chart ball in `span ℝ {ν}ᗮ`.

The normal and tangential coordinates of `y` are respectively
`⟪ν, y - x⟫` and the orthogonal projection of `y - x` onto `span ℝ {ν}ᗮ`. Thus this
coordinate-free definition packages the usual rigid-coordinate description intrinsically. The
chart records both cylinder radii. Smaller positive radii give another chart, allowing later trace
and extension arguments to shrink charts without changing their coordinates.

Every open half-space is a Lipschitz domain, supplying the basic nondegenerate example.

## Main declarations

* `TauCeti.LipschitzBoundaryChart`: local graph data at a frontier point.
* `TauCeti.LipschitzBoundaryChart.restrict`: restriction to a smaller product cylinder.
* `TauCeti.IsLipschitzDomain`: every frontier point has a Lipschitz boundary chart.
* `TauCeti.isLipschitzDomain_innerHalfSpace`: open half-spaces are Lipschitz domains.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5.
* W. McLean, *Strongly Elliptic Systems and Boundary Integral Equations*, §3.1.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set TopologicalSpace
open scoped NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The signed normal coordinate of `y`, in coordinates centred at `x` with normal `ν`. -/
def boundaryNormalCoordinate (ν x y : F) : ℝ :=
  inner ℝ ν (y - x)

omit [FiniteDimensional ℝ F] in
@[simp]
theorem boundaryNormalCoordinate_apply (ν x y : F) :
    boundaryNormalCoordinate ν x y = inner ℝ ν (y - x) := by
  rw [boundaryNormalCoordinate]

omit [FiniteDimensional ℝ F] in
theorem boundaryNormalCoordinate_self (ν x : F) : boundaryNormalCoordinate ν x x = 0 := by
  simp

omit [FiniteDimensional ℝ F] in
/-- The normal-coordinate function is continuous. -/
theorem continuous_boundaryNormalCoordinate (ν x : F) :
    Continuous (boundaryNormalCoordinate ν x) := by
  rw [show boundaryNormalCoordinate ν x = (fun y => inner ℝ ν (y - x)) from
    funext (boundaryNormalCoordinate_apply ν x)]
  exact continuous_const.inner (continuous_id.sub continuous_const)

/-- The tangential coordinate of `y`, in coordinates centred at `x` with normal `ν`. -/
def boundaryTangentCoordinate (ν x y : F) : (ℝ ∙ ν)ᗮ :=
  ((ℝ ∙ ν)ᗮ).orthogonalProjectionOnto (y - x)

omit [FiniteDimensional ℝ F] in
@[simp]
theorem coe_boundaryTangentCoordinate (ν x y : F) :
    (boundaryTangentCoordinate ν x y : F) = ((ℝ ∙ ν)ᗮ).starProjection (y - x) :=
  by
    rw [boundaryTangentCoordinate]
    exact Submodule.coe_orthogonalProjectionOnto_apply _ _

omit [FiniteDimensional ℝ F] in
@[simp]
theorem boundaryTangentCoordinate_self (ν x : F) : boundaryTangentCoordinate ν x x = 0 := by
  simp [boundaryTangentCoordinate]

omit [FiniteDimensional ℝ F] in
/-- The tangential-coordinate function is continuous. -/
theorem continuous_boundaryTangentCoordinate (ν x : F) :
    Continuous (boundaryTangentCoordinate ν x) := by
  rw [show boundaryTangentCoordinate ν x =
      (fun y => ((ℝ ∙ ν)ᗮ).orthogonalProjectionOnto (y - x)) from
    funext fun y => by rw [boundaryTangentCoordinate]]
  exact ((ℝ ∙ ν)ᗮ).orthogonalProjectionOnto.continuous.comp
    (continuous_id.sub continuous_const)

omit [FiniteDimensional ℝ F] in
/-- A point is recovered by adding its normal and tangential coordinates to the chart centre. -/
theorem boundary_coordinate_reconstruction (ν x y : F) (hν : ‖ν‖ = 1) :
    y = x + boundaryNormalCoordinate ν x y • ν + (boundaryTangentCoordinate ν x y : F) := by
  simp only [boundaryNormalCoordinate_apply, coe_boundaryTangentCoordinate,
    Submodule.starProjection_orthogonal, sub_apply, ContinuousLinearMap.id_apply,
    Submodule.starProjection_unit_singleton ℝ hν]
  abel

/-- The open product cylinder with normal radius `r` and tangential radius `ρ`, in coordinates
centred at `x` with normal `ν`. -/
def boundaryCylinder (ν x : F) (r ρ : ℝ) : Set F :=
  {y | |boundaryNormalCoordinate ν x y| < r ∧ ‖boundaryTangentCoordinate ν x y‖ < ρ}

omit [FiniteDimensional ℝ F] in
@[simp]
theorem mem_boundaryCylinder {ν x y : F} {r ρ : ℝ} :
    y ∈ boundaryCylinder ν x r ρ ↔
      |boundaryNormalCoordinate ν x y| < r ∧ ‖boundaryTangentCoordinate ν x y‖ < ρ :=
  Iff.rfl

omit [FiniteDimensional ℝ F] in
/-- A product cylinder is open. -/
theorem isOpen_boundaryCylinder (ν x : F) (r ρ : ℝ) : IsOpen (boundaryCylinder ν x r ρ) := by
  exact (isOpen_lt (continuous_boundaryNormalCoordinate ν x).abs continuous_const).inter
    (isOpen_lt (continuous_boundaryTangentCoordinate ν x).norm continuous_const)

omit [FiniteDimensional ℝ F] in
/-- Decreasing either radius decreases the corresponding product cylinder. -/
theorem boundaryCylinder_mono {ν x : F} {r r' ρ ρ' : ℝ} (hr : r' ≤ r) (hρ : ρ' ≤ ρ) :
    boundaryCylinder ν x r' ρ' ⊆ boundaryCylinder ν x r ρ := by
  intro y hy
  exact ⟨hy.1.trans_le hr, hy.2.trans_le hρ⟩

/-- A Lipschitz graph description of an open set near one of its frontier points.

The chosen unit vector points into the domain: locally, membership is the strict inequality that
the height at the tangential coordinate is less than the normal coordinate. -/
@[ext]
structure LipschitzBoundaryChart (Ω : Opens F) (x : F) where
  /-- The centre is a frontier point of the domain. -/
  mem_frontier : x ∈ frontier (Ω : Set F)
  /-- The inward unit normal used by the chart. -/
  normal : F
  /-- The normal has unit length. -/
  norm_normal : ‖normal‖ = 1
  /-- The normal radius of the product cylinder. -/
  normalRadius : ℝ
  /-- The normal radius is positive. -/
  normalRadius_pos : 0 < normalRadius
  /-- The tangential radius of the product cylinder. -/
  tangentRadius : ℝ
  /-- The tangential radius is positive. -/
  tangentRadius_pos : 0 < tangentRadius
  /-- The height function on the tangential chart ball. -/
  height : Metric.ball (0 : (ℝ ∙ normal)ᗮ) tangentRadius → ℝ
  /-- The height function is Lipschitz. -/
  exists_lipschitzWith_height : ∃ K : ℝ≥0, LipschitzWith K height
  /-- The height function passes through the centre of the chart. -/
  height_zero : height ⟨0, by simpa using tangentRadius_pos⟩ = 0
  /-- Inside the product cylinder, the domain is exactly the region above the height function. -/
  mem_iff {y : F} (hy : y ∈ boundaryCylinder normal x normalRadius tangentRadius) :
    y ∈ Ω ↔ height ⟨boundaryTangentCoordinate normal x y, by
      simpa using (mem_boundaryCylinder.mp hy).2⟩ <
      boundaryNormalCoordinate normal x y

namespace LipschitzBoundaryChart

variable {Ω : Opens F} {x : F}

/-- A Lipschitz constant for the height function. -/
def lipschitzConstant (c : LipschitzBoundaryChart Ω x) : ℝ≥0 :=
  c.exists_lipschitzWith_height.choose

omit [FiniteDimensional ℝ F] in
/-- The height function has the chosen Lipschitz constant. -/
theorem lipschitzWith_height (c : LipschitzBoundaryChart Ω x) :
    LipschitzWith c.lipschitzConstant c.height :=
  c.exists_lipschitzWith_height.choose_spec

omit [FiniteDimensional ℝ F] in
/-- The height function of a Lipschitz boundary chart is continuous. -/
theorem continuousOn_height (c : LipschitzBoundaryChart Ω x) :
    ContinuousOn c.height Set.univ :=
  c.lipschitzWith_height.continuous.continuousOn

omit [FiniteDimensional ℝ F] in
/-- The centre of a boundary chart belongs to the chart's product cylinder. -/
theorem mem_boundaryCylinder_center (c : LipschitzBoundaryChart Ω x) :
    x ∈ boundaryCylinder c.normal x c.normalRadius c.tangentRadius := by
  simp [c.normalRadius_pos, c.tangentRadius_pos]

/-- Restrict a Lipschitz boundary chart to smaller positive normal and tangential radii. -/
abbrev restrict (c : LipschitzBoundaryChart Ω x) {r ρ : ℝ}
    (hr : 0 < r) (hrc : r ≤ c.normalRadius)
    (hρ : 0 < ρ) (hρc : ρ ≤ c.tangentRadius) : LipschitzBoundaryChart Ω x where
  mem_frontier := c.mem_frontier
  normal := c.normal
  norm_normal := c.norm_normal
  normalRadius := r
  normalRadius_pos := hr
  tangentRadius := ρ
  tangentRadius_pos := hρ
  height := c.height ∘ Set.inclusion (Metric.ball_subset_ball hρc)
  exists_lipschitzWith_height := by
    refine ⟨c.lipschitzConstant, ?_⟩
    simpa using c.lipschitzWith_height.comp ((LipschitzWith.subtype_val _).subtype_mk _)
  height_zero := c.height_zero
  mem_iff hy := c.mem_iff (boundaryCylinder_mono hrc hρc hy)

omit [FiniteDimensional ℝ F] in
@[simp]
theorem restrict_normal (c : LipschitzBoundaryChart Ω x) {r ρ : ℝ}
    (hr : 0 < r) (hrc : r ≤ c.normalRadius)
    (hρ : 0 < ρ) (hρc : ρ ≤ c.tangentRadius) :
    (c.restrict hr hrc hρ hρc).normal = c.normal :=
  (rfl)

omit [FiniteDimensional ℝ F] in
@[simp]
theorem restrict_height_apply (c : LipschitzBoundaryChart Ω x) {r ρ : ℝ}
    (hr : 0 < r) (hrc : r ≤ c.normalRadius)
    (hρ : 0 < ρ) (hρc : ρ ≤ c.tangentRadius)
    (z : Metric.ball (0 : (ℝ ∙ c.normal)ᗮ) ρ) :
    (c.restrict hr hrc hρ hρc).height z =
      c.height (Set.inclusion (Metric.ball_subset_ball hρc) z) :=
  (rfl)

omit [FiniteDimensional ℝ F] in
@[simp]
theorem restrict_normalRadius (c : LipschitzBoundaryChart Ω x) {r ρ : ℝ}
    (hr : 0 < r) (hrc : r ≤ c.normalRadius)
    (hρ : 0 < ρ) (hρc : ρ ≤ c.tangentRadius) :
    (c.restrict hr hrc hρ hρc).normalRadius = r :=
  (rfl)

omit [FiniteDimensional ℝ F] in
@[simp]
theorem restrict_tangentRadius (c : LipschitzBoundaryChart Ω x) {r ρ : ℝ}
    (hr : 0 < r) (hrc : r ≤ c.normalRadius)
    (hρ : 0 < ρ) (hρc : ρ ≤ c.tangentRadius) :
    (c.restrict hr hrc hρ hρc).tangentRadius = ρ :=
  (rfl)

end LipschitzBoundaryChart

/-- An open set is a Lipschitz domain if each frontier point admits a Lipschitz boundary chart. -/
def IsLipschitzDomain (Ω : Opens F) : Prop :=
  ∀ x ∈ frontier (Ω : Set F), Nonempty (LipschitzBoundaryChart Ω x)

omit [FiniteDimensional ℝ F] in
/-- The open half-space based at `a` with inward unit normal `ν`. -/
def innerHalfSpace (a ν : F) : Opens F :=
  ⟨{y | 0 < inner ℝ ν (y - a)}, isOpen_lt continuous_const
    (continuous_const.inner (continuous_id.sub continuous_const))⟩

omit [FiniteDimensional ℝ F] in
@[simp]
theorem mem_innerHalfSpace {a ν y : F} : y ∈ innerHalfSpace a ν ↔ 0 < inner ℝ ν (y - a) :=
  Iff.rfl

omit [FiniteDimensional ℝ F] in
@[simp]
theorem coe_innerHalfSpace (a ν : F) :
    (innerHalfSpace a ν : Set F) = {y | 0 < inner ℝ ν (y - a)} :=
  Opens.coe_mk

omit [FiniteDimensional ℝ F] in
/-- The frontier of an open half-space lies in its defining hyperplane. -/
theorem inner_eq_zero_of_mem_frontier_innerHalfSpace {a ν x : F}
    (hx : x ∈ frontier (innerHalfSpace a ν : Set F)) : inner ℝ ν (x - a) = 0 := by
  rw [coe_innerHalfSpace] at hx
  exact (frontier_lt_subset_eq continuous_const
    (continuous_const.inner (continuous_id.sub continuous_const)) hx).symm

omit [FiniteDimensional ℝ F] in
/-- **The open half-space with unit inward normal `ν` is a Lipschitz domain.** -/
theorem isLipschitzDomain_innerHalfSpace (a ν : F) (hν : ‖ν‖ = 1) :
    IsLipschitzDomain (innerHalfSpace a ν) := by
  intro x hx
  have hx0 := inner_eq_zero_of_mem_frontier_innerHalfSpace hx
  refine ⟨{
    mem_frontier := hx
    normal := ν
    norm_normal := hν
    normalRadius := 1
    normalRadius_pos := zero_lt_one
    tangentRadius := 1
    tangentRadius_pos := zero_lt_one
    height := 0
    exists_lipschitzWith_height := ⟨0, LipschitzWith.const 0⟩
    height_zero := rfl
    mem_iff := ?_ }⟩
  intro y _
  have hcoord : inner ℝ ν (y - a) = inner ℝ ν (y - x) := by
    calc
      inner ℝ ν (y - a) = inner ℝ ν (y - x) + inner ℝ ν (x - a) := by
        rw [← inner_add_right]
        congr 2
        abel
      _ = inner ℝ ν (y - x) := by rw [hx0, add_zero]
  simp only [Pi.zero_apply, mem_innerHalfSpace, boundaryNormalCoordinate]
  rw [hcoord]

end TauCeti
