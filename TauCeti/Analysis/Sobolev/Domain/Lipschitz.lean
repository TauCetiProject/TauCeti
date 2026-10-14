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
function on `span ℝ {ν}ᗮ`.

The normal and tangential coordinates of `y` are respectively
`⟪ν, y - x⟫` and the orthogonal projection of `y - x` onto `span ℝ {ν}ᗮ`. Thus this
coordinate-free definition is precisely the usual definition after a rigid change of Euclidean
coordinates. The chart records both cylinder radii and the Lipschitz constant explicitly. Smaller
positive radii give another chart, allowing later trace and extension arguments to shrink charts
without changing their coordinates.

Every open half-space is a Lipschitz domain, with constant zero. This both supplies the basic
nondegenerate example and connects the definition to the flat model used by Sobolev trace theory.

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

/-- The hyperplane orthogonal to a prospective boundary normal. -/
def boundaryTangentSpace (ν : F) : Submodule ℝ F :=
  (Submodule.span ℝ {ν})ᗮ

omit [FiniteDimensional ℝ F] in
/-- A vector is tangential to `ν` exactly when it is orthogonal to `ν`. -/
@[simp]
theorem mem_boundaryTangentSpace {ν z : F} :
    z ∈ boundaryTangentSpace ν ↔ inner ℝ ν z = 0 := by
  simpa only [boundaryTangentSpace] using
    (Submodule.mem_orthogonal_singleton_iff_inner_right (𝕜 := ℝ) (u := ν) (v := z))

/-- The signed normal coordinate of `y`, in coordinates centred at `x` with normal `ν`. -/
def boundaryNormalCoordinate (ν x y : F) : ℝ :=
  inner ℝ ν (y - x)

omit [FiniteDimensional ℝ F] in
@[simp]
theorem boundaryNormalCoordinate_self (ν x : F) : boundaryNormalCoordinate ν x x = 0 := by
  simp [boundaryNormalCoordinate]

/-- The tangential coordinate of `y`, in coordinates centred at `x` with normal `ν`. -/
def boundaryTangentCoordinate (ν x y : F) : boundaryTangentSpace ν :=
  (boundaryTangentSpace ν).orthogonalProjectionOnto (y - x)

@[simp]
theorem boundaryTangentCoordinate_self (ν x : F) : boundaryTangentCoordinate ν x x = 0 := by
  simp [boundaryTangentCoordinate]

/-- The open product cylinder with normal radius `r` and tangential radius `ρ`, in coordinates
centred at `x` with normal `ν`. -/
def boundaryCylinder (ν x : F) (r ρ : ℝ) : Set F :=
  {y | |boundaryNormalCoordinate ν x y| < r ∧ ‖boundaryTangentCoordinate ν x y‖ < ρ}

theorem mem_boundaryCylinder {ν x y : F} {r ρ : ℝ} :
    y ∈ boundaryCylinder ν x r ρ ↔
      |boundaryNormalCoordinate ν x y| < r ∧ ‖boundaryTangentCoordinate ν x y‖ < ρ :=
  Iff.rfl

/-- A product cylinder is open. -/
theorem isOpen_boundaryCylinder (ν x : F) (r ρ : ℝ) : IsOpen (boundaryCylinder ν x r ρ) := by
  unfold boundaryCylinder boundaryNormalCoordinate boundaryTangentCoordinate
  have hsub : Continuous (fun y : F => y - x) := continuous_id.sub continuous_const
  have hnormal : Continuous (fun y : F => inner ℝ ν (y - x)) := continuous_const.inner hsub
  exact (isOpen_lt hnormal.abs continuous_const).inter
    (isOpen_lt ((boundaryTangentSpace ν).orthogonalProjectionOnto.continuous.comp
      hsub).norm continuous_const)

/-- Decreasing either radius decreases the corresponding product cylinder. -/
theorem boundaryCylinder_mono {ν x : F} {r r' ρ ρ' : ℝ} (hr : r' ≤ r) (hρ : ρ' ≤ ρ) :
    boundaryCylinder ν x r' ρ' ⊆ boundaryCylinder ν x r ρ := by
  intro y hy
  exact ⟨hy.1.trans_le hr, hy.2.trans_le hρ⟩

/-- A Lipschitz graph description of an open set near one of its frontier points.

The chosen unit vector points into the domain: locally, membership is the strict inequality
`graph (tangentCoordinate y) < normalCoordinate y`. -/
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
  /-- The height function over the orthogonal tangent hyperplane. -/
  graph : boundaryTangentSpace normal → ℝ
  /-- An explicit Lipschitz constant for the height function. -/
  lipschitzConstant : ℝ≥0
  /-- The height function has the recorded Lipschitz constant on the tangential chart ball. -/
  lipschitzOnWith_graph :
    LipschitzOnWith lipschitzConstant graph (Metric.ball 0 tangentRadius)
  /-- The graph passes through the centre of the chart. -/
  graph_zero : graph 0 = 0
  /-- Inside the product cylinder, the domain is exactly the region above the graph. -/
  mem_iff {y : F} (hy : y ∈ boundaryCylinder normal x normalRadius tangentRadius) :
    y ∈ Ω ↔ graph (boundaryTangentCoordinate normal x y) <
      boundaryNormalCoordinate normal x y

namespace LipschitzBoundaryChart

variable {Ω : Opens F} {x : F}

/-- The graph function of a Lipschitz boundary chart is continuous on its tangential chart ball. -/
theorem continuousOn_graph (c : LipschitzBoundaryChart Ω x) :
    ContinuousOn c.graph (Metric.ball 0 c.tangentRadius) :=
  c.lipschitzOnWith_graph.continuousOn

/-- The centre of a boundary chart belongs to every one of its product cylinders. -/
theorem mem_boundaryCylinder_center (c : LipschitzBoundaryChart Ω x) :
    x ∈ boundaryCylinder c.normal x c.normalRadius c.tangentRadius := by
  simp [boundaryCylinder, c.normalRadius_pos, c.tangentRadius_pos]

/-- Restrict a Lipschitz boundary chart to smaller positive normal and tangential radii. -/
def restrict (c : LipschitzBoundaryChart Ω x) {r ρ : ℝ}
    (hr : 0 < r) (hrc : r ≤ c.normalRadius)
    (hρ : 0 < ρ) (hρc : ρ ≤ c.tangentRadius) : LipschitzBoundaryChart Ω x where
  mem_frontier := c.mem_frontier
  normal := c.normal
  norm_normal := c.norm_normal
  normalRadius := r
  normalRadius_pos := hr
  tangentRadius := ρ
  tangentRadius_pos := hρ
  graph := c.graph
  lipschitzConstant := c.lipschitzConstant
  lipschitzOnWith_graph := c.lipschitzOnWith_graph.mono (Metric.ball_subset_ball hρc)
  graph_zero := c.graph_zero
  mem_iff hy := c.mem_iff (boundaryCylinder_mono hrc hρc hy)

@[simp]
theorem restrict_normal (c : LipschitzBoundaryChart Ω x) {r ρ : ℝ}
    (hr : 0 < r) (hrc : r ≤ c.normalRadius)
    (hρ : 0 < ρ) (hρc : ρ ≤ c.tangentRadius) :
    (c.restrict hr hrc hρ hρc).normal = c.normal :=
  (rfl)

@[simp]
theorem restrict_lipschitzConstant (c : LipschitzBoundaryChart Ω x) {r ρ : ℝ}
    (hr : 0 < r) (hrc : r ≤ c.normalRadius)
    (hρ : 0 < ρ) (hρc : ρ ≤ c.tangentRadius) :
    (c.restrict hr hrc hρ hρc).lipschitzConstant = c.lipschitzConstant :=
  (rfl)

@[simp]
theorem restrict_normalRadius (c : LipschitzBoundaryChart Ω x) {r ρ : ℝ}
    (hr : 0 < r) (hrc : r ≤ c.normalRadius)
    (hρ : 0 < ρ) (hρc : ρ ≤ c.tangentRadius) :
    (c.restrict hr hrc hρ hρc).normalRadius = r :=
  (rfl)

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

/-- The graph characterization of a Lipschitz domain. -/
theorem isLipschitzDomain_iff (Ω : Opens F) :
    IsLipschitzDomain Ω ↔
      ∀ x ∈ frontier (Ω : Set F), Nonempty (LipschitzBoundaryChart Ω x) :=
  Iff.rfl

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
/-- The frontier of an open half-space lies in its defining hyperplane. -/
theorem inner_eq_zero_of_mem_frontier_innerHalfSpace {a ν x : F}
    (hx : x ∈ frontier (innerHalfSpace a ν : Set F)) : inner ℝ ν (x - a) = 0 :=
  (frontier_lt_subset_eq continuous_const
    (continuous_const.inner (continuous_id.sub continuous_const)) hx).symm

/-- **Open half-spaces are Lipschitz domains.** The boundary graph is zero and has Lipschitz
constant zero; both chart radii may be chosen arbitrarily, here as one. -/
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
    graph := 0
    lipschitzConstant := 0
    lipschitzOnWith_graph := (LipschitzWith.const 0).lipschitzOnWith
    graph_zero := rfl
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
