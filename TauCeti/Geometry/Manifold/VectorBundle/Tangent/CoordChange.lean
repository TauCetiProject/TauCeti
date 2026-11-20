/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Tangent coordinate changes

The tangent coordinate change `tangentCoordChange I x y z` between the preferred charts at `x` and
`y` is the derivative, within the range of the model, of the change of extended charts. On a
boundaryless manifold the range is the whole model space, so it is an honest derivative. A linear
map `L` between tangent spaces, read in the charts at `x₀` and `y₀` instead of the preferred charts
of its base points, is conjugated by tangent coordinate changes, and this reading determines `L`.

## Main results

* `TauCeti.Manifold.tangentCoordChange_eq_fderiv`: on a boundaryless manifold, the tangent
  coordinate change is the derivative of the change of extended charts.
* `TauCeti.Manifold.tangentCoordChange_comp_comp_tangentCoordChange`: changing the charts at both
  ends of a linear map in coordinates through intermediate charts gives the direct change of chart.
* `TauCeti.Manifold.eq_of_tangentCoordChange_comp_comp_eq`: a linear map between tangent spaces is
  determined by its expression in the charts at any two points whose chart sources contain its
  base points.
-/

public section

open Set
open scoped Manifold

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]

/-- On a boundaryless manifold, the tangent change of coordinates from the chart at `x` to the
chart at `y`, at `z`, is the derivative of the change of extended charts
`extChartAt I y ∘ (extChartAt I x).symm` at the coordinate of `z`. -/
theorem tangentCoordChange_eq_fderiv [I.Boundaryless] {x y z : M} :
    tangentCoordChange I x y z =
      fderiv 𝕜 (extChartAt I y ∘ (extChartAt I x).symm) (extChartAt I x z) := by
  rw [tangentCoordChange_def, I.range_eq_univ, fderivWithin_univ]

/-- Changing the charts at both ends of a linear map `L` in coordinates, from the charts at `a` and
`b` to those at the base points `x` and `y` and then to those at `x₀` and `y₀`, gives the direct
change of chart from `a` and `b` to `x₀` and `y₀`. -/
theorem tangentCoordChange_comp_comp_tangentCoordChange {a x₀ x : M} {b y₀ y : N}
    (hx : x ∈ (chartAt H x₀).source ∩ (chartAt H a).source)
    (hy : y ∈ (chartAt H' y₀).source ∩ (chartAt H' b).source) (L : E →L[𝕜] E') :
    tangentCoordChange I' y y₀ y ∘L
        (tangentCoordChange I' b y y ∘L L ∘L tangentCoordChange I x a x) ∘L
          tangentCoordChange I x₀ x x =
      tangentCoordChange I' b y₀ y ∘L L ∘L tangentCoordChange I x₀ a x := by
  ext v
  simp only [ContinuousLinearMap.comp_apply]
  rw [tangentCoordChange_comp (I := I)
      (by simp only [extChartAt_source]; exact ⟨⟨hx.1, mem_chart_source H x⟩, hx.2⟩),
    tangentCoordChange_comp
      (by simp only [extChartAt_source]; exact ⟨⟨hy.2, mem_chart_source H' y⟩, hy.1⟩)]

/-- A linear map between the tangent spaces at `x` and `y`, read in the model spaces, is determined
by its expression in the charts at `x₀` and `y₀`, when their sources contain `x` and `y`. -/
theorem eq_of_tangentCoordChange_comp_comp_eq {x₀ x : M} {y₀ y : N}
    (hx : x ∈ (chartAt H x₀).source) (hy : y ∈ (chartAt H' y₀).source)
    {L L' : E →L[𝕜] E'}
    (h : tangentCoordChange I' y y₀ y ∘L L ∘L tangentCoordChange I x₀ x x =
      tangentCoordChange I' y y₀ y ∘L L' ∘L tangentCoordChange I x₀ x x) :
    L = L' := by
  have hX : x ∈ (extChartAt I x).source ∩ (extChartAt I x₀).source ∩ (extChartAt I x).source := by
    simp only [extChartAt_source]
    exact ⟨⟨mem_chart_source H x, hx⟩, mem_chart_source H x⟩
  have hY : y ∈ (extChartAt I' y).source ∩ (extChartAt I' y₀).source ∩
      (extChartAt I' y).source := by
    simp only [extChartAt_source]
    exact ⟨⟨mem_chart_source H' y, hy⟩, mem_chart_source H' y⟩
  -- Evaluating the composite is definitional; the tangent spaces are the model spaces.
  have key : ∀ (K : E →L[𝕜] E') (w : E),
      (tangentCoordChange I' y y₀ y ∘L K ∘L tangentCoordChange I x₀ x x) w =
        tangentCoordChange I' y y₀ y (K (tangentCoordChange I x₀ x x w)) :=
    fun _ _ ↦ rfl
  ext v
  have hv := congrArg (tangentCoordChange I' y₀ y y)
    (DFunLike.congr_fun h (tangentCoordChange I x x₀ x v))
  have hY' : ∀ w : E',
      tangentCoordChange I' y₀ y y (tangentCoordChange I' y y₀ y w) = w := fun w ↦
    (tangentCoordChange_comp hY).trans (tangentCoordChange_self (mem_extChartAt_source y))
  have hX' : tangentCoordChange I x₀ x x (tangentCoordChange I x x₀ x v) = v :=
    (tangentCoordChange_comp hX).trans (tangentCoordChange_self (mem_extChartAt_source x))
  rwa [key, key, hY', hY', hX'] at hv

end TauCeti.Manifold
