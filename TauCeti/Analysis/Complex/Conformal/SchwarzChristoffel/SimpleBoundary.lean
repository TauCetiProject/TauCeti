/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Image
import TauCeti.Analysis.Complex.PlaneSeparation.JordanCurve
import TauCeti.Algebra.BigOperators.Finset.Fiber

/-!
# The Schwarz--Christoffel image of a simple boundary polygon

Let `F = schwarzChristoffelPrimitive a e z₀` and let `P` be the range of the compactified boundary
path `schwarzChristoffelCompactifiedBoundary a e z₀`, under the standing assumptions of
`TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Image`: every finite prevertex is
integrable and the total exponent is less than `-1`. No convexity is assumed: the turning
exponents may have either sign, so the polygon may have reentrant corners.

When the compactified boundary path is injective, `P` is a Jordan curve, and the image of the
upper half-plane **does not meet `P`**: the image is open and lies in the filled hull of `P`, and
an open set in the filled hull of a Jordan curve misses the curve
(`TauCeti.IsJordanCurve.disjoint_of_isOpen_of_subset_filledHull`). Consequently the image is
exactly one complementary component of `P`, and its frontier is all of `P`.

Over that component, `TauCeti.isCoveringMapOn_schwarzChristoffelPrimitive` therefore exhibits the
whole upper half-plane as a covering space. For convex data the covering is a bijection onto the
interior of the polygon, `TauCeti.bijOn_schwarzChristoffelPrimitive_interior_closedConvexHull`.

## Main results

* `TauCeti.disjoint_image_schwarzChristoffelPrimitive_range` — the image of the upper half-plane
  misses a simple compactified boundary path.
* `TauCeti.image_schwarzChristoffelPrimitive_eq_connectedComponentIn` — the image is the
  component of the complement of the path containing `F z₀`.
* `TauCeti.frontier_image_schwarzChristoffelPrimitive_eq_range` — the frontier of the image is the
  whole path.
* `TauCeti.exists_ball_preimage_schwarzChristoffelPrimitive_subset_of_boundary_injective` —
  preimages of values near a simple boundary point lie near its unique boundary preimage.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Metric Set UpperHalfPlane
open scoped OnePoint

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **The Schwarz--Christoffel image misses a simple boundary path.** If every finite prevertex is
integrable, the total exponent is less than `-1`, and the compactified boundary path is injective,
then the primitive sends no point of the upper half-plane onto that path. -/
theorem disjoint_image_schwarzChristoffelPrimitive_range (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀)) :
    Disjoint (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)
      (range (schwarzChristoffelCompactifiedBoundary a e z₀)) :=
  (isJordanCurve_range_schwarzChristoffelCompactifiedBoundary a e z₀ hfinite hinfty hinj)
    |>.disjoint_of_isOpen_of_subset_filledHull
      (isOpen_image_schwarzChristoffelPrimitive a e z₀ isOpen_upperHalfPlaneSet subset_rfl)
      (image_schwarzChristoffelPrimitive_subset_filledHull a e z₀ hfinite hinfty)

/-- **The Schwarz--Christoffel image is a complementary component of a simple boundary path.**
Under the hypotheses of `TauCeti.disjoint_image_schwarzChristoffelPrimitive_range`, the image of the
upper half-plane is the component of the complement of the compactified boundary path containing
the image of the base point. -/
theorem image_schwarzChristoffelPrimitive_eq_connectedComponentIn (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hinfty : ∑ i, e i < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀)) :
    schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet =
      connectedComponentIn (range (schwarzChristoffelCompactifiedBoundary a e z₀))ᶜ
        (schwarzChristoffelPrimitive a e z₀ z₀) := by
  have hdisj := disjoint_image_schwarzChristoffelPrimitive_range a e z₀ hfinite hinfty hinj
  refine image_schwarzChristoffelPrimitive_eq_of_subset a e z₀ hfinite hinfty
    isPreconnected_connectedComponentIn
    (disjoint_left.mpr fun w hw => connectedComponentIn_subset _ _ hw) ?_
  exact ((convex_halfSpace_im_gt 0).isPreconnected.image _
    (differentiableOn_schwarzChristoffelPrimitive a e z₀).continuousOn).subset_connectedComponentIn
    (mem_image_of_mem _ z₀.im_pos) (subset_compl_iff_disjoint_right.mpr hdisj)

/-- **The frontier of the Schwarz--Christoffel image is a simple boundary path.** Under the
hypotheses of `TauCeti.disjoint_image_schwarzChristoffelPrimitive_range`, the frontier of the image
of the upper half-plane is the whole range of the compactified boundary path. -/
@[simp]
theorem frontier_image_schwarzChristoffelPrimitive_eq_range (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀)) :
    frontier (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) =
      range (schwarzChristoffelCompactifiedBoundary a e z₀) := by
  rw [frontier_image_schwarzChristoffelPrimitive a e z₀ hfinite hinfty,
    (disjoint_image_schwarzChristoffelPrimitive_range a e z₀ hfinite hinfty hinj).sdiff_eq_right]

/-- Near a point of a simple compactified boundary, every preimage under the primitive lies
near its unique boundary preimage. This includes preimages tending to infinity: the limit there
is the value at the compactification point, which is distinct from the chosen boundary value. -/
theorem exists_ball_preimage_schwarzChristoffelPrimitive_subset_of_boundary_injective
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀))
    (x : ℝ) {U : Set ℂ} (hU : IsOpen U) (hxU : (x : ℂ) ∈ U) :
    ∃ ε > 0, ∀ z ∈ upperHalfPlaneSet,
      schwarzChristoffelPrimitive a e z₀ z ∈
        Metric.ball (schwarzChristoffelBoundary a e z₀ x) ε → z ∈ U := by
  set F := schwarzChristoffelPrimitive a e z₀
  set B := schwarzChristoffelBoundary a e z₀
  set V := schwarzChristoffelVertexAtInfinity a e z₀
  set E := closure (upperHalfPlaneSet \ U)
  have hEclosed : IsClosed E := isClosed_closure
  have hEsub : E ⊆ closure upperHalfPlaneSet :=
    closure_mono sdiff_subset
  have hxE : (x : ℂ) ∉ E := by
    have hsub : E ⊆ Uᶜ :=
      closure_minimal (fun z hz => hz.2) hU.isClosed_compl
    exact fun hx => hsub hx hxU
  have hBV : B x ≠ V := by
    intro h
    have heq : (x : OnePoint ℝ) = ∞ := hinj (by simpa using h)
    exact OnePoint.coe_ne_infty x heq
  have hdisj : Disjoint (F '' upperHalfPlaneSet)
      (range (schwarzChristoffelCompactifiedBoundary a e z₀)) :=
    disjoint_image_schwarzChristoffelPrimitive_range a e z₀ hfinite hinfty hinj
  -- No point outside `U` in the closed upper half-plane has the chosen boundary value.
  have hnotE : B x ∉
      extendFrom upperHalfPlaneSet F '' E := by
    rintro ⟨z, hzE, hz⟩
    by_cases hzH : z ∈ upperHalfPlaneSet
    · have hF : F z = B x := by
        rw [extendFrom_extends
          (differentiableOn_schwarzChristoffelPrimitive a e z₀).continuousOn z hzH] at hz
        exact hz
      exact Set.disjoint_left.mp hdisj (mem_image_of_mem F hzH)
        ⟨(x : OnePoint ℝ), by simp [hF, B]⟩
    · have hre : ((z.re : ℝ) : ℂ) = z := by
        have him : z.im = 0 := by
          have hle : 0 ≤ z.im := by
            simpa only [Complex.closure_setOfPred_lt_im, Set.mem_ofPred_eq] using hEsub hzE
          exact le_antisymm (not_lt.mp hzH) hle
        exact Complex.ext (by simp) (by simp [him])
      have hlim := tendsto_schwarzChristoffelPrimitive_boundary a e z₀ z.re
        (lt_sum_filter_eq_of_forall_apply neg_one_lt_zero hfinite z.re)
      rw [hre] at hlim
      have hBz : B z.re = B x := by
        simpa only [B, F] using (extendFrom_eq (hEsub hzE) hlim).symm.trans hz
      have hzx : z.re = x := by
        apply OnePoint.coe_injective
        apply hinj
        simpa using hBz
      rw [← hre, hzx] at hzE
      exact hxE hzE
  -- A preimage escaping every compact set tends to the different value at infinity. On a
  -- compact piece, the continuous extension turns closure of the image into an actual image.
  have hnotcl : B x ∉ closure (F '' (upperHalfPlaneSet \ U)) := by
    intro hw
    have hclose : ∀ ε > 0, B x ∈ extendFrom upperHalfPlaneSet F '' E ∨
        dist (B x) V ≤ ε := by
      intro ε hε
      obtain ⟨R, hR⟩ :=
        exists_forall_dist_schwarzChristoffelPrimitive_le a e z₀ hinfty hε
      let K := E ∩ Metric.closedBall 0 R
      have hKcompact : IsCompact K :=
        (isCompact_closedBall 0 R).inter_left hEclosed
      have hKsub : K ⊆ closure upperHalfPlaneSet :=
        (inter_subset_left).trans hEsub
      have himage : F '' (upperHalfPlaneSet \ U) ⊆
          extendFrom upperHalfPlaneSet F '' K ∪ Metric.closedBall V ε := by
        rintro _ ⟨z, hz, rfl⟩
        by_cases hzR : R ≤ ‖z‖
        · exact Or.inr (hR z hz.1 hzR)
        · refine Or.inl ⟨z, ⟨subset_closure hz,
            by simpa using (not_le.mp hzR).le⟩, ?_⟩
          exact extendFrom_extends
            (differentiableOn_schwarzChristoffelPrimitive a e z₀).continuousOn z hz.1
      have hKimage := hKcompact.image_of_continuousOn
        ((continuousOn_extendFrom_schwarzChristoffelPrimitive a e z₀ hfinite).mono hKsub)
      have hw' := closure_mono himage hw
      rw [(hKimage.isClosed.union Metric.isClosed_closedBall).closure_eq] at hw'
      rcases hw' with ⟨z, hzK, hzeq⟩ | hw'
      · exact Or.inl ⟨z, hzK.1, hzeq⟩
      · exact Or.inr hw'
    have hD : 0 < dist (B x) V := dist_pos.mpr hBV
    have hle := (hclose (dist (B x) V / 2) (half_pos hD)).resolve_left hnotE
    linarith
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (isClosed_closure.isOpen_compl.mem_nhds hnotcl)
  refine ⟨ε, hε, fun z hz hzball => ?_⟩
  by_contra hzU
  exact (hball hzball) (subset_closure ⟨z, ⟨hz, hzU⟩, rfl⟩)

end TauCeti
