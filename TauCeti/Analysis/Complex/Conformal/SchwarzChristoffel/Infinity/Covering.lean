/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the bounded covering theory supplies the predicates and boundary map in the statements.
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Covering
-- Non-public: properness of the boundary map, escape of the primitive at infinity, the
-- fibre-sum bound and injectivity of coverings of simply connected sets are used only in proofs.
import TauCeti.Algebra.BigOperators.Finset.Fiber
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Divergence
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Infinity.Power
import TauCeti.Topology.Homotopy.Covering

/-!
# The Schwarz--Christoffel primitive onto an unbounded polygon

Let `F = schwarzChristoffelPrimitive a e z₀` and `B = schwarzChristoffelBoundary a e z₀`. When
every finite prevertex is integrable and the total exponent `∑ i, e i` is at least `-1`, the
point at infinity of the upper half-plane is sent to infinity: `B` escapes every bounded set at
both ends of the real axis, and `F` escapes every bounded set uniformly in the upper half-plane.
The candidate polygon is then unbounded, and its boundary is the range of `B`, which is closed
because `B` is proper.

This file develops, in that regime, the counterpart of the bounded image and covering theory of
`TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Image` and
`TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Covering`. The primitive is proper over
the complement of `range B`: the points of the upper half-plane sent into a compact set avoiding
`range B` form a compact set. Consequently the closure of the image is the image together with
`range B`, the primitive is a covering map over the complement of `range B`, and it maps the
upper half-plane bijectively onto any simply connected set that avoids `range B` and contains the
image. Unlike in the bounded case only compact, rather than closed, sets have compact preimages,
since the image is unbounded.

## Main results

* `TauCeti.isCompact_upperHalfPlaneSet_inter_preimage_schwarzChristoffelPrimitive_of_neg_one_le_sum`
  -- the preimage of a compact set avoiding the boundary values is compact.
* `TauCeti.closure_image_schwarzChristoffelPrimitive_of_neg_one_le_sum` -- the closure of the
  image is the image together with the boundary values.
* `TauCeti.frontier_image_schwarzChristoffelPrimitive_of_neg_one_le_sum` -- its frontier is the
  set of boundary values outside the image.
* `TauCeti.image_schwarzChristoffelPrimitive_eq_of_subset_of_neg_one_le_sum` -- a preconnected
  set avoiding the boundary values and containing the image is the image.
* `TauCeti.isCoveringMapOn_schwarzChristoffelPrimitive_of_neg_one_le_sum` -- on `ℍ`, the
  primitive is a covering map over the complement of the boundary values.
* `TauCeti.bijOn_schwarzChristoffelPrimitive_of_subset_of_neg_one_le_sum` -- the primitive maps
  the upper half-plane bijectively onto every simply connected set that avoids the boundary values
  and contains the image.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Bornology Filter Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **The Schwarz--Christoffel primitive is proper over the complement of its boundary values**
when every finite prevertex is integrable and the total exponent is at least `-1`. The points of
the upper half-plane that the primitive sends into a compact set `K` avoiding the range of the
boundary map form a compact set. -/
theorem isCompact_upperHalfPlaneSet_inter_preimage_schwarzChristoffelPrimitive_of_neg_one_le_sum
    (a e : ι → ℝ) (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hsum : -1 ≤ ∑ i, e i) {K : Set ℂ} (hK : IsCompact K)
    (hKB : Disjoint K (range (schwarzChristoffelBoundary a e z₀))) :
    IsCompact (upperHalfPlaneSet ∩ schwarzChristoffelPrimitive a e z₀ ⁻¹' K) := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_upperHalfPlaneSet_inter_preimage_schwarzChristoffelPrimitive a e z₀ hfinite
      hK.isClosed hKB) ?_
  -- Far out in the upper half-plane, the primitive has escaped the bounded set `K`.
  have h := (tendsto_schwarzChristoffelPrimitive_atInfinity_cobounded_of_neg_one_le_sum a e z₀
    hsum).eventually (isBounded_def.mp hK.isBounded)
  rw [eventually_inf_principal] at h
  exact isBounded_def.mpr (h.mono fun z hz hzK => hz hzK.1 hzK.2)

/-- **The closure of the image of the Schwarz--Christoffel primitive** is the image together with
the boundary values, when every finite prevertex is integrable and the total exponent is at least
`-1`. -/
theorem closure_image_schwarzChristoffelPrimitive_of_neg_one_le_sum (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hsum : -1 ≤ ∑ i, e i) :
    closure (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) =
      schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ∪
        range (schwarzChristoffelBoundary a e z₀) := by
  set F := schwarzChristoffelPrimitive a e z₀
  have hB := (isProperMap_schwarzChristoffelBoundary a e z₀ hfinite hsum).isClosed_range
  refine Subset.antisymm (fun w hw => ?_) (union_subset subset_closure ?_)
  · rw [mem_union, or_iff_not_imp_right]
    intro hwB
    -- A closed ball about `w` avoids the boundary values, so its preimage is compact.
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hB.isOpen_compl w hwB
    have hKB : Disjoint (closedBall w (r / 2)) (range (schwarzChristoffelBoundary a e z₀)) :=
      subset_compl_iff_disjoint_right.mp <| (closedBall_subset_ball (half_lt_self hr)).trans hball
    have hcpt :=
      isCompact_upperHalfPlaneSet_inter_preimage_schwarzChristoffelPrimitive_of_neg_one_le_sum
        a e z₀ hfinite hsum (isCompact_closedBall w (r / 2)) hKB
    have himage : IsClosed (F '' (upperHalfPlaneSet ∩ F ⁻¹' closedBall w (r / 2))) :=
      (hcpt.image_of_continuousOn
        ((differentiableOn_schwarzChristoffelPrimitive a e z₀).continuousOn.mono
          inter_subset_left)).isClosed
    -- Near `w`, the image consists of values at points of that compact preimage.
    have hsub : ball w (r / 2) ∩ F '' upperHalfPlaneSet ⊆
        F '' (upperHalfPlaneSet ∩ F ⁻¹' closedBall w (r / 2)) := by
      rintro _ ⟨hz, z, hzH, rfl⟩
      exact ⟨z, ⟨hzH, ball_subset_closedBall hz⟩, rfl⟩
    have hw' := closure_mono hsub
      (isOpen_ball.inter_closure ⟨mem_ball_self (half_pos hr), hw⟩)
    rw [himage.closure_eq] at hw'
    exact image_mono inter_subset_left hw'
  -- Every boundary value is a limit of the primitive from the upper half-plane.
  · rintro _ ⟨x, rfl⟩
    have := Real.nhdsWithin_upperHalfPlaneSet_neBot x
    exact mem_closure_of_tendsto (tendsto_schwarzChristoffelPrimitive_boundary a e z₀ x
        (lt_sum_filter_eq_of_forall_apply neg_one_lt_zero hfinite x))
      (eventually_mem_nhdsWithin.mono fun z hz => mem_image_of_mem F hz)

/-- **The frontier of the image of the Schwarz--Christoffel primitive** is the set of boundary
values that the image does not cover, when every finite prevertex is integrable and the total
exponent is at least `-1`. -/
theorem frontier_image_schwarzChristoffelPrimitive_of_neg_one_le_sum (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hsum : -1 ≤ ∑ i, e i) :
    frontier (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) =
      range (schwarzChristoffelBoundary a e z₀) \
        schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet := by
  have hopen :=
    isOpen_image_schwarzChristoffelPrimitive a e z₀ isOpen_upperHalfPlaneSet subset_rfl
  rw [frontier, closure_image_schwarzChristoffelPrimitive_of_neg_one_le_sum a e z₀ hfinite hsum,
    hopen.interior_eq, union_sdiff_left]

/-- **A preconnected set avoiding the boundary values and containing the image is the image**,
when every finite prevertex is integrable and the total exponent is at least `-1`. -/
theorem image_schwarzChristoffelPrimitive_eq_of_subset_of_neg_one_le_sum (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hsum : -1 ≤ ∑ i, e i) {W : Set ℂ} (hW : IsPreconnected W)
    (hWB : Disjoint W (range (schwarzChristoffelBoundary a e z₀)))
    (hFW : schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ⊆ W) :
    schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet = W := by
  refine hFW.antisymm <| hW.subset_of_closure_inter_subset
    (isOpen_image_schwarzChristoffelPrimitive a e z₀ isOpen_upperHalfPlaneSet subset_rfl) ?_
    fun w ⟨hw, hwW⟩ => ?_
  · have hz₀ : (z₀ : ℂ) ∈ upperHalfPlaneSet := z₀.im_pos
    exact ⟨_, hFW (mem_image_of_mem _ hz₀), mem_image_of_mem _ hz₀⟩
  · rw [closure_image_schwarzChristoffelPrimitive_of_neg_one_le_sum a e z₀ hfinite hsum] at hw
    exact hw.resolve_right (disjoint_left.mp hWB hwW)

/-- **The Schwarz--Christoffel primitive is a covering map off its boundary values** when every
finite prevertex is integrable and the total exponent is at least `-1`. Viewed as a map on `ℍ`,
it is a covering map over the complement of the range of the boundary map. -/
theorem isCoveringMapOn_schwarzChristoffelPrimitive_of_neg_one_le_sum (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hsum : -1 ≤ ∑ i, e i) :
    IsCoveringMapOn (fun τ : ℍ => schwarzChristoffelPrimitive a e z₀ τ)
      (range (schwarzChristoffelBoundary a e z₀))ᶜ :=
  isCoveringMapOn_schwarzChristoffelPrimitive_of_isCompact_preimage a e z₀
    (isProperMap_schwarzChristoffelBoundary a e z₀ hfinite hsum).isClosed_range.isOpen_compl
    fun _ hKB hK =>
      isCompact_upperHalfPlaneSet_inter_preimage_schwarzChristoffelPrimitive_of_neg_one_le_sum
        a e z₀ hfinite hsum hK (subset_compl_iff_disjoint_right.mp hKB)

/-- **The Schwarz--Christoffel primitive is a bijection onto a simply connected region avoiding
its boundary values**, when every finite prevertex is integrable and the total exponent is at
least `-1`. If the image of the upper half-plane lies in a simply connected set `W` disjoint from
the range of the boundary map, then the primitive maps the upper half-plane bijectively onto
`W`. -/
theorem bijOn_schwarzChristoffelPrimitive_of_subset_of_neg_one_le_sum (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hsum : -1 ≤ ∑ i, e i) {W : Set ℂ} [SimplyConnectedSpace W]
    (hWB : Disjoint W (range (schwarzChristoffelBoundary a e z₀)))
    (hFW : schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ⊆ W) :
    BijOn (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet W := by
  have hW : IsPreconnected W := isPreconnected_iff_preconnectedSpace.mpr inferInstance
  have himage :=
    image_schwarzChristoffelPrimitive_eq_of_subset_of_neg_one_le_sum a e z₀ hfinite hsum hW hWB hFW
  refine ⟨himage ▸ mapsTo_image _ _, fun z hz w hw hzw => ?_, himage ▸ surjOn_image _ _⟩
  -- The path-connected `ℍ` covers the simply connected `W`, so the covering is trivial.
  exact congrArg ((↑) : ℍ → ℂ) <|
    (isCoveringMapOn_schwarzChristoffelPrimitive_of_neg_one_le_sum a e z₀ hfinite
      hsum).injective_of_range_subset (subset_compl_iff_disjoint_right.mpr hWB)
      (range_subset_iff.mpr fun τ => hFW (mem_image_of_mem _ τ.im_pos))
      (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) hzw

end TauCeti
