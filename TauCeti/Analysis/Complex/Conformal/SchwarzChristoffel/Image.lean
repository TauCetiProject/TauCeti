/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the compactified boundary path and the filled hull occur in the exported statements.
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Compactification
public import TauCeti.Analysis.Normed.Module.FilledHull
-- Non-public: analyticity of the primitive and the inverse function theorem are used only to
-- prove that the primitive is an open map.
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
-- Non-public: the fibre-sum bound is used only to spread integrability off the prevertices.
import TauCeti.Algebra.BigOperators.Finset.Fiber

/-!
# The image of the Schwarz--Christoffel primitive and its boundary

Let `F = schwarzChristoffelPrimitive a e z₀` and let `P` be the range of the compactified boundary
map `schwarzChristoffelCompactifiedBoundary a e z₀`, the closed boundary path through all the
finite vertices and the vertex at infinity.  For a monotone family of prevertices,
`range_schwarzChristoffelCompactifiedBoundary` identifies `P` with the boundary of
`schwarzChristoffelPolygon`.

This file locates the image `F '' upperHalfPlaneSet` relative to `P`, assuming only that every
finite prevertex is integrable and that the total exponent is less than `-1`. These results do
not assume simplicity of `P` or injectivity of `F`. The image is open because `F` has a
nonvanishing derivative. It is bounded, and its closure is exactly the image together with `P`:
every point of `P` is a boundary limit of `F`. Every limit of `F` from the upper half-plane is
either an interior value, a finite boundary value or the vertex at infinity. Hence the frontier
of the image is `P` minus the image.

Two consequences describe the image by the components of the complement of `P`.  The image lies
in `filledHull P`: it misses the unbounded complementary component.  And a complementary
component that meets the image is contained in it.  Away from `P`, the image is therefore a union
of bounded complementary components of `P`; identifying it with the inside of the polygon further
requires knowing those components and showing that the image does not meet `P`.  In the same
direction, a preconnected set avoiding `P` and containing the image is equal to the image.

The primitive is also proper over the complement of `P`: the points of the upper half-plane that
it sends into a closed set avoiding `P` form a compact set.  Near the real axis and near infinity
the primitive is close to its boundary values, which all lie on `P`.

The continuous extension to the closed upper half-plane and convergence to the vertex at infinity
are also available separately. They control preimages near a specified boundary value.

## Main results

* `TauCeti.isOpen_image_schwarzChristoffelPrimitive` -- the primitive maps open subsets of the
  upper half-plane to open sets.
* `TauCeti.isBounded_image_schwarzChristoffelPrimitive` -- the image of the upper half-plane is
  bounded.
* `TauCeti.closure_image_schwarzChristoffelPrimitive` -- its closure is the image together with
  the compactified boundary path.
* `TauCeti.continuousOn_extendFrom_schwarzChristoffelPrimitive` -- the extension is continuous on
  the closed upper half-plane.
* `TauCeti.exists_forall_dist_schwarzChristoffelPrimitive_le` -- the primitive approaches its
  vertex at infinity uniformly outside a large ball.
* `TauCeti.frontier_image_schwarzChristoffelPrimitive` -- its frontier is the part of the
  boundary path outside the image.
* `TauCeti.image_schwarzChristoffelPrimitive_subset_filledHull` -- the image lies in the filled
  hull of the boundary path.
* `TauCeti.image_schwarzChristoffelPrimitive_subset_interior_closedConvexHull` -- the image lies
  in the interior of the closed convex hull of the boundary path.
* `TauCeti.connectedComponentIn_subset_image_schwarzChristoffelPrimitive` -- a complementary
  component of the boundary path meeting the image lies in the image.
* `TauCeti.image_schwarzChristoffelPrimitive_eq_of_subset` -- a preconnected set avoiding the
  boundary path and containing the image is the image.
* `TauCeti.isCompact_upperHalfPlaneSet_inter_preimage_schwarzChristoffelPrimitive` -- the
  preimage of a closed set avoiding the boundary path is compact.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Bornology Complex Filter Metric Set Topology UpperHalfPlane
open scoped OnePoint

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **The Schwarz--Christoffel primitive is an open map on the upper half-plane.**  Its derivative
is the integrand, which never vanishes there, so the inverse function theorem makes the image of
every neighbourhood a neighbourhood. -/
theorem isOpen_image_schwarzChristoffelPrimitive (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    {s : Set ℂ} (hs : IsOpen s) (hsH : s ⊆ upperHalfPlaneSet) :
    IsOpen (schwarzChristoffelPrimitive a e z₀ '' s) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  have hzH : z ∈ upperHalfPlaneSet := hsH hz
  have hstrict := ((differentiableOn_schwarzChristoffelPrimitive a e z₀).analyticAt
    (isOpen_upperHalfPlaneSet.mem_nhds hzH)).hasStrictDerivAt
  have hderiv : deriv (schwarzChristoffelPrimitive a e z₀) z ≠ 0 := by
    rw [deriv_schwarzChristoffelPrimitive a e z₀ hzH]
    exact schwarzChristoffelIntegrand_ne_zero a e hzH
  rw [← hstrict.map_nhds_eq hderiv]
  exact image_mem_map (hs.mem_nhds hz)

/-- A point of the closed upper half-plane outside the open one is real. -/
private theorem ofReal_re_eq_of_mem_closure_of_notMem {z : ℂ} (hz : z ∈ closure upperHalfPlaneSet)
    (hzH : z ∉ upperHalfPlaneSet) : ((z.re : ℝ) : ℂ) = z := by
  rw [Complex.closure_setOfPred_lt_im] at hz
  have him : z.im = 0 := le_antisymm (not_lt.mp hzH) hz
  exact Complex.ext (by simp) (by simp [him])

/-- The `extendFrom` extension of the primitive to the closed upper half-plane is continuous
there, under integrability at every finite prevertex. -/
theorem continuousOn_extendFrom_schwarzChristoffelPrimitive (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) :
    ContinuousOn (extendFrom upperHalfPlaneSet (schwarzChristoffelPrimitive a e z₀))
      (closure upperHalfPlaneSet) := by
  refine continuousOn_extendFrom subset_rfl fun z hz => ?_
  by_cases hzH : z ∈ upperHalfPlaneSet
  · exact ⟨_, (differentiableOn_schwarzChristoffelPrimitive a e z₀).continuousOn z hzH⟩
  · have hre := ofReal_re_eq_of_mem_closure_of_notMem hz hzH
    rw [← hre]
    exact ⟨_, tendsto_schwarzChristoffelPrimitive_boundary a e z₀ z.re
      (lt_sum_filter_eq_of_forall_apply neg_one_lt_zero hfinite z.re)⟩

/-- The value of the extension at a point of the closed upper half-plane lies in the image of the
open half-plane or on the compactified boundary path. -/
private theorem extendFrom_schwarzChristoffelPrimitive_mem (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) {z : ℂ}
    (hz : z ∈ closure upperHalfPlaneSet) :
    extendFrom upperHalfPlaneSet (schwarzChristoffelPrimitive a e z₀) z ∈
      schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ∪
        range (schwarzChristoffelCompactifiedBoundary a e z₀) := by
  by_cases hzH : z ∈ upperHalfPlaneSet
  · left
    rw [extendFrom_extends (differentiableOn_schwarzChristoffelPrimitive a e z₀).continuousOn z hzH]
    exact mem_image_of_mem _ hzH
  · right
    have hre := ofReal_re_eq_of_mem_closure_of_notMem hz hzH
    refine ⟨(z.re : OnePoint ℝ), ?_⟩
    rw [schwarzChristoffelCompactifiedBoundary_coe]
    refine (extendFrom_eq hz ?_).symm
    rw [← hre]
    exact tendsto_schwarzChristoffelPrimitive_boundary a e z₀ z.re
      (lt_sum_filter_eq_of_forall_apply neg_one_lt_zero hfinite z.re)

/-- Far out in the upper half-plane the primitive stays within any prescribed distance of the
vertex at infinity. -/
theorem exists_forall_dist_schwarzChristoffelPrimitive_le (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hinfty : ∑ i, e i < -1) {ε : ℝ} (hε : 0 < ε) :
    ∃ R, ∀ z ∈ upperHalfPlaneSet, R ≤ ‖z‖ →
      dist (schwarzChristoffelPrimitive a e z₀ z) (schwarzChristoffelVertexAtInfinity a e z₀)
        ≤ ε := by
  have h := (tendsto_schwarzChristoffelPrimitive_atInfinity a e z₀ hinfty).eventually
    (closedBall_mem_nhds _ hε)
  rw [eventually_inf_principal, hasBasis_cobounded_norm.eventually_iff] at h
  obtain ⟨R, -, hR⟩ := h
  exact ⟨R, fun z hz hzR => hR hzR hz⟩

/-- The image of the upper half-plane is covered by the image of a compact piece of the closed
half-plane under the continuous extension, together with a small closed ball about the vertex at
infinity. -/
private theorem exists_image_schwarzChristoffelPrimitive_subset (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hinfty : ∑ i, e i < -1) {ε : ℝ} (hε : 0 < ε) :
    ∃ K ⊆ closure upperHalfPlaneSet, IsCompact K ∧
      schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ⊆
        extendFrom upperHalfPlaneSet (schwarzChristoffelPrimitive a e z₀) '' K ∪
          closedBall (schwarzChristoffelVertexAtInfinity a e z₀) ε := by
  obtain ⟨R, hR⟩ := exists_forall_dist_schwarzChristoffelPrimitive_le a e z₀ hinfty hε
  refine ⟨closure upperHalfPlaneSet ∩ closedBall 0 R, inter_subset_left,
    (isCompact_closedBall 0 R).inter_left isClosed_closure, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  by_cases hzR : R ≤ ‖z‖
  · exact Or.inr (hR z hz hzR)
  · refine Or.inl ⟨z, ⟨subset_closure hz, mem_closedBall_zero_iff.mpr (not_le.mp hzR).le⟩, ?_⟩
    exact extendFrom_extends (differentiableOn_schwarzChristoffelPrimitive a e z₀).continuousOn z hz

/-- **The image of the Schwarz--Christoffel primitive is bounded** when every finite prevertex is
integrable and the total exponent is less than `-1`. -/
theorem isBounded_image_schwarzChristoffelPrimitive (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1) :
    IsBounded (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) := by
  obtain ⟨K, hKH, hK, hsub⟩ :=
    exists_image_schwarzChristoffelPrimitive_subset a e z₀ hinfty one_pos
  refine IsBounded.subset (IsBounded.union ?_ isBounded_closedBall) hsub
  exact (hK.image_of_continuousOn
    ((continuousOn_extendFrom_schwarzChristoffelPrimitive a e z₀ hfinite).mono hKH)).isBounded

/-- **The closure of the image of the Schwarz--Christoffel primitive** is the image together with
the compactified boundary path.  Every point of the path is a limit of the primitive from the
upper half-plane, and conversely every limit point of the image outside it lies on the path. -/
theorem closure_image_schwarzChristoffelPrimitive (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1) :
    closure (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) =
      schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ∪
        range (schwarzChristoffelCompactifiedBoundary a e z₀) := by
  set F := schwarzChristoffelPrimitive a e z₀
  set V := schwarzChristoffelVertexAtInfinity a e z₀
  refine Subset.antisymm (fun w hw => ?_) (union_subset subset_closure ?_)
  · -- For each `ε > 0`, the closure lies in the image, on the path, or within `ε` of `V`.
    have hclose : ∀ ε > 0, w ∈ F '' upperHalfPlaneSet ∪
        range (schwarzChristoffelCompactifiedBoundary a e z₀) ∨ dist w V ≤ ε := by
      intro ε hε
      obtain ⟨K, hKH, hK, hsub⟩ :=
        exists_image_schwarzChristoffelPrimitive_subset a e z₀ hinfty hε
      have hKimage := hK.image_of_continuousOn
        ((continuousOn_extendFrom_schwarzChristoffelPrimitive a e z₀ hfinite).mono hKH)
      have hw' := closure_mono hsub hw
      rw [(hKimage.isClosed.union isClosed_closedBall).closure_eq] at hw'
      rcases hw' with ⟨z, hz, rfl⟩ | hw'
      · exact Or.inl (extendFrom_schwarzChristoffelPrimitive_mem a e z₀ hfinite (hKH hz))
      · exact Or.inr hw'
    by_contra hnot
    have hV : w = V := dist_le_zero.mp <| le_of_forall_pos_le_add fun ε hε => by
      simpa using (hclose ε hε).resolve_left hnot
    exact hnot (Or.inr ⟨∞, by rw [hV, schwarzChristoffelCompactifiedBoundary_infty]⟩)
  · rintro _ ⟨x, rfl⟩
    induction x using OnePoint.rec with
    | infty =>
      rw [schwarzChristoffelCompactifiedBoundary_infty]
      have hne : (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet).NeBot := by
        refine inf_principal_neBot_iff.mpr fun U hU => ?_
        obtain ⟨R, -, hR⟩ := hasBasis_cobounded_norm.mem_iff.mp hU
        have hpos : (0 : ℝ) < |R| + 1 := by positivity
        refine ⟨((|R| + 1 : ℝ) : ℂ) * Complex.I, hR ?_, by simpa using hpos⟩
        rw [Set.mem_ofPred_eq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg hpos.le]
        linarith [le_abs_self R]
      exact mem_closure_of_tendsto (tendsto_schwarzChristoffelPrimitive_atInfinity a e z₀ hinfty)
        (eventually_inf_principal.mpr (Eventually.of_forall fun z hz => mem_image_of_mem F hz))
    | coe x =>
      rw [schwarzChristoffelCompactifiedBoundary_coe]
      have := Real.nhdsWithin_upperHalfPlaneSet_neBot x
      exact mem_closure_of_tendsto (tendsto_schwarzChristoffelPrimitive_boundary a e z₀ x
          (lt_sum_filter_eq_of_forall_apply neg_one_lt_zero hfinite x))
        (eventually_mem_nhdsWithin.mono fun z hz => mem_image_of_mem F hz)

/-- **The frontier of the image of the Schwarz--Christoffel primitive** is the part of the
compactified boundary path that the image does not cover. -/
theorem frontier_image_schwarzChristoffelPrimitive (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1) :
    frontier (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) =
      range (schwarzChristoffelCompactifiedBoundary a e z₀) \
        schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet := by
  have hopen :=
    isOpen_image_schwarzChristoffelPrimitive a e z₀ isOpen_upperHalfPlaneSet subset_rfl
  rw [frontier, closure_image_schwarzChristoffelPrimitive a e z₀ hfinite hinfty,
    hopen.interior_eq, union_sdiff_left]

/-- **The image of the Schwarz--Christoffel primitive misses the unbounded complementary component
of its boundary path**: it lies in the filled hull of that path. -/
theorem image_schwarzChristoffelPrimitive_subset_filledHull (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1) :
    schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ⊆
      filledHull (range (schwarzChristoffelCompactifiedBoundary a e z₀)) := by
  refine subset_filledHull_of_frontier_subset
    (isBounded_image_schwarzChristoffelPrimitive a e z₀ hfinite hinfty) ?_
  rw [frontier_image_schwarzChristoffelPrimitive a e z₀ hfinite hinfty]
  exact sdiff_subset

/-- **The image of the Schwarz--Christoffel primitive lies in the interior of the closed convex
hull of its compactified boundary path.** The filled hull of a nonempty set lies in its closed
convex hull. Since the primitive has open image, that containment automatically improves to
containment in the interior. -/
theorem image_schwarzChristoffelPrimitive_subset_interior_closedConvexHull
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1) :
    schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ⊆
      interior (closedConvexHull ℝ
        (range (schwarzChristoffelCompactifiedBoundary a e z₀))) := by
  let P := range (schwarzChristoffelCompactifiedBoundary a e z₀)
  have hP : P.Nonempty := range_nonempty _
  apply interior_maximal _
    (isOpen_image_schwarzChristoffelPrimitive a e z₀ isOpen_upperHalfPlaneSet subset_rfl)
  exact (image_schwarzChristoffelPrimitive_subset_filledHull a e z₀ hfinite hinfty).trans
    (filledHull_subset_closedConvexHull hP)

/-- **A complementary component of the boundary path that meets the image lies in the image.**
The component is preconnected and avoids the path, which contains the frontier of the open
image. -/
theorem connectedComponentIn_subset_image_schwarzChristoffelPrimitive (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hinfty : ∑ i, e i < -1) {w : ℂ}
    (hw : w ∈ schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)
    (hwP : w ∉ range (schwarzChristoffelCompactifiedBoundary a e z₀)) :
    connectedComponentIn (range (schwarzChristoffelCompactifiedBoundary a e z₀))ᶜ w ⊆
      schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet := by
  refine isPreconnected_connectedComponentIn.subset_of_closure_inter_subset
    (isOpen_image_schwarzChristoffelPrimitive a e z₀ isOpen_upperHalfPlaneSet subset_rfl)
    ⟨w, mem_connectedComponentIn hwP, hw⟩ fun z ⟨hz, hzC⟩ => ?_
  rw [closure_image_schwarzChristoffelPrimitive a e z₀ hfinite hinfty] at hz
  exact hz.resolve_right (connectedComponentIn_subset _ _ hzC)


/-- **A preconnected set avoiding the boundary path and containing the image is the image.** -/
theorem image_schwarzChristoffelPrimitive_eq_of_subset (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1) {W : Set ℂ}
    (hW : IsPreconnected W)
    (hWP : Disjoint W (range (schwarzChristoffelCompactifiedBoundary a e z₀)))
    (hFW : schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ⊆ W) :
    schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet = W := by
  refine hFW.antisymm <| hW.subset_of_closure_inter_subset
    (isOpen_image_schwarzChristoffelPrimitive a e z₀ isOpen_upperHalfPlaneSet subset_rfl) ?_
    fun w ⟨hw, hwW⟩ => ?_
  · have hz₀ : (z₀ : ℂ) ∈ upperHalfPlaneSet := z₀.im_pos
    exact ⟨_, hFW (mem_image_of_mem _ hz₀), mem_image_of_mem _ hz₀⟩
  · rw [closure_image_schwarzChristoffelPrimitive a e z₀ hfinite hinfty] at hw
    exact hw.resolve_right (disjoint_left.mp hWP hwW)

/-- **The Schwarz--Christoffel primitive is proper over the complement of its boundary path.**
The points of the upper half-plane that the primitive sends into a closed set `K` avoiding the
compactified boundary path form a compact set. -/
theorem isCompact_upperHalfPlaneSet_inter_preimage_schwarzChristoffelPrimitive (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hinfty : ∑ i, e i < -1) {K : Set ℂ} (hK : IsClosed K)
    (hKP : Disjoint K (range (schwarzChristoffelCompactifiedBoundary a e z₀))) :
    IsCompact (upperHalfPlaneSet ∩ schwarzChristoffelPrimitive a e z₀ ⁻¹' K) := by
  set F := schwarzChristoffelPrimitive a e z₀
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_of_closure_subset fun z hz => ?_) ?_
  · -- A limit point `z` is either in the upper half-plane, where `F` is continuous, or real,
    -- where `F` tends to a boundary value; the latter would have to lie in `K`.
    have hzH : z ∈ closure upperHalfPlaneSet := closure_mono inter_subset_left hz
    have : (𝓝[upperHalfPlaneSet ∩ F ⁻¹' K] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz
    have hFK : ∀ᶠ w in 𝓝[upperHalfPlaneSet ∩ F ⁻¹' K] z, F w ∈ K :=
      eventually_nhdsWithin_of_forall fun w hw => hw.2
    by_cases hzH' : z ∈ upperHalfPlaneSet
    · have hcont := (differentiableOn_schwarzChristoffelPrimitive a e z₀).continuousOn.continuousAt
        (isOpen_upperHalfPlaneSet.mem_nhds hzH')
      exact ⟨hzH', hK.mem_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hFK⟩
    · have hre := ofReal_re_eq_of_mem_closure_of_notMem hzH hzH'
      have ht := (tendsto_schwarzChristoffelPrimitive_boundary a e z₀ z.re
        (lt_sum_filter_eq_of_forall_apply neg_one_lt_zero hfinite z.re)).mono_left
          (nhdsWithin_mono _ (inter_subset_left (t := F ⁻¹' K)))
      rw [hre] at ht
      exact absurd ⟨(z.re : OnePoint ℝ), schwarzChristoffelCompactifiedBoundary_coe a e z₀ z.re⟩
        (disjoint_left.mp hKP (hK.mem_of_tendsto ht hFK))
  · -- Far out, `F` stays in a neighbourhood of the vertex at infinity that misses `K`.
    have hV : schwarzChristoffelVertexAtInfinity a e z₀ ∉ K := fun hV =>
      disjoint_left.mp hKP hV ⟨∞, schwarzChristoffelCompactifiedBoundary_infty a e z₀⟩
    have h := (tendsto_schwarzChristoffelPrimitive_atInfinity a e z₀ hinfty).eventually
      (hK.isOpen_compl.mem_nhds hV)
    rw [eventually_inf_principal, hasBasis_cobounded_norm.eventually_iff] at h
    obtain ⟨R, -, hR⟩ := h
    refine (isBounded_ball (x := (0 : ℂ)) (r := R)).subset fun z hz => ?_
    rw [mem_ball_zero_iff]
    by_contra hzR
    exact hR (not_lt.mp hzR) hz.1 hz.2

end TauCeti
