/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.MultipleEnds.Univalence
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.RegularEdge

/-!
# A single boundary sheet for Schwarz--Christoffel maps with several ends

A finite boundary value with just one spherical boundary parameter confines all nearby
interior preimages to that parameter, provided the value is not attained in the interior.
At a regular edge, holomorphic continuation is locally injective, so this confinement
produces a globally singleton interior fiber.

If the image avoids the finite boundary trace, constancy of the sheet count then makes the
primitive globally injective and a bijection onto a complementary component. Only one
regular boundary value must have a unique parameter. In particular, logarithmic ends may
all map to infinity, and other boundary values may have several parameters. Boundary
avoidance is still necessary and is not inferred from the local edge geometry.

Local injectivity comes from `exists_injOn_schwarzChristoffelPrimitive_continuation` in
`TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.RegularEdge`.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Complex Filter Metric Set Topology UpperHalfPlane
open scoped OnePoint

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- Near a finite boundary value with a unique spherical boundary parameter, all interior
preimages lie in any prescribed neighborhood of that parameter. The chosen boundary value
must not be attained in the interior; other boundary values may be attained there. -/
theorem exists_ball_preimage_schwarzChristoffelPrimitive_subset_of_unique_boundary_value
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i) (x : ℝ)
    (hx : -1 < ∑ i with a i = x, e i)
    (hnot : schwarzChristoffelBoundary a e z₀ x ∉
      schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)
    (hunique : ∀ t : OnePoint ℝ, schwarzChristoffelSphereBoundary a e z₀ t =
      schwarzChristoffelSphereBoundary a e z₀ (x : OnePoint ℝ) → t = (x : OnePoint ℝ))
    {U : Set ℂ} (hU : IsOpen U) (hxU : (x : ℂ) ∈ U) :
    ∃ ε > 0, ∀ z ∈ upperHalfPlaneSet,
      schwarzChristoffelPrimitive a e z₀ z ∈ ball (schwarzChristoffelBoundary a e z₀ x) ε →
        z ∈ U := by
  let C := closure (((↑) : ℂ → OnePoint ℂ) '' upperHalfPlaneSet)
  let E := schwarzChristoffelSphereExtension a e z₀
  let b : OnePoint ℂ := schwarzChristoffelBoundary a e z₀ x
  let : CompactSpace C := isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  have hcont : Continuous (C.domRestrict E) :=
    (continuousOn_schwarzChristoffelSphereExtension a e z₀ hfinite).domRestrict
  have hBx : schwarzChristoffelSphereBoundary a e z₀ (x : OnePoint ℝ) = b :=
    schwarzChristoffelSphereBoundary_coe_of_exponent_sum_gt_neg_one a e z₀ x hx
  -- Interior points are excluded by `hnot`; boundary points are determined by `hunique`.
  have hfiber (v : C) (hv : C.domRestrict E v = b) :
      (v : OnePoint ℂ) = ((x : ℂ) : OnePoint ℂ) := by
    rcases v with ⟨v, hvC⟩
    induction v using OnePoint.rec with
    | infty =>
      have hB : schwarzChristoffelSphereBoundary a e z₀ ∞ = b := by
        simpa only [domRestrict_apply, E, schwarzChristoffelSphereBoundary_apply,
          OnePoint.map_infty] using hv
      exact False.elim (OnePoint.infty_ne_coe x (hunique ∞ (hB.trans hBx.symm)))
    | coe z =>
      have hz : 0 ≤ z.im := by
        simpa [C, closure_coe_image_upperHalfPlaneSet] using hvC
      rcases lt_or_eq_of_le hz with hz | hz
      · have hF : schwarzChristoffelPrimitive a e z₀ z =
            schwarzChristoffelBoundary a e z₀ x := by
          apply OnePoint.coe_injective
          simpa only [domRestrict_apply, E, b,
            schwarzChristoffelSphereExtension_coe_of_im_pos a e z₀ hz] using hv
        exact False.elim (hnot ⟨z, hz, hF⟩)
      · have hre : (z.re : ℂ) = z := by
          exact Complex.ext (by simp) (by simp [← hz])
        have hB : schwarzChristoffelSphereBoundary a e z₀ (z.re : OnePoint ℝ) = b := by
          simpa only [domRestrict_apply, E, schwarzChristoffelSphereBoundary_apply,
            OnePoint.map_some, hre] using hv
        have heq := OnePoint.coe_injective
          (hunique (z.re : OnePoint ℝ) (hB.trans hBx.symm))
        exact congrArg ((↑) : ℂ → OnePoint ℂ) ((congrArg ofReal heq).symm.trans hre).symm
  -- Compactness makes the extension a closed map. Its unique fiber controls all nearby fibers.
  have hnear : ∀ᶠ w in 𝓝 b, ∀ v : C, C.domRestrict E v = w →
      (v : OnePoint ℂ) ∈ ((↑) : ℂ → OnePoint ℂ) '' U := by
    apply hcont.isClosedMap.eventually_nhds_fiber
    intro v hv
    have hvU : (v : OnePoint ℂ) ∈ ((↑) : ℂ → OnePoint ℂ) '' U := by
      rw [hfiber v hv]
      exact ⟨x, hxU, rfl⟩
    exact ((OnePoint.isOpenEmbedding_coe.isOpenMap U hU).preimage
      continuous_subtype_val).mem_nhds hvU
  have hnearC := OnePoint.continuous_coe.continuousAt.tendsto.eventually hnear
  obtain ⟨ε, hε, hεnear⟩ := Metric.eventually_nhds_iff.mp hnearC
  refine ⟨ε, hε, fun z hz hzball => ?_⟩
  have hzC : (z : OnePoint ℂ) ∈ C := subset_closure ⟨z, hz, rfl⟩
  have hzU := hεnear hzball (⟨z, hzC⟩ : C)
    (schwarzChristoffelSphereExtension_coe_of_im_pos a e z₀ hz)
  simpa using hzU

/-- A regular boundary value with one spherical boundary parameter and no interior preimage
produces a globally singleton interior fiber. No global boundary avoidance or injectivity is
required. Logarithmic ends elsewhere are allowed. -/
theorem exists_schwarzChristoffelPrimitive_fiber_eq_singleton_of_unique_boundary_value
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i) {p q x : ℝ}
    (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q) (hx : x ∈ Ioo p q)
    (hnot : schwarzChristoffelBoundary a e z₀ x ∉
      schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)
    (hunique : ∀ t : OnePoint ℝ, schwarzChristoffelSphereBoundary a e z₀ t =
      schwarzChristoffelSphereBoundary a e z₀ (x : OnePoint ℝ) → t = (x : OnePoint ℝ)) :
    ∃ τ : ℍ, ((fun z : ℍ => schwarzChristoffelPrimitive a e z₀ z) ⁻¹'
      {schwarzChristoffelPrimitive a e z₀ τ}) = {τ} := by
  have hxsum := sum_filter_eq_zero_of_mem_Ioo a e ha hx
  have hxint : -1 < ∑ i with a i = x, e i := by rw [hxsum]; norm_num
  obtain ⟨U, hUopen, hxU, G, hGF, hGinj, _, _⟩ :=
    exists_injOn_schwarzChristoffelPrimitive_continuation a e z₀ ha hx
  obtain ⟨ε, hε, hnear⟩ :=
    exists_ball_preimage_schwarzChristoffelPrimitive_subset_of_unique_boundary_value
      a e z₀ hfinite x hxint hnot hunique hUopen hxU
  have hclose : schwarzChristoffelBoundary a e z₀ x ∈
      closure (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) := by
    rw [closure_image_schwarzChristoffelPrimitive_eq_union_finiteBoundary a e z₀ hfinite]
    exact Or.inr ((mem_schwarzChristoffelFiniteBoundary a e z₀ _).mpr
      (Or.inl ⟨x, hxint, rfl⟩))
  obtain ⟨_, hwball, z, hz, rfl⟩ :=
    _root_.mem_closure_iff.mp hclose _ isOpen_ball (mem_ball_self hε)
  refine ⟨⟨z, hz⟩, ?_⟩
  ext τ
  simp only [mem_preimage, mem_singleton_iff]
  constructor
  · intro hτ
    have hzU := hnear z hz hwball
    have hτU := hnear τ τ.im_pos (hτ ▸ hwball)
    apply UpperHalfPlane.ext_iff.mpr
    apply hGinj hτU hzU
    rw [hGF ⟨hτU, τ.im_pos⟩, hGF ⟨hzU, hz⟩]
    exact hτ
  · rintro rfl
    rfl

/-- **One boundary sheet implies global univalence.** If the image avoids its finite boundary
trace, a single uniquely parametrized regular boundary value forces injectivity throughout
the upper half-plane. The spherical boundary need not be injective at any other value. -/
theorem injOn_schwarzChristoffelPrimitive_of_unique_boundary_value
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i)
    (havoid : Disjoint (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)
      (schwarzChristoffelFiniteBoundary a e z₀)) {p q x : ℝ}
    (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q) (hx : x ∈ Ioo p q)
    (hunique : ∀ t : OnePoint ℝ, schwarzChristoffelSphereBoundary a e z₀ t =
      schwarzChristoffelSphereBoundary a e z₀ (x : OnePoint ℝ) → t = (x : OnePoint ℝ)) :
    InjOn (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet := by
  have hxsum := sum_filter_eq_zero_of_mem_Ioo a e ha hx
  have hxB : schwarzChristoffelBoundary a e z₀ x ∈
      schwarzChristoffelFiniteBoundary a e z₀ :=
    (mem_schwarzChristoffelFiniteBoundary a e z₀ _).mpr
      (Or.inl ⟨x, by rw [hxsum]; norm_num, rfl⟩)
  obtain ⟨τ, hτ⟩ :=
    exists_schwarzChristoffelPrimitive_fiber_eq_singleton_of_unique_boundary_value a e z₀
      hfinite ha hx (fun hw => disjoint_left.mp havoid hw hxB) hunique
  exact (injOn_schwarzChristoffelPrimitive_iff_fiber_ncard_eq_one a e z₀ hfinite havoid
    (mem_image_of_mem _ τ.im_pos)).mpr (by rw [hτ, ncard_singleton])

/-- **The component mapping theorem from one boundary sheet.** Under boundary avoidance,
one uniquely parametrized regular boundary value makes the primitive a bijection onto the
complementary component of the finite boundary trace containing its base-point image.
Neither simple connectivity of that component nor global boundary injectivity is assumed. -/
theorem bijOn_schwarzChristoffelPrimitive_connectedComponentIn_of_unique_boundary_value
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i)
    (havoid : Disjoint (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)
      (schwarzChristoffelFiniteBoundary a e z₀)) {p q x : ℝ}
    (ha : ∀ i, e i ≠ 0 → a i ∉ Ioo p q) (hx : x ∈ Ioo p q)
    (hunique : ∀ t : OnePoint ℝ, schwarzChristoffelSphereBoundary a e z₀ t =
      schwarzChristoffelSphereBoundary a e z₀ (x : OnePoint ℝ) → t = (x : OnePoint ℝ)) :
    BijOn (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet
      (connectedComponentIn (schwarzChristoffelFiniteBoundary a e z₀)ᶜ
        (schwarzChristoffelPrimitive a e z₀ z₀)) := by
  let F := schwarzChristoffelPrimitive a e z₀
  let W := connectedComponentIn (schwarzChristoffelFiniteBoundary a e z₀)ᶜ (F z₀)
  have hconn : IsPreconnected (F '' upperHalfPlaneSet) :=
    (convex_halfSpace_im_gt 0).isPreconnected.image _
      (differentiableOn_schwarzChristoffelPrimitive a e z₀).continuousOn
  have hFW : F '' upperHalfPlaneSet ⊆ W :=
    hconn.subset_connectedComponentIn (mem_image_of_mem _ z₀.im_pos)
      (subset_compl_iff_disjoint_right.mpr havoid)
  have hxB : schwarzChristoffelBoundary a e z₀ x ∈
      schwarzChristoffelFiniteBoundary a e z₀ :=
    (mem_schwarzChristoffelFiniteBoundary a e z₀ _).mpr
      (Or.inl ⟨x, by rw [sum_filter_eq_zero_of_mem_Ioo a e ha hx]; norm_num, rfl⟩)
  obtain ⟨τ, hτ⟩ :=
    exists_schwarzChristoffelPrimitive_fiber_eq_singleton_of_unique_boundary_value a e z₀
      hfinite ha hx (fun hw => disjoint_left.mp havoid hw hxB) hunique
  exact (bijOn_schwarzChristoffelPrimitive_iff_fiber_ncard_eq_one a e z₀ hfinite
    isPreconnected_connectedComponentIn
    (disjoint_compl_left.mono_left (connectedComponentIn_subset _ _)) hFW
    (hFW (mem_image_of_mem _ τ.im_pos))).mpr (by rw [hτ, ncard_singleton])

end TauCeti
