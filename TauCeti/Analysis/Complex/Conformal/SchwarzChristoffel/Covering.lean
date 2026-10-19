/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: simple connectivity and the covering and local-homeomorphism predicates occur in the
-- exported statements.
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Covering.Basic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Image
-- Non-public: the inverse function theorem and the covering-space criteria are used only in
-- proofs.
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import TauCeti.Topology.Covering.Proper
import TauCeti.Topology.Homotopy.Covering

/-!
# The Schwarz--Christoffel primitive as a covering map

Let `F = schwarzChristoffelPrimitive a e z₀` and let `P` be the range of the compactified boundary
path `schwarzChristoffelCompactifiedBoundary a e z₀`.  Assume, as in
`TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Image`, that every finite prevertex is
integrable and that the total exponent is less than `-1`.

The primitive has nonvanishing derivative, so on the upper half-plane it is a local
homeomorphism.  It is also proper over the complement of `P`
(`isCompact_upperHalfPlaneSet_inter_preimage_schwarzChristoffelPrimitive`).  A proper local
homeomorphism is a covering map, so `F`, viewed on `ℍ`, is a covering map over the complement of
`P`.

This is the topological core of the argument that the Schwarz--Christoffel map is univalent.  If
a simply connected set `W` avoids `P` and contains the image of the upper half-plane, then the
upper half-plane is a path-connected covering space of `W`.  Such a covering is trivial, so `F` is
injective, and by connectedness its image is all of `W`.  For a convex polygon, the interior of
the polygon is a natural choice of `W`.  To use it, one must know that the image lies inside the
polygon and does not meet its sides.

## Main results

* `TauCeti.isLocalHomeomorphOn_schwarzChristoffelPrimitive` -- the primitive is a local
  homeomorphism on the upper half-plane.
* `TauCeti.isCoveringMapOn_schwarzChristoffelPrimitive_of_isCompact_preimage` -- on `ℍ`, the
  primitive is a covering map over every open set where it is proper.
* `TauCeti.isCoveringMapOn_schwarzChristoffelPrimitive` -- on `ℍ`, the primitive is a covering
  map over the complement of the compactified boundary path.
* `TauCeti.bijOn_schwarzChristoffelPrimitive_of_subset` -- the primitive maps the upper
  half-plane bijectively onto every simply connected set that avoids the boundary path and
  contains the image.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
* O. Forster, *Lectures on Riemann Surfaces*, Section 4.
-/

public section

noncomputable section

open Set Topology UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **The Schwarz--Christoffel primitive is a local homeomorphism on the upper half-plane.**
Its derivative is nonzero throughout this domain. -/
theorem isLocalHomeomorphOn_schwarzChristoffelPrimitive (a e : ι → ℝ) (z₀ : UpperHalfPlane) :
    IsLocalHomeomorphOn (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet := by
  refine IsLocalHomeomorphOn.mk _ _ fun z hz => ?_
  have hstrict := ((differentiableOn_schwarzChristoffelPrimitive a e z₀).analyticAt
    (isOpen_upperHalfPlaneSet.mem_nhds hz)).hasStrictDerivAt
  have hderiv : deriv (schwarzChristoffelPrimitive a e z₀) z ≠ 0 := by
    rw [deriv_schwarzChristoffelPrimitive a e z₀ hz]
    exact schwarzChristoffelIntegrand_ne_zero a e hz
  have hf := hstrict.hasStrictFDerivAt_equiv hderiv
  exact ⟨hf.toOpenPartialHomeomorph _, hf.mem_toOpenPartialHomeomorph_source, fun w _ => by
    rw [hf.toOpenPartialHomeomorph_coe]⟩

/-- **The Schwarz--Christoffel primitive is a covering map over an open set where it is
proper.**  Viewed as a map on `ℍ`, the primitive is a covering map over every open set `U` such
that the points of the upper half-plane sent into any compact subset of `U` form a compact set.
No assumption on the exponents is needed: the primitive is always a local homeomorphism. -/
theorem isCoveringMapOn_schwarzChristoffelPrimitive_of_isCompact_preimage (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) {U : Set ℂ} (hU : IsOpen U)
    (hK : ∀ K ⊆ U, IsCompact K →
      IsCompact (upperHalfPlaneSet ∩ schwarzChristoffelPrimitive a e z₀ ⁻¹' K)) :
    IsCoveringMapOn (fun τ : ℍ => schwarzChristoffelPrimitive a e z₀ τ) U := by
  set F := schwarzChristoffelPrimitive a e z₀
  have hloc : IsLocalHomeomorph fun τ : ℍ => F τ :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr <|
      (isLocalHomeomorphOn_schwarzChristoffelPrimitive a e z₀).comp
        isOpenEmbedding_coe.isLocalHomeomorph.isLocalHomeomorphOn fun τ _ => τ.im_pos
  refine IsCoveringMapOn.of_isLocalHomeomorph_of_isCompact_preimage hU hloc.isLocalHomeomorphOn
    fun K hKU hK' => ?_
  rw [isOpenEmbedding_coe.isEmbedding.isCompact_iff]
  have himage : ((↑) : ℍ → ℂ) '' ((fun τ : ℍ => F τ) ⁻¹' K) = upperHalfPlaneSet ∩ F ⁻¹' K := by
    ext z
    refine ⟨?_, fun ⟨hz, hzK⟩ => ⟨⟨z, hz⟩, hzK, rfl⟩⟩
    rintro ⟨τ, hτ, rfl⟩
    exact ⟨τ.im_pos, hτ⟩
  rw [himage]
  exact hK K hKU hK'

/-- **The Schwarz--Christoffel primitive is a covering map off its boundary path.**  Viewed as a
map on `ℍ`, the primitive is a covering map over the complement of the compactified boundary
path, provided every finite prevertex is integrable and the total exponent is less than `-1`. -/
theorem isCoveringMapOn_schwarzChristoffelPrimitive (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1) :
    IsCoveringMapOn (fun τ : ℍ => schwarzChristoffelPrimitive a e z₀ τ)
      (range (schwarzChristoffelCompactifiedBoundary a e z₀))ᶜ := by
  have hP : IsClosed (range (schwarzChristoffelCompactifiedBoundary a e z₀)) :=
    (isCompact_range
      (continuous_schwarzChristoffelCompactifiedBoundary a e z₀ hfinite hinfty)).isClosed
  exact isCoveringMapOn_schwarzChristoffelPrimitive_of_isCompact_preimage a e z₀ hP.isOpen_compl
    fun K hKP hK => isCompact_upperHalfPlaneSet_inter_preimage_schwarzChristoffelPrimitive a e z₀
      hfinite hinfty hK.isClosed (subset_compl_iff_disjoint_right.mp hKP)

/-- **The Schwarz--Christoffel primitive is a bijection onto a simply connected region avoiding
its boundary path.**  If the image of the upper half-plane lies in a simply connected set `W`
disjoint from the compactified boundary path, then the primitive maps the upper half-plane
bijectively onto `W`. -/
theorem bijOn_schwarzChristoffelPrimitive_of_subset (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1) {W : Set ℂ}
    [SimplyConnectedSpace W]
    (hWP : Disjoint W (range (schwarzChristoffelCompactifiedBoundary a e z₀)))
    (hFW : schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ⊆ W) :
    BijOn (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet W := by
  have hW : IsPreconnected W := isPreconnected_iff_preconnectedSpace.mpr inferInstance
  have himage := image_schwarzChristoffelPrimitive_eq_of_subset a e z₀ hfinite hinfty hW hWP hFW
  refine ⟨himage ▸ mapsTo_image _ _, fun z hz w hw hzw => ?_, himage ▸ surjOn_image _ _⟩
  -- The path-connected `ℍ` covers the simply connected `W`, so the covering is trivial.
  exact congrArg ((↑) : ℍ → ℂ) <|
    (isCoveringMapOn_schwarzChristoffelPrimitive a e z₀ hfinite hinfty).injective_of_range_subset
      (subset_compl_iff_disjoint_right.mpr hWP)
      (range_subset_iff.mpr fun τ => hFW (mem_image_of_mem _ τ.im_pos))
      (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) hzw

end TauCeti
