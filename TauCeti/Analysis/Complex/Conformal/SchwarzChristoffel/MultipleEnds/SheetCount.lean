/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.MultipleEnds.FiniteBoundary
import TauCeti.Data.Set.Restrict
import TauCeti.Topology.Homotopy.Monodromy.Basic
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Finite sheet count of the Schwarz--Christoffel primitive

When every finite prevertex has total exponent at least `-1`, the restriction of the
Schwarz--Christoffel primitive over the complement of its finite boundary trace is a proper local
homeomorphism. Its fibers there are compact and discrete, hence finite. Covering-space monodromy
identifies the fibers over points joined by a path in that complement, so the number of preimages
is constant on each path component. Any number of logarithmic ends is allowed, and the total
exponent is unrestricted.

If the image avoids the finite boundary trace, it has one positive finite sheet count throughout.
Showing this count equals one establishes global univalence.

## Main results

* `TauCeti.finite_schwarzChristoffelPrimitive_fiber`: a fiber away from the boundary is finite.
* `TauCeti.ncard_schwarzChristoffelPrimitive_fiber_eq_of_joinedIn`: paths in the complement
  preserve fiber cardinality.
* `TauCeti.exists_constant_schwarzChristoffelPrimitive_fiber_ncard`: boundary avoidance yields
  one positive finite sheet count throughout the image.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* O. Forster, *Lectures on Riemann Surfaces*, Section 4.
-/

public section

noncomputable section

open Set UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- A fiber outside the finite boundary trace is finite, including when several prevertices
are logarithmic ends. -/
theorem finite_schwarzChristoffelPrimitive_fiber (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i)
    {w : ℂ} (hw : w ∉ schwarzChristoffelFiniteBoundary a e z₀) :
    (Set.preimage (fun τ : ℍ => schwarzChristoffelPrimitive a e z₀ τ) {w}).Finite := by
  let F : ℍ → ℂ := fun τ => schwarzChristoffelPrimitive a e z₀ τ
  have hWB : Disjoint (((↑) : ℂ → OnePoint ℂ) '' {w})
      (range (schwarzChristoffelSphereBoundary a e z₀)) := by
    rw [disjoint_left]
    rintro _ ⟨v, hv, rfl⟩ hvB
    rw [mem_singleton_iff] at hv
    subst v
    exact hw (by rwa [schwarzChristoffelFiniteBoundary_eq_preimage_range a e z₀ hfinite])
  have hplane :=
  isCompact_upperHalfPlaneSet_inter_preimage_schwarzChristoffelPrimitive_of_neg_one_le_prevertex_sum
    a e z₀ hfinite isCompact_singleton hWB
  have hcompact : IsCompact (F ⁻¹' {w}) := by
    rw [isOpenEmbedding_coe.isEmbedding.isCompact_iff]
    have himage : ((↑) : ℍ → ℂ) '' (F ⁻¹' {w}) =
        upperHalfPlaneSet ∩ (schwarzChristoffelPrimitive a e z₀) ⁻¹' {w} := by
      ext z
      constructor
      · rintro ⟨τ, hτ, rfl⟩
        exact ⟨τ.im_pos, hτ⟩
      · rintro ⟨hz, hzw⟩
        exact ⟨⟨z, hz⟩, hzw, rfl⟩
    rw [himage]
    exact hplane
  have hlocal : IsLocalHomeomorph F :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr <|
      (isLocalHomeomorphOn_schwarzChristoffelPrimitive a e z₀).comp
        isOpenEmbedding_coe.isLocalHomeomorph.isLocalHomeomorphOn fun τ _ => τ.im_pos
  exact hcompact.finite
    (IsDiscrete.of_openPartialHomeomorph F subset_rfl fun τ _ => by
      obtain ⟨φ, hφ, hφF⟩ := hlocal τ
      exact ⟨φ, hφ, hφF.symm⟩)

/-- Paths avoiding the finite boundary trace preserve the number of preimages. Both fibers
are finite, so these are ordinary natural-number counts even with several logarithmic ends. -/
theorem ncard_schwarzChristoffelPrimitive_fiber_eq_of_joinedIn
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i)
    {w₁ w₂ : ℂ} (hjoined : JoinedIn
      (schwarzChristoffelFiniteBoundary a e z₀)ᶜ w₁ w₂) :
    ((fun τ : ℍ => schwarzChristoffelPrimitive a e z₀ τ) ⁻¹' {w₁}).ncard =
      ((fun τ : ℍ => schwarzChristoffelPrimitive a e z₀ τ) ⁻¹' {w₂}).ncard := by
  let P := schwarzChristoffelFiniteBoundary a e z₀
  let F : ℍ → ℂ := fun τ => schwarzChristoffelPrimitive a e z₀ τ
  let u : ↥(Pᶜ) := ⟨w₁, hjoined.source_mem⟩
  let v : ↥(Pᶜ) := ⟨w₂, hjoined.target_mem⟩
  have hcov : IsCoveringMap (Pᶜ.restrictPreimage F) := by
    have h := isCoveringMapOn_schwarzChristoffelPrimitive_of_neg_one_le_prevertex_sum
      a e z₀ hfinite
    rw [← schwarzChristoffelFiniteBoundary_eq_preimage_range a e z₀ hfinite] at h
    exact h.isCoveringMap_restrictPreimage
  let γ : Path u v := hjoined.joined_subtype.somePath
  have hcard := Nat.card_congr (coveringFiberEquiv hcov (Path.Homotopic.Quotient.mk γ))
  calc
    (F ⁻¹' {w₁}).ncard = ((Pᶜ.restrictPreimage F) ⁻¹' {u}).ncard :=
      (ncard_fiber_restrictPreimage F Pᶜ u).symm
    _ = ((Pᶜ.restrictPreimage F) ⁻¹' {v}).ncard := by
      simpa only [Nat.card_coe_set_eq] using hcard
    _ = (F ⁻¹' {w₂}).ncard := ncard_fiber_restrictPreimage F Pᶜ v

/-- If the image avoids the finite boundary trace, the primitive has a positive finite
constant number of preimages throughout its image. No boundary simplicity is required. -/
theorem exists_constant_schwarzChristoffelPrimitive_fiber_ncard (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i)
    (havoid : Disjoint (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)
      (schwarzChristoffelFiniteBoundary a e z₀)) :
    ∃ d : ℕ, 0 < d ∧ ∀ w ∈ schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet,
      ((fun τ : ℍ => schwarzChristoffelPrimitive a e z₀ τ) ⁻¹' {w}).ncard = d := by
  let F : ℍ → ℂ := fun τ => schwarzChristoffelPrimitive a e z₀ τ
  let U := schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet
  have hUopen : IsOpen U :=
    isOpen_image_schwarzChristoffelPrimitive a e z₀ isOpen_upperHalfPlaneSet subset_rfl
  have hUpre : IsPreconnected U :=
    (convex_halfSpace_im_gt 0).isPreconnected.image _
      (differentiableOn_schwarzChristoffelPrimitive a e z₀).continuousOn
  have hUconn : IsConnected U :=
    ⟨⟨schwarzChristoffelPrimitive a e z₀ z₀, mem_image_of_mem _ z₀.im_pos⟩, hUpre⟩
  have hUpath : IsPathConnected U :=
    hUopen.isConnected_iff_isPathConnected.mp hUconn
  have hw₀ : F z₀ ∉ schwarzChristoffelFiniteBoundary a e z₀ :=
    Set.disjoint_left.mp havoid (mem_image_of_mem _ z₀.im_pos)
  have hfin₀ : (F ⁻¹' {F z₀}).Finite :=
    finite_schwarzChristoffelPrimitive_fiber a e z₀ hfinite hw₀
  refine ⟨(F ⁻¹' {F z₀}).ncard,
    (Set.ncard_pos hfin₀).mpr ⟨z₀, rfl⟩, fun w hw => ?_⟩
  have hjoined : JoinedIn U (F z₀) w := hUpath.joinedIn _ (mem_image_of_mem _ z₀.im_pos) _ hw
  have hjoinedP : JoinedIn
      (schwarzChristoffelFiniteBoundary a e z₀)ᶜ (F z₀) w :=
    hjoined.mono (Set.subset_compl_iff_disjoint_right.mpr havoid)
  exact (ncard_schwarzChristoffelPrimitive_fiber_eq_of_joinedIn
    a e z₀ hfinite hjoinedP).symm

end TauCeti
