/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.SimpleBoundary
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Covering
import TauCeti.Data.Set.Restrict
import TauCeti.Topology.Homotopy.Monodromy.Basic
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Finite sheet count of the Schwarz--Christoffel primitive

When the Schwarz--Christoffel primitive has an integrable boundary at every finite prevertex
and at infinity, its restriction over the complement of the compactified boundary path is a
proper local homeomorphism. Its fibers there are compact and discrete, hence finite. The
covering-space monodromy then identifies the fibers over points joined by a path in that
complement. In particular the number of preimages is constant on each path component.

For a simple polygonal boundary, the image of the primitive is one such component. Its finite
sheet count is the degree that a subsequent univalence argument must show equals one.

## Main results

* `TauCeti.finite_schwarzChristoffelPrimitive_fiber`: a fiber away from the boundary is finite.
* `TauCeti.ncard_schwarzChristoffelPrimitive_fiber_eq_of_joinedIn`: paths in the complement
  preserve fiber cardinality.
* `TauCeti.exists_constant_schwarzChristoffelPrimitive_fiber_ncard`: a simple boundary yields
  one positive finite sheet count throughout the image component.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* O. Forster, *Lectures on Riemann Surfaces*, Section 4.
-/

public section

noncomputable section

open Set UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- A fiber of the Schwarz--Christoffel primitive over a point outside its compactified
boundary path is finite. -/
theorem finite_schwarzChristoffelPrimitive_fiber (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1)
    {w : ℂ} (hw : w ∉ range (schwarzChristoffelCompactifiedBoundary a e z₀)) :
    (Set.preimage (fun τ : ℍ => schwarzChristoffelPrimitive a e z₀ τ) {w}).Finite := by
  let F : ℍ → ℂ := fun τ => schwarzChristoffelPrimitive a e z₀ τ
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
    exact isCompact_upperHalfPlaneSet_inter_preimage_schwarzChristoffelPrimitive
      a e z₀ hfinite hinfty isClosed_singleton
      (disjoint_singleton_left.mpr hw)
  have hlocal : IsLocalHomeomorph F :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr <|
      (isLocalHomeomorphOn_schwarzChristoffelPrimitive a e z₀).comp
        isOpenEmbedding_coe.isLocalHomeomorph.isLocalHomeomorphOn fun τ _ => τ.im_pos
  exact hcompact.finite
    (IsDiscrete.of_openPartialHomeomorph F subset_rfl fun τ _ => by
      obtain ⟨φ, hφ, hφF⟩ := hlocal τ
      exact ⟨φ, hφ, hφF.symm⟩)

/-- The number of preimages of the Schwarz--Christoffel primitive is constant along paths
avoiding its compactified boundary. Both fibers are finite, so this is an equality of ordinary
natural-number counts. -/
theorem ncard_schwarzChristoffelPrimitive_fiber_eq_of_joinedIn
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1)
    {w₁ w₂ : ℂ} (hjoined : JoinedIn
      (range (schwarzChristoffelCompactifiedBoundary a e z₀))ᶜ w₁ w₂) :
    ((fun τ : ℍ => schwarzChristoffelPrimitive a e z₀ τ) ⁻¹' {w₁}).ncard =
      ((fun τ : ℍ => schwarzChristoffelPrimitive a e z₀ τ) ⁻¹' {w₂}).ncard := by
  let P := range (schwarzChristoffelCompactifiedBoundary a e z₀)
  let F : ℍ → ℂ := fun τ => schwarzChristoffelPrimitive a e z₀ τ
  let u : ↥(Pᶜ) := ⟨w₁, hjoined.source_mem⟩
  let v : ↥(Pᶜ) := ⟨w₂, hjoined.target_mem⟩
  have hcov : IsCoveringMap (Pᶜ.restrictPreimage F) := by
    have h := isCoveringMapOn_schwarzChristoffelPrimitive a e z₀ hfinite hinfty
    exact h.isCoveringMap_restrictPreimage
  let γ : Path u v := hjoined.joined_subtype.somePath
  have hcard := Nat.card_congr (coveringFiberEquiv hcov (Path.Homotopic.Quotient.mk γ))
  calc
    (F ⁻¹' {w₁}).ncard = ((Pᶜ.restrictPreimage F) ⁻¹' {u}).ncard :=
      (ncard_fiber_restrictPreimage F Pᶜ u).symm
    _ = ((Pᶜ.restrictPreimage F) ⁻¹' {v}).ncard := by
      simpa only [Nat.card_coe_set_eq] using hcard
    _ = (F ⁻¹' {w₂}).ncard := ncard_fiber_restrictPreimage F Pᶜ v

/-- If the compactified Schwarz--Christoffel boundary is simple, the primitive has a positive,
finite, constant number of preimages at every point of its image. -/
theorem exists_constant_schwarzChristoffelPrimitive_fiber_ncard (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i)
    (hinfty : ∑ i, e i < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀)) :
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
  have hdisj := disjoint_image_schwarzChristoffelPrimitive_range a e z₀ hfinite hinfty hinj
  have hw₀ : F z₀ ∉ range (schwarzChristoffelCompactifiedBoundary a e z₀) :=
    Set.disjoint_left.mp hdisj (mem_image_of_mem _ z₀.im_pos)
  have hfin₀ : (F ⁻¹' {F z₀}).Finite :=
    finite_schwarzChristoffelPrimitive_fiber a e z₀ hfinite hinfty hw₀
  refine ⟨(F ⁻¹' {F z₀}).ncard,
    (Set.ncard_pos hfin₀).mpr ⟨z₀, rfl⟩, fun w hw => ?_⟩
  have hjoined : JoinedIn U (F z₀) w := hUpath.joinedIn _ (mem_image_of_mem _ z₀.im_pos) _ hw
  have hjoinedP : JoinedIn
      (range (schwarzChristoffelCompactifiedBoundary a e z₀))ᶜ (F z₀) w :=
    hjoined.mono (Set.subset_compl_iff_disjoint_right.mpr hdisj)
  exact (ncard_schwarzChristoffelPrimitive_fiber_eq_of_joinedIn
    a e z₀ hfinite hinfty hjoinedP).symm

end TauCeti
