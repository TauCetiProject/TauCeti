/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.SphericalExtension
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Covering
import TauCeti.Topology.Homotopy.Covering

/-!
# Schwarz--Christoffel coverings with several ends

If every finite prevertex has total exponent at least `-1`, the Schwarz--Christoffel
primitive has a continuous extension to the compactified closed upper half-plane.
Logarithmic prevertices map to infinity; they need not be distinct as sphere-valued
boundary points. Compactness of this extension makes the primitive proper over the
complement of its finite spherical boundary values, and hence a covering map there.

Consequently, a simply connected region avoiding those boundary values and containing
the image is mapped onto bijectively. This is the covering criterion for polygonal images
with several logarithmic ends. It does not assume boundary simplicity, impose a bound on
the total exponent, or assert that the image avoids its boundary values automatically.

The proof uses `schwarzChristoffelSphereExtension` and the existing local-homeomorphism
criterion for the primitive, rather than separate estimates near each end.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
* O. Forster, *Lectures on Riemann Surfaces*, Section 4.
-/

public section

open Complex Set Topology UpperHalfPlane
open scoped OnePoint

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The spherical closure of the image consists of the image together with the spherical
boundary values. Logarithmic ends, including several parameters mapping to infinity, are
allowed. -/
theorem closure_coe_image_schwarzChristoffelPrimitive (a e : ι → ℝ)
    (z₀ : UpperHalfPlane) (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i) :
    closure (((↑) : ℂ → OnePoint ℂ) ''
      (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)) =
      ((↑) : ℂ → OnePoint ℂ) ''
        (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) ∪
      range (schwarzChristoffelSphereBoundary a e z₀) := by
  let E := schwarzChristoffelSphereExtension a e z₀
  have hext : E '' (((↑) : ℂ → OnePoint ℂ) '' upperHalfPlaneSet) =
      ((↑) : ℂ → OnePoint ℂ) ''
        (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) := by
    ext w
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨_, ⟨z, hz, rfl⟩, (schwarzChristoffelSphereExtension_coe_of_im_pos a e z₀ hz).symm⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, ⟨z, hz, rfl⟩, schwarzChristoffelSphereExtension_coe_of_im_pos a e z₀ hz⟩
  rw [← hext, ← image_closure_of_isCompact isClosed_closure.isCompact
    (continuousOn_schwarzChristoffelSphereExtension a e z₀ hfinite), hext]
  rw [closure_coe_image_upperHalfPlaneSet]
  apply Subset.antisymm
  · rintro w ⟨x, hx, rfl⟩
    rcases hx with rfl | ⟨z, hz, rfl⟩
    · right
      exact ⟨∞, by simp [schwarzChristoffelSphereBoundary_apply]⟩
    · have hz' : 0 ≤ z.im := hz
      rcases lt_or_eq_of_le hz' with hz | hz
      · left
        exact ⟨_, ⟨z, hz, rfl⟩, (schwarzChristoffelSphereExtension_coe_of_im_pos a e z₀ hz).symm⟩
      · right
        have hre : (z.re : ℂ) = z := by
          apply Complex.ext <;> simp [← hz]
        exact ⟨z.re, by simp [schwarzChristoffelSphereBoundary_apply, hre]⟩
  · intro w hw
    rcases hw with ⟨_, ⟨z, hz, rfl⟩, rfl⟩ | ⟨x, rfl⟩
    · exact ⟨z, mem_insert_of_mem _ ⟨z, (le_of_lt hz : 0 ≤ z.im), rfl⟩,
        schwarzChristoffelSphereExtension_coe_of_im_pos a e z₀ hz⟩
    · induction x using OnePoint.rec with
      | infty => exact ⟨∞, mem_insert _ _, by simp [schwarzChristoffelSphereBoundary_apply]⟩
      | coe p =>
        exact ⟨(p : ℂ), mem_insert_of_mem _ ⟨(p : ℂ), by simp, rfl⟩,
          by simp [schwarzChristoffelSphereBoundary_apply]⟩

/-- Compact sets avoiding the finite spherical boundary values have compact preimages in
the upper half-plane, even when finite prevertices are logarithmic ends. -/
theorem isCompact_upperHalfPlaneSet_inter_preimage_schwarzChristoffelPrimitive_of_le_prevertex_sum
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i) {K : Set ℂ} (hK : IsCompact K)
    (hKB : Disjoint (((↑) : ℂ → OnePoint ℂ) '' K)
      (range (schwarzChristoffelSphereBoundary a e z₀))) :
    IsCompact (upperHalfPlaneSet ∩ schwarzChristoffelPrimitive a e z₀ ⁻¹' K) := by
  let E := schwarzChristoffelSphereExtension a e z₀
  have hcont := continuousOn_schwarzChristoffelSphereExtension a e z₀ hfinite
  have hclosed := hcont.preimage_isClosed_of_isClosed isClosed_closure
    (hK.image OnePoint.continuous_coe).isClosed
  have heq : closure (((↑) : ℂ → OnePoint ℂ) '' upperHalfPlaneSet) ∩
      E ⁻¹' (((↑) : ℂ → OnePoint ℂ) '' K) =
      ((↑) : ℂ → OnePoint ℂ) ''
        (upperHalfPlaneSet ∩ schwarzChristoffelPrimitive a e z₀ ⁻¹' K) := by
    ext x
    constructor
    · rintro ⟨hx, hxK⟩
      induction x using OnePoint.rec with
      | infty =>
        exact False.elim (disjoint_left.mp hKB hxK
          ⟨∞, by simp [E, schwarzChristoffelSphereBoundary_apply]⟩)
      | coe z =>
        have hz : 0 ≤ z.im := by
          simpa [closure_coe_image_upperHalfPlaneSet] using hx
        have hzpos : 0 < z.im := by
          by_contra h
          have him : z.im = 0 := le_antisymm (not_lt.mp h) hz
          have hre : (z.re : ℂ) = z := by
            apply Complex.ext <;> simp [him]
          exact disjoint_left.mp hKB hxK
            ⟨z.re, by simp [E, schwarzChristoffelSphereBoundary_apply, hre]⟩
        simp only [mem_preimage, E,
          schwarzChristoffelSphereExtension_coe_of_im_pos a e z₀ hzpos] at hxK
        exact ⟨z, ⟨hzpos, by simpa using hxK⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzK⟩, rfl⟩
      refine ⟨subset_closure ⟨z, hz, rfl⟩, ?_⟩
      simp only [mem_preimage, E,
        schwarzChristoffelSphereExtension_coe_of_im_pos a e z₀ hz]
      exact mem_image_of_mem _ hzK
  rw [OnePoint.isOpenEmbedding_coe.isEmbedding.isCompact_iff, ← heq]
  exact hclosed.isCompact

/-- The primitive is a covering map over the complement of the finite spherical boundary
values. Every finite prevertex may be integrable or logarithmic, and the total exponent is
unrestricted. -/
theorem isCoveringMapOn_schwarzChristoffelPrimitive_of_le_prevertex_sum
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i) :
    IsCoveringMapOn (fun τ : ℍ => schwarzChristoffelPrimitive a e z₀ τ)
      (((↑) : ℂ → OnePoint ℂ) ⁻¹' range (schwarzChristoffelSphereBoundary a e z₀))ᶜ := by
  have hB := (isCompact_range
    (continuous_schwarzChristoffelSphereBoundary a e z₀ hfinite)).isClosed
  apply isCoveringMapOn_schwarzChristoffelPrimitive_of_isCompact_preimage a e z₀
    (hB.preimage OnePoint.continuous_coe).isOpen_compl
  intro K hKB hK
  apply isCompact_upperHalfPlaneSet_inter_preimage_schwarzChristoffelPrimitive_of_le_prevertex_sum
    a e z₀ hfinite hK
  rw [disjoint_left]
  rintro _ ⟨w, hw, rfl⟩ hwB
  exact hKB hw hwB

/-- A preconnected region avoiding the finite spherical boundary values and containing the
image is exactly the image, including for data with several logarithmic ends. -/
theorem image_schwarzChristoffelPrimitive_eq_of_subset_of_le_prevertex_sum
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i) {W : Set ℂ} (hW : IsPreconnected W)
    (hWB : Disjoint (((↑) : ℂ → OnePoint ℂ) '' W)
      (range (schwarzChristoffelSphereBoundary a e z₀)))
    (hFW : schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ⊆ W) :
    schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet = W := by
  refine hFW.antisymm (hW.subset_of_closure_inter_subset
    (isOpen_image_schwarzChristoffelPrimitive a e z₀ isOpen_upperHalfPlaneSet subset_rfl)
    ⟨_, hFW (mem_image_of_mem _ z₀.im_pos), mem_image_of_mem _ z₀.im_pos⟩ ?_)
  intro w hw
  have hwcl := OnePoint.isOpenEmbedding_coe.isEmbedding.closure_eq_preimage_closure_image
    (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)
  have hw' : (w : OnePoint ℂ) ∈ closure (((↑) : ℂ → OnePoint ℂ) ''
      (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)) := by
    rw [hwcl] at hw
    exact hw.1
  rw [closure_coe_image_schwarzChristoffelPrimitive a e z₀ hfinite] at hw'
  have himage := hw'.resolve_right (disjoint_left.mp hWB (mem_image_of_mem _ hw.2))
  simpa using himage

/-- **Univalence criterion with multiple logarithmic ends.** If the image lies in a simply
connected region avoiding the finite spherical boundary values, the Schwarz--Christoffel
primitive maps the upper half-plane bijectively onto that region. Boundary injectivity is
not assumed. -/
theorem bijOn_schwarzChristoffelPrimitive_of_subset_of_le_prevertex_sum
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i) {W : Set ℂ} [SimplyConnectedSpace W]
    (hWB : Disjoint (((↑) : ℂ → OnePoint ℂ) '' W)
      (range (schwarzChristoffelSphereBoundary a e z₀)))
    (hFW : schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ⊆ W) :
    BijOn (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet W := by
  have himage := image_schwarzChristoffelPrimitive_eq_of_subset_of_le_prevertex_sum a e z₀
    hfinite (isPreconnected_iff_preconnectedSpace.mpr inferInstance) hWB hFW
  refine ⟨himage ▸ mapsTo_image _ _, fun z hz w hw hzw => ?_, himage ▸ surjOn_image _ _⟩
  have hcov := isCoveringMapOn_schwarzChristoffelPrimitive_of_le_prevertex_sum a e z₀ hfinite
  exact congrArg ((↑) : ℍ → ℂ) <|
    hcov.injective_of_range_subset
      (fun w hwW hwB => disjoint_left.mp hWB (mem_image_of_mem _ hwW) hwB)
      (range_subset_iff.mpr fun τ => hFW (mem_image_of_mem _ τ.im_pos))
      (a₁ := ⟨z, hz⟩) (a₂ := ⟨w, hw⟩) hzw

end TauCeti
