/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.MultipleEnds.SheetCount

/-!
# Single-sheet univalence for Schwarz--Christoffel maps with several ends

If the primitive's image avoids its finite boundary trace, one uniquely attained interior
value forces global injectivity. More generally, a preconnected region containing the image
and avoiding the trace is mapped onto bijectively exactly when the fiber over one of its points
has cardinality one. This criterion needs neither simple connectivity of that region nor
injectivity of the sphere-valued boundary, which identifies all logarithmic ends with infinity.

The criterion requires a globally singleton fiber. One can establish this near an end by combining
local end geometry with exclusion of all other preimages in the upper half-plane.
Boundary avoidance remains a genuine hypothesis, not a consequence of local univalence.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
* O. Forster, *Lectures on Riemann Surfaces*, Section 4.
-/

public section

open Set UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- **Single-sheet univalence.** If the image avoids its finite boundary trace, the primitive
is injective exactly when one interior value has one preimage. Any number of logarithmic ends,
coincident prevertices, and an unrestricted total exponent are allowed. -/
theorem injOn_schwarzChristoffelPrimitive_iff_fiber_ncard_eq_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i)
    (havoid : Disjoint (schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet)
      (schwarzChristoffelFiniteBoundary a e z₀))
    {w : ℂ} (hw : w ∈ schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet) :
    InjOn (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet ↔
      ((fun τ : ℍ => schwarzChristoffelPrimitive a e z₀ τ) ⁻¹' {w}).ncard = 1 := by
  let F := schwarzChristoffelPrimitive a e z₀
  let Fh : ℍ → ℂ := fun τ => F τ
  constructor
  · intro hinj
    obtain ⟨z, hz, rfl⟩ := hw
    have hfiber : Fh ⁻¹' {F z} = {⟨z, hz⟩} := by
      ext τ
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro h
        exact UpperHalfPlane.ext_iff.mpr (hinj τ.im_pos hz h)
      · rintro rfl
        rfl
    rw [hfiber, ncard_singleton]
  · intro hone
    obtain ⟨d, -, hd⟩ :=
      exists_constant_schwarzChristoffelPrimitive_fiber_ncard a e z₀ hfinite havoid
    have hd1 : d = 1 := (hd w hw).symm.trans hone
    intro z hz y hy hzy
    obtain ⟨τ, hτ⟩ := ncard_eq_one.mp ((hd (F z) (mem_image_of_mem F hz)).trans hd1)
    have hzmem : (⟨z, hz⟩ : ℍ) ∈ Fh ⁻¹' {F z} := rfl
    have hymem : (⟨y, hy⟩ : ℍ) ∈ Fh ⁻¹' {F z} := hzy.symm
    rw [hτ, mem_singleton_iff] at hzmem hymem
    exact congrArg ((↑) : ℍ → ℂ) (hzmem.trans hymem.symm)

/-- **A degree-one mapping criterion with several logarithmic ends.** A preconnected region
containing the image and avoiding the finite boundary trace is the bijective image of the
upper half-plane exactly when the fiber over one specified point has cardinality one.
No openness or simple-connectivity hypothesis on the region is necessary. -/
theorem bijOn_schwarzChristoffelPrimitive_iff_fiber_ncard_eq_one
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 ≤ ∑ i with a i = a j, e i)
    {W : Set ℂ} (hW : IsPreconnected W)
    (hWB : Disjoint W (schwarzChristoffelFiniteBoundary a e z₀))
    (hFW : schwarzChristoffelPrimitive a e z₀ '' upperHalfPlaneSet ⊆ W)
    {w : ℂ} (hw : w ∈ W) :
    BijOn (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet W ↔
      ((fun τ : ℍ => schwarzChristoffelPrimitive a e z₀ τ) ⁻¹' {w}).ncard = 1 := by
  have hWB' : Disjoint (((↑) : ℂ → OnePoint ℂ) '' W)
      (range (schwarzChristoffelSphereBoundary a e z₀)) := by
    rw [disjoint_left]
    rintro _ ⟨v, hv, rfl⟩ hvB
    exact disjoint_left.mp hWB hv
      (by rwa [schwarzChristoffelFiniteBoundary_eq_preimage_range a e z₀ hfinite])
  have himage := image_schwarzChristoffelPrimitive_eq_of_subset_of_neg_one_le_prevertex_sum
    a e z₀ hfinite hW hWB' hFW
  have hinj := injOn_schwarzChristoffelPrimitive_iff_fiber_ncard_eq_one a e z₀ hfinite
    (hWB.mono_left hFW) (himage.symm ▸ hw)
  exact ⟨fun h => hinj.mp h.injOn,
    fun h => ⟨himage ▸ mapsTo_image _ _, hinj.mpr h, himage ▸ surjOn_image _ _⟩⟩

end TauCeti
