/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.MultipleEnds.Univalence
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.SimpleBoundary
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.RegularEdge
import TauCeti.Order.Interval.Finite

/-!
# The Schwarz--Christoffel map of a simple polygon

When its compactified boundary is a simple curve, the Schwarz--Christoffel primitive maps the
upper half-plane bijectively onto the complementary component containing its base-point image.
This identifies the image component for simple polygons, including those with reentrant corners.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Set UpperHalfPlane

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- A simple compactified Schwarz--Christoffel boundary makes the primitive a bijection from
the upper half-plane onto the complementary component containing its base-point image. -/
theorem bijOn_schwarzChristoffelPrimitive_of_simple_boundary
    (a e : ι → ℝ) (z₀ : UpperHalfPlane)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1)
    (hinj : Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀)) :
    BijOn (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet
      (connectedComponentIn (range (schwarzChristoffelCompactifiedBoundary a e z₀))ᶜ
        (schwarzChristoffelPrimitive a e z₀ z₀)) := by
  let F := schwarzChristoffelPrimitive a e z₀
  obtain ⟨p, q, x, ha, hx⟩ := exists_Ioo_disjoint_range_of_finite a
  obtain ⟨U, hUopen, hxU, G, hGF, hGinj, _, _⟩ :=
    exists_injOn_schwarzChristoffelPrimitive_continuation a e z₀ (fun i _ => ha i) hx
  obtain ⟨ε, hε, hnear⟩ :=
    exists_ball_preimage_schwarzChristoffelPrimitive_subset_of_boundary_injective
      a e z₀ hfinite hinfty hinj x hUopen hxU
  have hBclose : schwarzChristoffelBoundary a e z₀ x ∈ closure (F '' upperHalfPlaneSet) := by
    rw [closure_image_schwarzChristoffelPrimitive a e z₀ hfinite hinfty]
    exact Or.inr ⟨(x : OnePoint ℝ), by simp⟩
  obtain ⟨w, hwball, ⟨z, hzH, rfl⟩⟩ :=
    _root_.mem_closure_iff.mp hBclose _ Metric.isOpen_ball (Metric.mem_ball_self hε)
  let Fh : ℍ → ℂ := fun τ => F τ
  have hfiber : Fh ⁻¹' {F z} = {⟨z, hzH⟩} := by
    ext τ
    constructor
    · intro hτ
      have hτeq : F τ = F z := hτ
      have hwτ : F τ ∈ Metric.ball (schwarzChristoffelBoundary a e z₀ x) ε := by
        rw [hτeq]
        exact hwball
      have hτU : (τ : ℂ) ∈ U := hnear τ τ.im_pos hwτ
      have hzU : z ∈ U := hnear z hzH hwball
      apply Set.mem_singleton_iff.mpr
      apply UpperHalfPlane.ext_iff.mpr
      apply hGinj hτU hzU
      rw [hGF ⟨hτU, τ.im_pos⟩, hGF ⟨hzU, hzH⟩]
      exact hτeq
    · intro hτ
      obtain rfl := Set.mem_singleton_iff.mp hτ
      simp [Fh]
  have havoid : Disjoint (F '' upperHalfPlaneSet)
      (schwarzChristoffelFiniteBoundary a e z₀) := by
    rw [schwarzChristoffelFiniteBoundary_eq_range_compactifiedBoundary a e z₀ hfinite hinfty]
    exact disjoint_image_schwarzChristoffelPrimitive_range a e z₀ hfinite hinfty hinj
  have hF_inj : InjOn F upperHalfPlaneSet :=
    (injOn_schwarzChristoffelPrimitive_iff_fiber_ncard_eq_one a e z₀
      (fun j => (hfinite j).le) havoid (mem_image_of_mem F hzH)).mpr
      (by rw [hfiber, ncard_singleton])
  have himage := image_schwarzChristoffelPrimitive_eq_connectedComponentIn
    a e z₀ hfinite hinfty hinj
  exact ⟨himage ▸ mapsTo_image F _, hF_inj, himage ▸ surjOn_image F _⟩

end TauCeti
