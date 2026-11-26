/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.HalfPlane
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Hom

/-!
# Hom atlases over bases with boundary

For a finite bundle atlas `A` of `V₁` over a manifold modelled on the closed upper half-plane, the
atlas `A.hom h` of the bundle `x ↦ V₁ x →L[ℝ] V₂ x` has the interiors of the chart images of `A`
(`TauCeti.FiniteBundleAtlas.halfImage_hom`), and applying the reading in `ℂ` of a section of the
hom bundle to the reading of a section of `V₁` gives the reading of the applied section
(`TauCeti.FiniteBundleAtlas.halfCoord_hom_apply`), the half-plane form of
`TauCeti.FiniteBundleAtlas.coord_hom_apply`.
-/

public section

open Bundle Set
open scoped Manifold

namespace TauCeti

namespace FiniteBundleAtlas

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, AddCommGroup (V₁ x)]
  [∀ x, Module 𝕜 (V₁ x)] [∀ x, TopologicalSpace (V₁ x)] [FiberBundle F₁ V₁]
  [VectorBundle 𝕜 F₁ V₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, AddCommGroup (V₂ x)]
  [∀ x, Module 𝕜 (V₂ x)] [∀ x, TopologicalSpace (V₂ x)] [FiberBundle F₂ V₂]
  [VectorBundle 𝕜 F₂ V₂] [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]
  (A : FiniteBundleAtlas ClosedUpperHalfPlane M F₁ V₁)
  (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F₂ V₂ (A.center i)).baseSet)

/-- The hom atlas has the interiors of the chart images of `A`. -/
@[simp]
theorem halfImage_hom (i : Fin A.n) : (A.hom (𝕜 := 𝕜) h).halfImage i = A.halfImage i :=
  A.halfImage_ofBaseSet i

/-- The hom atlas has the chart images in `ℂ` of `A`. -/
@[simp]
theorem halfClosedImage_hom (i : Fin A.n) :
    (A.hom (𝕜 := 𝕜) h).halfClosedImage i = A.halfClosedImage i :=
  halfClosedImage_ofBaseSet i

/-- The hom atlas has the interiors of the overlaps in `ℂ` of `A`. -/
@[simp]
theorem halfOverlap_hom (i i' : Fin A.n) :
    (A.hom (𝕜 := 𝕜) h).halfOverlap i i' = A.halfOverlap i i' :=
  halfOverlap_ofBaseSet i i'

/-- The hom atlas has the chart transitions in `ℂ` of `A`. -/
@[simp]
theorem halfTransition_hom (i i' : Fin A.n) :
    (A.hom (𝕜 := 𝕜) h).halfTransition i i' = A.halfTransition i i' :=
  halfTransition_ofBaseSet i i'

/-- A section of the hom bundle read in `ℂ` in a chart of `A.hom h` is its value at the
corresponding point of `M` expressed in the preferred trivializations of `V₁` and `V₂` at the
centre of the chart. -/
theorem halfCoord_hom (i : Fin A.n) (φ : ∀ x, V₁ x →L[𝕜] V₂ x) (z : ℂ) :
    (A.hom h).halfCoord i φ z =
      ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ (A.center i)
        ((A.chart i).symm (closedUpperHalfPlaneModel.symm z)) (A.center i)
        ((A.chart i).symm (closedUpperHalfPlaneModel.symm z))
        (φ ((A.chart i).symm (closedUpperHalfPlaneModel.symm z))) := by
  rw [halfCoord_def (A := A.hom h) i]
  exact A.coord_hom h i φ (closedUpperHalfPlaneModel.symm z)

/-- **Hom sections act chartwise.** At the points of the image of chart `i`, applying the reading
of a section `φ` of the hom bundle to the reading of a section `s` of `V₁` gives the reading of the
section `x ↦ φ x (s x)` of `V₂`. -/
theorem halfCoord_hom_apply (i : Fin A.n) (φ : ∀ x, V₁ x →L[𝕜] V₂ x) (s : ∀ x, V₁ x) {z : ℂ}
    (hz : closedUpperHalfPlaneModel.symm z ∈ A.image i) :
    (A.hom h).halfCoord i φ z (A.halfCoord i s z) =
      (A.ofBaseSet h).halfCoord i (fun x ↦ φ x (s x)) z := by
  rw [halfCoord_def (A := A.hom h) i, halfCoord_def A i, halfCoord_def (A := A.ofBaseSet h) i]
  exact A.coord_hom_apply h i φ s hz

end FiniteBundleAtlas

end TauCeti
