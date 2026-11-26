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

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ClosedUpperHalfPlane M]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, AddCommGroup (V₁ x)]
  [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)] [FiberBundle F₁ V₁]
  [VectorBundle ℝ F₁ V₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, AddCommGroup (V₂ x)]
  [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)] [FiberBundle F₂ V₂]
  [VectorBundle ℝ F₂ V₂] [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  (A : FiniteBundleAtlas ClosedUpperHalfPlane M F₁ V₁)
  (h : ∀ i, closure (A.dom i) ⊆ (trivializationAt F₂ V₂ (A.center i)).baseSet)

/-- The hom atlas has the interiors of the chart images of `A`. -/
@[simp]
theorem halfImage_hom (i : Fin A.n) : (A.hom (𝕜 := ℝ) h).halfImage i = A.halfImage i :=
  A.halfImage_ofBaseSet i

/-- **Hom sections act chartwise.** At the points of the image of chart `i`, applying the reading
of a section `φ` of the hom bundle to the reading of a section `s` of `V₁` gives the reading of the
section `x ↦ φ x (s x)` of `V₂`. -/
theorem halfCoord_hom_apply (i : Fin A.n) (φ : ∀ x, V₁ x →L[ℝ] V₂ x) (s : ∀ x, V₁ x) {z : ℂ}
    (hz : closedUpperHalfPlaneModel.symm z ∈ A.image i) :
    (A.hom (𝕜 := ℝ) h).halfCoord i φ z (A.halfCoord i s z) =
      (A.ofBaseSet h).halfCoord i (fun x ↦ φ x (s x)) z := by
  rw [halfCoord_def A i s z, halfCoord_def (A.ofBaseSet h) i _ z]
  exact (congrArg (· (A.coord i s (closedUpperHalfPlaneModel.symm z)))
    (halfCoord_def (A.hom (𝕜 := ℝ) h) i φ z)).trans (A.coord_hom_apply h i φ s hz)

end FiniteBundleAtlas

end TauCeti
