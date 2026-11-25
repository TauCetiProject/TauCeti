/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Manifold

/-!
# The Floer quantities of a map into a manifold depend only on its germ

The perturbed derivative `du - X_K`, the Floer energy density and the Floer equation of a map
`u : ℝ × ℝ → M` at a point `y` only see `u` near `y`. These are the manifold counterparts of
`TauCeti.SymplecticForm.perturbedFDeriv_congr_of_eventuallyEq` and
`TauCeti.SymplecticForm.floerEnergyDensity_congr_of_eventuallyEq` for a vector-space target.

## Main results

* `TauCeti.SmoothTwoForm.perturbedMFDeriv_congr_of_eventuallyEq`: the perturbed derivative at `y`
  only depends on the germ of the map at `y`.
* `TauCeti.SmoothTwoForm.floerEnergyDensity_congr_of_eventuallyEq`: so does the energy density.
* `TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_of_eventuallyEq`: so does the Floer
  equation, for a family of almost complex structures on the tangent spaces of `M`.
-/

public section

open Filter Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
  {u u' : ℝ × ℝ → M} {y : ℝ × ℝ}

/-- The perturbed derivative at `y` only depends on the germ of the map at `y`. -/
theorem perturbedMFDeriv_congr_of_eventuallyEq (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (h : u =ᶠ[𝓝 y] u') :
    ω.perturbedMFDeriv Ks Kt u y =
      (ω.perturbedMFDeriv Ks Kt u' y : ℝ × ℝ →L[ℝ] TangentSpace I (u y)) := by
  have hy : u y = u' y := h.eq_of_nhds
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [perturbedMFDeriv_apply]
  rw [h.mfderiv_eq, hy, perturbedMFDeriv_apply]
  -- The identification of the tangent spaces at `u y = u' y` is the identity.
  rfl

/-- The Floer energy density at `y` only depends on the germ of the map at `y`. -/
theorem floerEnergyDensity_congr_of_eventuallyEq (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (h : u =ᶠ[𝓝 y] u') : ω.floerEnergyDensity Ks Kt u y = ω.floerEnergyDensity Ks Kt u' y := by
  have hy : u y = u' y := h.eq_of_nhds
  rw [floerEnergyDensity_def, floerEnergyDensity_def,
    ω.perturbedMFDeriv_congr_of_eventuallyEq Ks Kt h]
  -- Only the base point of the two-form remains to be identified.
  convert rfl using 2
  rw [hy]

/-- The Floer equation at `y`, for a family `J` of almost complex structures on the tangent spaces
of `M`, only depends on the germ of the map at `y`. -/
theorem isComplexLinearMap_perturbedMFDeriv_of_eventuallyEq (ω : SmoothTwoForm I M)
    (Ks Kt : ℝ × ℝ → M → ℝ) {J : (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (h : u =ᶠ[𝓝 y] u')
    (hJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (u' y))
      (ω.perturbedMFDeriv Ks Kt u' y).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (u y))
      (ω.perturbedMFDeriv Ks Kt u y).toLinearMap := by
  have hy : u y = u' y := h.eq_of_nhds
  rw [ω.perturbedMFDeriv_congr_of_eventuallyEq Ks Kt h]
  convert hJ using 2
  rw [hy]

end TauCeti.SmoothTwoForm
