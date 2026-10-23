/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic

/-!
# Coefficient maps of wedge products and `𝕜`-bilinear pairings

The paired wedge `φ.wedgeWith μ ψ` of two forms is natural in its coefficient spaces
(`TauCeti.SmoothForm.mapCoeff_wedgeWith`). This file records the two special cases that serve as
simp normal forms: coefficient maps applied to the factors, or to the product, are absorbed into
the pairing `μ`.

It also specialises the semilinearity of the paired wedge
(`TauCeti.SmoothForm.wedgeWith_smul_left_of_map_smul`) to pairings that are bilinear over a normed
`ℝ`-algebra `𝕜`, for instance complex-bilinear pairings of complex coefficient spaces: the paired
wedge of smooth forms for the underlying real pairing `μ.bilinearRestrictScalars ℝ` is `𝕜`-linear
in each factor, for the action of `𝕜` on smooth forms through their coefficients, and `simp`
moves such scalars out of either factor.

## Main declarations

* `TauCeti.RoughForm.mapCoeff_wedgeWith_mapCoeff`, `TauCeti.SmoothForm.mapCoeff_wedgeWith_mapCoeff`:
  coefficient maps of the factors are absorbed into the pairing by `bilinearComp`.
* `TauCeti.RoughForm.mapCoeff_wedgeWith_eq_postcomp`,
  `TauCeti.SmoothForm.mapCoeff_wedgeWith_eq_postcomp`: a coefficient map of the product is
  absorbed into the pairing by postcomposition.
* `TauCeti.SmoothForm.wedgeWith_bilinearRestrictScalars_smul_left`,
  `TauCeti.SmoothForm.wedgeWith_bilinearRestrictScalars_smul_right`: the paired wedge for a
  `𝕜`-bilinear pairing is `𝕜`-linear in each factor; for `𝕜 = ℂ` this is the complex-linearity
  of the wedge of complex-valued forms.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 14.
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti

variable {E H M F₁ F₂ F₃ G₁ G₂ G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] [NormedAddCommGroup G₁] [NormedSpace ℝ G₁]
  [NormedAddCommGroup G₂] [NormedSpace ℝ G₂] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {k l : ℕ}

/-! ### Rough forms -/

namespace RoughForm

/-- Coefficient maps applied to the two factors of a paired wedge are absorbed into the
pairing. -/
@[simp]
theorem mapCoeff_wedgeWith_mapCoeff (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (L₁ : G₁ →L[ℝ] F₁)
    (L₂ : G₂ →L[ℝ] F₂) (φ : RoughForm I M G₁ k) (ψ : RoughForm I M G₂ l) :
    (mapCoeff L₁ φ).wedgeWith μ (mapCoeff L₂ ψ) = φ.wedgeWith (μ.bilinearComp L₁ L₂) ψ := by
  ext x v
  simp only [wedgeWith_apply, mapCoeff_apply, ContinuousLinearMap.bilinearComp_apply]

/-- A coefficient map applied to a paired wedge is absorbed into the pairing. -/
@[simp]
theorem mapCoeff_wedgeWith_eq_postcomp (L : F₃ →L[ℝ] G) (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) :
    mapCoeff L (φ.wedgeWith μ ψ) = φ.wedgeWith ((ContinuousLinearMap.postcomp F₂ L).comp μ) ψ := by
  ext x v
  rw [mapCoeff_apply, wedgeWith_apply', wedgeWith_apply',
    ContinuousAlternatingMap.pairedWedge_postcomp L μ μ.continuous₂ (φ x) (ψ x),
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply]

end RoughForm

/-! ### Smooth forms -/

namespace SmoothForm

variable [IsManifold I 1 M]

/-- Coefficient maps applied to the two factors of a smooth paired wedge are absorbed into the
pairing. -/
@[simp]
theorem mapCoeff_wedgeWith_mapCoeff (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (L₁ : G₁ →L[ℝ] F₁)
    (L₂ : G₂ →L[ℝ] F₂) (φ : SmoothForm I M G₁ k) (ψ : SmoothForm I M G₂ l) :
    wedgeWith μ (mapCoeff L₁ φ) (mapCoeff L₂ ψ) = wedgeWith (μ.bilinearComp L₁ L₂) φ ψ :=
  Subtype.ext <| by
    simp only [coe_wedgeWith, coe_mapCoeff, RoughForm.mapCoeff_wedgeWith_mapCoeff]

/-- A coefficient map applied to a smooth paired wedge is absorbed into the pairing. -/
@[simp]
theorem mapCoeff_wedgeWith_eq_postcomp (L : F₃ →L[ℝ] G) (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : SmoothForm I M F₁ k) (ψ : SmoothForm I M F₂ l) :
    mapCoeff L (wedgeWith μ φ ψ) = wedgeWith ((ContinuousLinearMap.postcomp F₂ L).comp μ) φ ψ :=
  Subtype.ext <| by
    simp only [coe_wedgeWith, coe_mapCoeff, RoughForm.mapCoeff_wedgeWith_eq_postcomp]

section RestrictScalars

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  [NormedSpace 𝕜 F₁] [IsScalarTower ℝ 𝕜 F₁] [NormedSpace 𝕜 F₂] [IsScalarTower ℝ 𝕜 F₂]
  [NormedSpace 𝕜 F₃] [IsScalarTower ℝ 𝕜 F₃]

/-- The smooth paired wedge for a `𝕜`-bilinear pairing is `𝕜`-linear in its first factor. For
`𝕜 = ℂ` and complex-bilinear pairings, this is complex-linearity of the wedge of complex-valued
forms. -/
@[simp]
theorem wedgeWith_bilinearRestrictScalars_smul_left (μ : F₁ →L[𝕜] F₂ →L[𝕜] F₃) (c : 𝕜)
    (φ : SmoothForm I M F₁ k) (ψ : SmoothForm I M F₂ l) :
    wedgeWith (μ.bilinearRestrictScalars ℝ) (c • φ) ψ =
      c • wedgeWith (μ.bilinearRestrictScalars ℝ) φ ψ :=
  wedgeWith_smul_left_of_map_smul _ (fun a b ↦ by simp) φ ψ

/-- The smooth paired wedge for a `𝕜`-bilinear pairing is `𝕜`-linear in its second factor. For
`𝕜 = ℂ` and complex-bilinear pairings, this is complex-linearity of the wedge of complex-valued
forms. -/
@[simp]
theorem wedgeWith_bilinearRestrictScalars_smul_right (μ : F₁ →L[𝕜] F₂ →L[𝕜] F₃) (c : 𝕜)
    (φ : SmoothForm I M F₁ k) (ψ : SmoothForm I M F₂ l) :
    wedgeWith (μ.bilinearRestrictScalars ℝ) φ (c • ψ) =
      c • wedgeWith (μ.bilinearRestrictScalars ℝ) φ ψ :=
  wedgeWith_smul_right_of_map_smul _ (fun a b ↦ by simp) φ ψ

end RestrictScalars

end SmoothForm

end TauCeti
