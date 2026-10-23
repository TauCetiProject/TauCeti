/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Basic

/-!
# Coefficient maps and coefficient scalars of wedge products

The paired wedge `φ.wedgeWith μ ψ` of two forms is natural in its coefficient spaces: coefficient
maps applied to the factors, or to the product, are absorbed into the pairing `μ`. Consequently,
when scalars acting on the coefficients commute with the pairing in one argument, the paired
wedge is linear for those scalars in that argument.

The main application is to complex-valued forms. If `μ` is bilinear over a normed `ℝ`-algebra
`𝕜`, for instance a complex-bilinear pairing of complex coefficient spaces, then the paired wedge
of smooth forms for the underlying real pairing `μ.bilinearRestrictScalars ℝ` is `𝕜`-linear in
each factor, for the action of `𝕜` on smooth forms through their coefficients. Together with the
complex-linearity of the exterior derivative and pullback, this makes the wedge product of
complex-valued forms compatible with the complex vector space structure on which type
decompositions and the Dolbeault operators are built.

## Main declarations

* `TauCeti.RoughForm.mapCoeff_wedgeWith_mapCoeff`, `TauCeti.SmoothForm.mapCoeff_wedgeWith_mapCoeff`:
  coefficient maps of the factors are absorbed into the pairing by `bilinearComp`.
* `TauCeti.RoughForm.mapCoeff_wedgeWith`, `TauCeti.SmoothForm.mapCoeff_wedgeWith`: a coefficient
  map of the product is absorbed into the pairing by postcomposition.
* `TauCeti.SmoothForm.wedgeWith_smul_left_of_map_smul`,
  `TauCeti.SmoothForm.wedgeWith_smul_right_of_map_smul`: the paired wedge is linear for
  coefficient scalars commuting with the pairing.
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
theorem mapCoeff_wedgeWith_mapCoeff (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (L₁ : G₁ →L[ℝ] F₁)
    (L₂ : G₂ →L[ℝ] F₂) (φ : RoughForm I M G₁ k) (ψ : RoughForm I M G₂ l) :
    (mapCoeff L₁ φ).wedgeWith μ (mapCoeff L₂ ψ) = φ.wedgeWith (μ.bilinearComp L₁ L₂) ψ := by
  ext x v
  simp only [wedgeWith_apply, mapCoeff_apply, ContinuousLinearMap.bilinearComp_apply]

/-- A coefficient map applied to a paired wedge is absorbed into the pairing. -/
theorem mapCoeff_wedgeWith (L : F₃ →L[ℝ] G) (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) :
    mapCoeff L (φ.wedgeWith μ ψ) = φ.wedgeWith ((ContinuousLinearMap.postcomp F₂ L).comp μ) ψ := by
  ext x v
  rw [mapCoeff_apply, wedgeWith_apply', wedgeWith_apply',
    ContinuousAlternatingMap.pairedWedge_postcomp L μ μ.continuous₂ (φ x) (ψ x),
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply]

variable {S : Type*} [Monoid S]
  [DistribMulAction S F₃] [ContinuousConstSMul S F₃] [SMulCommClass ℝ S F₃]

/-- A coefficient scalar commuting with the pairing in its first argument can be moved out of
the first factor of a paired wedge. -/
theorem wedgeWith_smul_left_of_map_smul [DistribMulAction S F₁] [ContinuousConstSMul S F₁]
    [SMulCommClass ℝ S F₁] (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {c : S}
    (hμ : ∀ a b, μ (c • a) b = c • μ a b) (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) :
    (c • φ).wedgeWith μ ψ = c • φ.wedgeWith μ ψ := by
  have h := mapCoeff_wedgeWith_mapCoeff μ (c • ContinuousLinearMap.id ℝ F₁)
    (ContinuousLinearMap.id ℝ F₂) φ ψ
  rw [mapCoeff_id] at h
  rw [smul_eq_mapCoeff c φ, h, smul_eq_mapCoeff c (φ.wedgeWith μ ψ), mapCoeff_wedgeWith]
  congr 1
  ext a b
  simp [hμ]

/-- A coefficient scalar commuting with the pairing in its second argument can be moved out of
the second factor of a paired wedge. -/
theorem wedgeWith_smul_right_of_map_smul [DistribMulAction S F₂] [ContinuousConstSMul S F₂]
    [SMulCommClass ℝ S F₂] (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {c : S}
    (hμ : ∀ a b, μ a (c • b) = c • μ a b) (φ : RoughForm I M F₁ k) (ψ : RoughForm I M F₂ l) :
    φ.wedgeWith μ (c • ψ) = c • φ.wedgeWith μ ψ := by
  have h := mapCoeff_wedgeWith_mapCoeff μ (ContinuousLinearMap.id ℝ F₁)
    (c • ContinuousLinearMap.id ℝ F₂) φ ψ
  rw [mapCoeff_id] at h
  rw [smul_eq_mapCoeff c ψ, h, smul_eq_mapCoeff c (φ.wedgeWith μ ψ), mapCoeff_wedgeWith]
  congr 1
  ext a b
  simp [hμ]

end RoughForm

/-! ### Smooth forms -/

namespace SmoothForm

variable [IsManifold I 1 M]

/-- Coefficient maps applied to the two factors of a smooth paired wedge are absorbed into the
pairing. -/
theorem mapCoeff_wedgeWith_mapCoeff (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (L₁ : G₁ →L[ℝ] F₁)
    (L₂ : G₂ →L[ℝ] F₂) (φ : SmoothForm I M G₁ k) (ψ : SmoothForm I M G₂ l) :
    wedgeWith μ (mapCoeff L₁ φ) (mapCoeff L₂ ψ) = wedgeWith (μ.bilinearComp L₁ L₂) φ ψ :=
  Subtype.ext <| by
    simp only [coe_wedgeWith, coe_mapCoeff, RoughForm.mapCoeff_wedgeWith_mapCoeff]

/-- A coefficient map applied to a smooth paired wedge is absorbed into the pairing. -/
theorem mapCoeff_wedgeWith (L : F₃ →L[ℝ] G) (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (φ : SmoothForm I M F₁ k) (ψ : SmoothForm I M F₂ l) :
    mapCoeff L (wedgeWith μ φ ψ) = wedgeWith ((ContinuousLinearMap.postcomp F₂ L).comp μ) φ ψ :=
  Subtype.ext <| by
    simp only [coe_wedgeWith, coe_mapCoeff, RoughForm.mapCoeff_wedgeWith]

section Scalars

variable {S : Type*} [Monoid S]
  [DistribMulAction S F₃] [ContinuousConstSMul S F₃] [SMulCommClass ℝ S F₃]

/-- A coefficient scalar commuting with the pairing in its first argument can be moved out of
the first factor of a smooth paired wedge. -/
theorem wedgeWith_smul_left_of_map_smul [DistribMulAction S F₁] [ContinuousConstSMul S F₁]
    [SMulCommClass ℝ S F₁] (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {c : S}
    (hμ : ∀ a b, μ (c • a) b = c • μ a b) (φ : SmoothForm I M F₁ k)
    (ψ : SmoothForm I M F₂ l) :
    wedgeWith μ (c • φ) ψ = c • wedgeWith μ φ ψ :=
  Subtype.ext <| by
    simpa only [coe_wedgeWith, smul_toRoughForm] using
      RoughForm.wedgeWith_smul_left_of_map_smul μ hμ φ.1 ψ.1

/-- A coefficient scalar commuting with the pairing in its second argument can be moved out of
the second factor of a smooth paired wedge. -/
theorem wedgeWith_smul_right_of_map_smul [DistribMulAction S F₂] [ContinuousConstSMul S F₂]
    [SMulCommClass ℝ S F₂] (μ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) {c : S}
    (hμ : ∀ a b, μ a (c • b) = c • μ a b) (φ : SmoothForm I M F₁ k)
    (ψ : SmoothForm I M F₂ l) :
    wedgeWith μ φ (c • ψ) = c • wedgeWith μ φ ψ :=
  Subtype.ext <| by
    simpa only [coe_wedgeWith, smul_toRoughForm] using
      RoughForm.wedgeWith_smul_right_of_map_smul μ hμ φ.1 ψ.1

end Scalars

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
