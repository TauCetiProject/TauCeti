/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Normal quotient maps induced by differentials

The normal fiber of a map `u` at `x` is the quotient by the actual derivative image
`range (du x)`. The differential of any target map `Φ` carries this image into
`range (d(Φ ∘ u) x)`, so it induces the map of normal quotients `normalFDerivMap`, built with
`Submodule.mapQ`. It does not require `u` to be immersive or `Φ` to be invertible.

Precomposing with a source map `ψ` goes the other way: the derivative image of `u ∘ ψ` at `y`
lies in that of `u` at `ψ y`, with equality when `dψ y` is surjective. So the normal fiber of
`u ∘ ψ` maps onto that of `u` by `Submodule.factor`, and the two are identified by
`Submodule.quotEquivOfEq` when `ψ` is a submersion at `y`, for instance a local
reparametrization.

## Main results

* `TauCeti.normalFDerivMap_id`, `TauCeti.normalFDerivMap_comp`: functoriality in the target
  map.
* `TauCeti.normalFDerivMap_injective`, `TauCeti.normalFDerivMap_surjective`,
  `TauCeti.normalFDerivMap_bijective`: the induced map inherits injectivity, surjectivity and
  bijectivity from the differential of the target map.
* `TauCeti.range_fderiv_comp_le_range_fderiv`, `TauCeti.range_fderiv_comp_eq_range_fderiv`:
  precomposition with a source map shrinks the derivative image, and preserves it when the
  differential of the source map is surjective.
-/

public section

noncomputable section

namespace TauCeti

variable {𝕜 U V W : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup U] [NormedSpace 𝕜 U]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- The differential of any target map carries the derivative image of `u` into that of
`Φ ∘ u`. No differentiability is needed: otherwise one of the derivatives is zero. -/
theorem range_fderiv_le_comap_range_fderiv_comp (u : U → V) (Φ : V → W) (x : U) :
    (fderiv 𝕜 u x).toLinearMap.range ≤
      (fderiv 𝕜 (Φ ∘ u) x).toLinearMap.range.comap (fderiv 𝕜 Φ (u x)).toLinearMap := by
  by_cases hΦ : DifferentiableAt 𝕜 Φ (u x)
  · by_cases hu : DifferentiableAt 𝕜 u x
    · rintro _ ⟨a, rfl⟩
      exact ⟨a, by simp [fderiv_comp x hΦ hu]⟩
    · simp [fderiv_zero_of_not_differentiableAt hu]
  · simp [fderiv_zero_of_not_differentiableAt hΦ]

variable (𝕜) in
/-- The map of normal quotients `V ⧸ range (du x) → W ⧸ range (d(Φ ∘ u) x)` induced by the
differential of a target map `Φ`. -/
def normalFDerivMap (u : U → V) (Φ : V → W) (x : U) :
    (V ⧸ (fderiv 𝕜 u x).toLinearMap.range) →ₗ[𝕜]
      W ⧸ (fderiv 𝕜 (Φ ∘ u) x).toLinearMap.range :=
  (fderiv 𝕜 u x).toLinearMap.range.mapQ _ (fderiv 𝕜 Φ (u x)).toLinearMap
    (range_fderiv_le_comap_range_fderiv_comp u Φ x)

/-- The induced normal map is the quotient map `Submodule.mapQ` of the differential. -/
theorem normalFDerivMap_def (u : U → V) (Φ : V → W) (x : U) :
    normalFDerivMap 𝕜 u Φ x =
      (fderiv 𝕜 u x).toLinearMap.range.mapQ _ (fderiv 𝕜 Φ (u x)).toLinearMap
        (range_fderiv_le_comap_range_fderiv_comp u Φ x) := (rfl)

/-- The induced normal map sends the class of `w` to the class of `dΦ (u x) w`. -/
@[simp]
theorem normalFDerivMap_mk (u : U → V) (Φ : V → W) (x : U) (w : V) :
    normalFDerivMap 𝕜 u Φ x (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (fderiv 𝕜 Φ (u x) w) := (rfl)

/-- The induced normal map is characterized by its composition with the quotient map. -/
@[simp]
theorem normalFDerivMap_comp_mkQ (u : U → V) (Φ : V → W) (x : U) :
    (normalFDerivMap 𝕜 u Φ x).comp (fderiv 𝕜 u x).toLinearMap.range.mkQ =
      (fderiv 𝕜 (Φ ∘ u) x).toLinearMap.range.mkQ.comp (fderiv 𝕜 Φ (u x)).toLinearMap :=
  Submodule.mapQ_mkQ _ _ _

/-- The identity target map induces the identity on the normal quotient. -/
@[simp]
theorem normalFDerivMap_id (u : U → V) (x : U) :
    normalFDerivMap 𝕜 u id x = LinearMap.id := by
  ext w
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, normalFDerivMap_mk, fderiv_id,
    ContinuousLinearMap.id_apply, LinearMap.id_apply]

/-- Normal quotient maps respect composition of target maps differentiable at the image
points, without requiring differentiability of the curve. -/
theorem normalFDerivMap_comp {Z : Type*} [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]
    (u : U → V) (Φ : V → W) (Ψ : W → Z) (x : U)
    (hΨ : DifferentiableAt 𝕜 Ψ (Φ (u x))) (hΦ : DifferentiableAt 𝕜 Φ (u x)) :
    normalFDerivMap 𝕜 u (Ψ ∘ Φ) x =
      (normalFDerivMap 𝕜 (Φ ∘ u) Ψ x).comp (normalFDerivMap 𝕜 u Φ x) := by
  ext w
  simp [normalFDerivMap_mk, fderiv_comp (u x) hΨ hΦ]

/-- A target map with surjective differential induces a surjection of normal quotients. -/
theorem normalFDerivMap_surjective (u : U → V) (Φ : V → W) (x : U)
    (h : Function.Surjective (fderiv 𝕜 Φ (u x))) :
    Function.Surjective (normalFDerivMap 𝕜 u Φ x) := by
  rintro ⟨w⟩
  obtain ⟨v, rfl⟩ := h w
  exact ⟨Submodule.Quotient.mk v, rfl⟩

/-- A target map with injective differential induces an injection of normal quotients, when
the curve and the target map are differentiable. -/
theorem normalFDerivMap_injective (u : U → V) (Φ : V → W) (x : U)
    (hu : DifferentiableAt 𝕜 u x) (hΦ : DifferentiableAt 𝕜 Φ (u x))
    (h : Function.Injective (fderiv 𝕜 Φ (u x))) :
    Function.Injective (normalFDerivMap 𝕜 u Φ x) := by
  refine (injective_iff_map_eq_zero _).2 ?_
  rintro ⟨w⟩ hw
  rw [Submodule.Quotient.quot_mk_eq_mk, normalFDerivMap_mk,
    Submodule.Quotient.mk_eq_zero] at hw
  obtain ⟨a, ha⟩ := hw
  rw [fderiv_comp x hΦ hu] at ha
  rw [Submodule.Quotient.quot_mk_eq_mk, Submodule.Quotient.mk_eq_zero]
  exact ⟨a, h ha⟩

/-- A target map with bijective differential induces a bijection of normal quotients, when
the curve and the target map are differentiable. -/
theorem normalFDerivMap_bijective (u : U → V) (Φ : V → W) (x : U)
    (hu : DifferentiableAt 𝕜 u x) (hΦ : DifferentiableAt 𝕜 Φ (u x))
    (h : Function.Bijective (fderiv 𝕜 Φ (u x))) :
    Function.Bijective (normalFDerivMap 𝕜 u Φ x) :=
  ⟨normalFDerivMap_injective u Φ x hu hΦ h.1, normalFDerivMap_surjective u Φ x h.2⟩

section Source

variable {U' : Type*} [NormedAddCommGroup U'] [NormedSpace 𝕜 U']

/-- The derivative image of `u ∘ ψ` at `y` lies in the derivative image of `u` at `ψ y`. Both
maps must be differentiable: otherwise `fderiv` is zero on one side only. -/
theorem range_fderiv_comp_le_range_fderiv (u : U → V) (ψ : U' → U) (y : U')
    (hu : DifferentiableAt 𝕜 u (ψ y)) (hψ : DifferentiableAt 𝕜 ψ y) :
    (fderiv 𝕜 (u ∘ ψ) y).toLinearMap.range ≤ (fderiv 𝕜 u (ψ y)).toLinearMap.range := by
  rw [fderiv_comp y hu hψ, ContinuousLinearMap.toLinearMap_comp]
  exact LinearMap.range_comp_le_range _ _

/-- A source map with surjective differential does not change the derivative image. -/
theorem range_fderiv_comp_eq_range_fderiv (u : U → V) (ψ : U' → U) (y : U')
    (hu : DifferentiableAt 𝕜 u (ψ y)) (hψ : DifferentiableAt 𝕜 ψ y)
    (h : Function.Surjective (fderiv 𝕜 ψ y)) :
    (fderiv 𝕜 (u ∘ ψ) y).toLinearMap.range = (fderiv 𝕜 u (ψ y)).toLinearMap.range := by
  rw [fderiv_comp y hu hψ, ContinuousLinearMap.toLinearMap_comp]
  exact LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 h)

end Source

end TauCeti
