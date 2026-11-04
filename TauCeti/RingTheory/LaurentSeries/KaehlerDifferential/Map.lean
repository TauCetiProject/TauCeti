/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.KaehlerDifferential.Basic
public import TauCeti.RingTheory.LaurentSeries.Convergence

/-!
# Coefficient-field maps on continuous Laurent differentials

A field embedding `σ : K →+* L` sends the continuous one-form `f dX` over `K` to
`σ(f) dX` over `L`, where `σ(f)` applies `σ` to every Laurent coefficient. This is a continuous
semilinear injection for the valuation topologies, characterized by its value on `dX`.
It commutes with the universal continuous derivations and with substitution, so extending
coefficients and changing the formal parameter give the same differential. Residues extend
by `σ` as well.

The construction uses `ContinuousKaehlerDifferential.equivLaurentSeries`, which identifies the
quotient of algebraic Kähler differentials by the kernel of formal differentiation with the
Laurent field. No topology on either coefficient field is required.
-/

public section

open HahnSeries
open scoped LaurentSeries

namespace TauCeti.ContinuousKaehlerDifferential

variable {K L M : Type*} [Field K] [Field L] [Field M]

/-- Extension of coefficients on continuous one-forms: `f dX ↦ σ(f) dX`. It is semilinear over
the coefficientwise Laurent-field embedding. -/
noncomputable def map (σ : K →+* L) :
    ContinuousKaehlerDifferential K →ₛₗ[(mapRingHom σ : K⸨X⸩ →+* L⸨X⸩)]
      ContinuousKaehlerDifferential L :=
  (equivLaurentSeries L).symm.toLinearMap.comp
    ((mapRingHom σ).toSemilinearMap.comp (equivLaurentSeries K).toLinearMap)

/-- In the coordinate `dX`, extension of coefficients is the coefficientwise Laurent-field map. -/
@[simp]
theorem equivLaurentSeries_map (σ : K →+* L) (ω : ContinuousKaehlerDifferential K) :
    equivLaurentSeries L (map σ ω) = mapRingHom σ (equivLaurentSeries K ω) :=
  (equivLaurentSeries L).apply_symm_apply _

/-- Extension of coefficients commutes with the universal continuous derivations. -/
@[simp]
theorem map_D (σ : K →+* L) (f : K⸨X⸩) :
    map σ (D K f) = D L (mapRingHom σ f) := by
  apply (equivLaurentSeries L).injective
  ext n
  simp [LaurentSeries.derivative_apply]

/-- The coefficient extension sends `dX` to `dX`. -/
theorem map_D_single_one (σ : K →+* L) :
    map σ (D K (single 1 1)) = D L (single 1 1) := by
  rw [map_D]
  congr 1
  ext n
  simp [coeff_single]

/-- Coefficient extension is the unique semilinear map sending `dX` to `dX`. -/
theorem eq_map_of_apply_D_single_one (σ : K →+* L)
    (ℓ : ContinuousKaehlerDifferential K →ₛₗ[(mapRingHom σ : K⸨X⸩ →+* L⸨X⸩)]
      ContinuousKaehlerDifferential L)
    (h : ℓ (D K (single 1 1)) = D L (single 1 1)) : ℓ = map σ :=
  hom_ext <| by rw [h, map_D_single_one]

/-- Extending coefficients on continuous one-forms is injective. -/
theorem map_injective (σ : K →+* L) : Function.Injective (map σ) := by
  intro ω η h
  apply (equivLaurentSeries K).injective
  apply mapRingHom_injective σ.injective
  simpa only [equivLaurentSeries_map] using congrArg (equivLaurentSeries L) h

/-- Coefficient extension on continuous one-forms is continuous for the valuation topologies. -/
theorem continuous_map (σ : K →+* L) : Continuous (map σ) :=
  (equivLaurentSeries L).symm.continuous.comp
    ((TauCeti.LaurentSeries.continuous_mapRingHom σ).comp (equivLaurentSeries K).continuous)

/-- Extending coefficients by the identity embedding fixes each continuous one-form. -/
@[simp]
theorem map_id (ω : ContinuousKaehlerDifferential K) : map (RingHom.id K) ω = ω := by
  apply (equivLaurentSeries K).injective
  simp

/-- Extension of coefficients is functorial in field embeddings. -/
theorem map_comp (σ : K →+* L) (τ : L →+* M) (ω : ContinuousKaehlerDifferential K) :
    map (τ.comp σ) ω = map τ (map σ ω) := by
  apply (equivLaurentSeries M).injective
  simp [mapRingHom_comp]

open PowerSeries

/-- Extending coefficients commutes with substitution into continuous one-forms. The target
parameter `ψ` is explicit so that it can be supplied in a convenient normal form. -/
theorem map_subst (σ : K →+* L) {φ : K⟦X⟧} {ψ : L⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hψ : PowerSeries.constantCoeff ψ = 0) (hψ₀ : ψ ≠ 0)
    (h : PowerSeries.map σ φ = ψ) (ω : ContinuousKaehlerDifferential K) :
    map σ (subst hφ hφ₀ ω) = subst hψ hψ₀ (map σ ω) := by
  apply (equivLaurentSeries L).injective
  have hcoe : mapRingHom σ (φ : K⸨X⸩) = (ψ : L⸨X⸩) := by
    rw [mapRingHom_apply, map_ofPowerSeries, h]
  have hD : mapRingHom σ (LaurentSeries.derivative K (φ : K⸨X⸩)) =
      LaurentSeries.derivative L (ψ : L⸨X⸩) := by
    simpa only [equivLaurentSeries_map, equivLaurentSeries_D, hcoe] using
      congrArg (equivLaurentSeries L) (map_D σ (φ : K⸨X⸩))
  simp only [equivLaurentSeries_map, equivLaurentSeries_subst, map_mul,
    TauCeti.LaurentSeries.mapRingHom_substAlgHom hφ hφ₀ σ hψ hψ₀ h, hD]

/-- Coefficient extension intertwines the semilinear actions of a formal coordinate and its
coefficientwise image. -/
theorem map_substEquiv (σ : K →+* L) (φ : FormalCoordinate K)
    (ω : ContinuousKaehlerDifferential K) :
    map σ (substEquiv φ ω) = substEquiv (FormalCoordinate.map σ φ) (map σ ω) := by
  simp only [substEquiv_apply]
  exact map_subst σ _ _ _ _ (FormalCoordinate.toPowerSeries_map σ φ).symm ω

end TauCeti.ContinuousKaehlerDifferential
