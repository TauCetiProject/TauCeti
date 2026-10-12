/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Constant coefficients in polynomial local rings

The constant coefficient map from a multivariate polynomial ring over a local ring extends to
the localization at the preimage of the coefficient ring's maximal ideal. It detects when a
polynomial is outside the square of the maximal ideal of that localization.

## Main results

* `TauCeti.algebraMap_notMem_maximalIdeal_sq`: a polynomial whose constant coefficient is
  outside the square of the coefficient ring's maximal ideal remains outside the square after
  localization.
-/

public section

namespace TauCeti

open _root_.IsLocalRing Ideal MvPolynomial

variable {R σ : Type*} [CommRing R] [IsLocalRing R]

/-- A polynomial whose constant coefficient is not in `𝔪_R²` does not lie in the square of the
maximal ideal of `R[σ]_𝔪`: the constant coefficient extends to `R[σ]_𝔪 → R`, which maps the
maximal ideal into `𝔪_R`. -/
lemma algebraMap_notMem_maximalIdeal_sq {p : MvPolynomial σ R}
    (hp : constantCoeff p ∉ maximalIdeal R ^ 2) :
    algebraMap (MvPolynomial σ R)
        (Localization.AtPrime ((maximalIdeal R).comap (constantCoeff (σ := σ)))) p ∉
      maximalIdeal
        (Localization.AtPrime ((maximalIdeal R).comap (constantCoeff (σ := σ)))) ^ 2 := by
  set 𝔪 := (maximalIdeal R).comap (constantCoeff : MvPolynomial σ R →+* R)
  let φ : Localization.AtPrime 𝔪 →+* R :=
    IsLocalization.lift (M := 𝔪.primeCompl) (g := constantCoeff) fun s ↦
      notMem_maximalIdeal.mp s.2
  have hφ : φ.comp (algebraMap _ _) = constantCoeff := IsLocalization.lift_comp _
  have hmap : (maximalIdeal (Localization.AtPrime 𝔪)).map φ ≤ maximalIdeal R := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hφ]
    exact map_comap_le
  refine fun h ↦ hp ?_
  rw [← hφ, RingHom.comp_apply, pow_two]
  rw [pow_two] at h
  exact mul_mono hmap hmap (Ideal.map_mul φ _ _ ▸ mem_map_of_mem φ h)

end TauCeti
