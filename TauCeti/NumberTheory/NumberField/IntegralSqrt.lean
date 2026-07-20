/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Square roots of integers as algebraic integers

An element `x` of a field `K` with `x² = d` for an integer `d` is a root of the monic
`X² - d`, hence integral over `ℤ`; this file packages such an `x` as an element
`TauCeti.NumberField.integralSqrt hx` of the ring of integers `𝓞 K`, together with its two
defining identities (its image in `K` is `x`, and it squares to `d` in `𝓞 K`). It also
records the compatibility `TauCeti.NumberField.algebraMap_smul` between the Galois action on
`𝓞 K` and the action on `K`, the bridge for moving such identities between the two rings.

This is the shared square-root packaging used by the multiquadratic Layer 1 files: the
splitting law (`TauCeti.NumberTheory.Multiquadratic.MultiquadraticSplitting`) moves the
generators `√dᵢ` into `𝓞 K` to compare residues, and the Frobenius computation
(`TauCeti.NumberTheory.NumberField.Frobenius`) applies the arithmetic-Frobenius congruence,
which lives on `𝓞 K`, to a square root.

## Main definitions and results

* `TauCeti.NumberField.isIntegral_of_sq_intCast`: a square root of an integer is integral.
* `TauCeti.NumberField.integralSqrt`: the packaging in `𝓞 K`, with
  `TauCeti.NumberField.algebraMap_integralSqrt` and `TauCeti.NumberField.integralSqrt_sq`.
* `TauCeti.NumberField.algebraMap_smul`: the Galois action on `𝓞 K` is the restriction of
  the action on `K`.
-/

public section

open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] {x : K} {d : ℤ}

/-- A square root of an integer is an algebraic integer: it is a root of the monic
`X² - d`. -/
theorem isIntegral_of_sq_intCast (hx : x ^ 2 = algebraMap ℤ K d) : IsIntegral ℤ x :=
  ⟨Polynomial.X ^ 2 - Polynomial.C d,
    Polynomial.monic_X_pow_sub_C d (by norm_num), by
      rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hx, sub_self]⟩

/-- A square root `x` of an integer `d`, packaged as an element of the ring of integers. -/
noncomputable def integralSqrt (hx : x ^ 2 = algebraMap ℤ K d) : 𝓞 K :=
  ⟨x, isIntegral_of_sq_intCast hx⟩

/-- Under `𝓞 K ↪ K`, `TauCeti.NumberField.integralSqrt hx` maps back to `x`. -/
@[simp] theorem algebraMap_integralSqrt (hx : x ^ 2 = algebraMap ℤ K d) :
    algebraMap (𝓞 K) K (integralSqrt hx) = x :=
  NumberField.RingOfIntegers.map_mk x _

/-- `TauCeti.NumberField.integralSqrt hx` squares to the radicand `d` in `𝓞 K`. -/
theorem integralSqrt_sq (hx : x ^ 2 = algebraMap ℤ K d) :
    integralSqrt hx ^ 2 = algebraMap ℤ (𝓞 K) d := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [map_pow, algebraMap_integralSqrt, ← IsScalarTower.algebraMap_apply ℤ (𝓞 K) K]
  exact hx

/-- The Galois action on `𝓞 K` is the restriction of the action on `K`: it agrees with
`galRestrict ℤ ℚ K (𝓞 K) σ` (both restrict `σ`, and they are pinned by injectivity of the
algebra map), so the compatibility is `algebraMap_galRestrict_apply`. -/
theorem algebraMap_smul [NumberField K] (σ : K ≃ₐ[ℚ] K) (y : 𝓞 K) :
    algebraMap (𝓞 K) K (σ • y) = σ (algebraMap (𝓞 K) K y) := by
  have hgal : galRestrict ℤ ℚ K (𝓞 K) σ y = σ • y := by
    apply FaithfulSMul.algebraMap_injective (𝓞 K) K
    rw [algebraMap_galRestrict_apply (A := ℤ) σ y]
    exact (integralClosure.coe_smul σ y).symm
  rw [← hgal, algebraMap_galRestrict_apply (A := ℤ) σ y]

end TauCeti.NumberField
