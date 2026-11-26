/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.TracePairing.Basic

/-!
# Checks for the naturality of the trace pairing along `ℂ → ℂ²`

Take `φ : ℂ → ℂ²`, `λ ↦ (λ, 0)`, and the positive tracial functional `τ(a, b) = b` on `ℂ²`,
`TauCeti.sndTracialFunctional`. The pullback `τ ∘ φ` is the zero functional
(`TauCeti.sndTracialFunctional_comp_inl`): a positive tracial functional that is not a state
(`TauCeti.not_isTracialState_sndTracialFunctional_comp_inl`). Both sides of the naturality
`(τ ∘ φ)_* = τ_* ∘ φ_*` vanish at `[1]`: `(τ ∘ φ)_* [1] = 0 = τ(1, 0) = τ_* (φ_* [1])`. A pairing
defined only for tracial states would leave the left side undefined.
-/

public section

open Matrix Algebra
open scoped ComplexOrder

namespace TauCeti.ProdTracePairingExample

/-- `(τ ∘ φ)_* [1] = 0`. -/
theorem kZeroPairing_comp_inl_of_mk_one :
    (sndTracialFunctional.comp (NonUnitalStarAlgHom.inl ℂ ℂ ℂ)).kZeroPairing
      (GrothendieckAddGroup.of (ProjectionMonoid.mk (1 : Matrix (Fin 1) (Fin 1) ℂ) (.one _))) =
        0 := by
  rw [PositiveTracialFunctional.kZeroPairing_of_mk_one]
  simp [sndTracialFunctional_comp_inl]

/-- `τ_* (φ_* [1]) = τ(1, 0) = 0`, as naturality requires. -/
theorem kZeroPairing_map_inl_of_mk_one :
    sndTracialFunctional.kZeroPairing (ProjectionKZero.map
      (NonUnitalStarRingHom.ofClass (NonUnitalStarAlgHom.inl ℂ ℂ ℂ))
        (GrothendieckAddGroup.of (ProjectionMonoid.mk (1 : Matrix (Fin 1) (Fin 1) ℂ) (.one _)))) =
      (sndTracialFunctional (1, 0)).re := by
  rw [← AddMonoidHom.comp_apply, ← PositiveTracialFunctional.kZeroPairing_comp,
    kZeroPairing_comp_inl_of_mk_one]
  simp

end TauCeti.ProdTracePairingExample
