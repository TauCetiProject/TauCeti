/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.TracePairing.Basic

/-!
# Checks for the naturality of the trace pairing along `ℂ → ℂ²`

Take `φ : ℂ → ℂ²`, `λ ↦ (λ, 0)`, and the positive tracial functional `τ(a, b) = b` on `ℂ²`
(OperatorKTheory K1.5, fourth Check). The pullback `τ ∘ φ` is the zero functional: a positive
tracial functional that is not a state, since it vanishes at `1`. Both sides of the naturality
`(τ ∘ φ)_* = τ_* ∘ φ_*` vanish at `[1]`: `(τ ∘ φ)_* [1] = 0 = τ(1, 0) = τ_* (φ_* [1])`. A pairing
defined only for tracial states would leave the left side undefined.
-/

public section

open Matrix Algebra
open scoped ComplexOrder

namespace TauCeti.ProdTracePairingExample

/-- The positive tracial functional `τ(a, b) = b` on `ℂ²`. -/
noncomputable def sndTrace : PositiveTracialFunctional (ℂ × ℂ) where
  toPositiveLinearMap := PositiveLinearMap.mk₀ (LinearMap.snd ℂ ℂ ℂ) fun _ hx ↦ hx.2
  map_mul_comm' a b := by simp [mul_comm]

@[simp]
theorem sndTrace_apply (x : ℂ × ℂ) : sndTrace x = x.2 :=
  (rfl)

/-- The pullback of `τ(a, b) = b` along `λ ↦ (λ, 0)` is the zero functional. -/
theorem sndTrace_comp_inl : sndTrace.comp (NonUnitalStarAlgHom.inl ℂ ℂ ℂ) = 0 :=
  PositiveTracialFunctional.ext fun _ ↦ by simp [PositiveTracialFunctional.comp_apply]

/-- The pullback `τ ∘ φ` is not a state: it vanishes at `1`. -/
theorem sndTrace_comp_inl_one : sndTrace.comp (NonUnitalStarAlgHom.inl ℂ ℂ ℂ) 1 = 0 := by
  simp [sndTrace_comp_inl]

/-- `(τ ∘ φ)_* [1] = 0`. -/
theorem kZeroPairing_comp_inl_of_mk_one :
    (sndTrace.comp (NonUnitalStarAlgHom.inl ℂ ℂ ℂ)).kZeroPairing
      (GrothendieckAddGroup.of (ProjectionMonoid.mk (1 : Matrix (Fin 1) (Fin 1) ℂ) (.one _))) =
        0 := by
  rw [PositiveTracialFunctional.kZeroPairing_of_mk_one]
  simp [sndTrace_comp_inl]

/-- `τ_* (φ_* [1]) = τ(1, 0) = 0`, as naturality requires. -/
theorem kZeroPairing_map_inl_of_mk_one :
    sndTrace.kZeroPairing (ProjectionKZero.map
      (NonUnitalStarRingHom.ofClass (NonUnitalStarAlgHom.inl ℂ ℂ ℂ))
        (GrothendieckAddGroup.of (ProjectionMonoid.mk (1 : Matrix (Fin 1) (Fin 1) ℂ) (.one _)))) =
      (sndTrace (1, 0)).re := by
  rw [← AddMonoidHom.comp_apply, ← PositiveTracialFunctional.kZeroPairing_comp,
    kZeroPairing_comp_inl_of_mk_one]
  simp

end TauCeti.ProdTracePairingExample
