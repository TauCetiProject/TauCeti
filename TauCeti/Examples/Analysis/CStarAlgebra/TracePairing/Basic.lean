/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.TracePairing.Basic

/-!
# Checks for the trace pairing with `K₀`

For `A = ℂ` with the identity functional `τ = id`, a tracial state, the unnormalized matrix trace
pairs the identity matrix of size `k` with `k`, and the rank-one projection `diag(1, 0)` in
`M₂(ℂ)` with `1`. A pairing through the normalized matrix trace would give `1` and `1 / 2`.
-/

public section

open Matrix Algebra
open scoped ComplexOrder

namespace TauCeti.TracePairingExample

/-- The identity of `ℂ` as a positive tracial functional. -/
noncomputable def idTrace : PositiveTracialFunctional ℂ :=
  .ofMapMulComm (PositiveContinuousLinearMap.id ℂ ℂ) fun a b ↦ by simp [mul_comm]

@[simp]
theorem idTrace_apply (z : ℂ) : idTrace z = z := by
  simp [idTrace]

/-- The identity matrix of size `k` pairs to `k` with the identity trace on `ℂ`. -/
theorem idTrace_kZeroPairing_of_mk_one (k : ℕ) :
    idTrace.kZeroPairing (GrothendieckAddGroup.of
      (ProjectionMonoid.mk (1 : Matrix (Fin k) (Fin k) ℂ) (.one _))) = k := by
  rw [PositiveTracialFunctional.kZeroPairing_of_mk_one]
  simp [idTrace]

/-- `diag(1, 0)` is a projection in `M₂(ℂ)`. -/
theorem isStarProjection_single : IsStarProjection (single (0 : Fin 2) (0 : Fin 2) (1 : ℂ)) := by
  refine ⟨?_, ?_⟩ <;> simp [IsIdempotentElem, IsSelfAdjoint, star_eq_conjTranspose]

/-- The rank-one projection `diag(1, 0)` in `M₂(ℂ)` pairs to `1`, not to `1 / 2`. -/
theorem idTrace_kZeroPairing_of_mk_single :
    idTrace.kZeroPairing (GrothendieckAddGroup.of
      (ProjectionMonoid.mk _ isStarProjection_single)) = 1 := by
  rw [PositiveTracialFunctional.kZeroPairing_of_mk]
  simp [idTrace, single_apply]

end TauCeti.TracePairingExample
