/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace
public import TauCeti.Analysis.CStarAlgebra.TracePairing.Basic

/-!
# Checks for the trace pairing of the normalized trace of `Mₙ(ℂ)`

Take `A = Mₙ(ℂ)`, `n ≥ 1`, with its normalized trace `τ = tr / n`, a tracial state. The
rank-one projection `e₀₀ = CStarMatrix.matrixUnit 0 0` of `A`, a `1 × 1` matrix over `A`, pairs
to `1 / n`, while the identity of `M_k(A)` pairs to `k`:
the pairing uses the unnormalized matrix trace over `A`, so the size `k` of the matrix over `A` is
not divided out, only the normalization of `τ` on `A` itself.
-/

public section

open Matrix Algebra
open scoped ComplexOrder

namespace TauCeti.NormalizedTracePairingExample

variable (n : ℕ)

/-- The normalized trace `tr / n` of `Mₙ(ℂ)` as a positive tracial functional. -/
noncomputable def normalizedTrace : PositiveTracialFunctional (CStarMatrix (Fin n) (Fin n) ℂ) :=
  .ofMapMulComm (CStarMatrix.normalizedTraceMap (Fin n)) CStarMatrix.normalizedTraceMap_mul_comm

@[simp]
theorem normalizedTrace_apply (x : CStarMatrix (Fin n) (Fin n) ℂ) :
    normalizedTrace n x = CStarMatrix.normalizedTrace x := by
  simp [normalizedTrace, CStarMatrix.normalizedTraceMap_apply]

variable [NeZero n]

/-- The rank-one projection `e₀₀ = CStarMatrix.matrixUnit 0 0`, written as a `1 × 1` matrix over
`Mₙ(ℂ)`, is a projection. -/
theorem isStarProjection_of_matrixUnit :
    IsStarProjection (of fun (_ _ : Fin 1) ↦ CStarMatrix.matrixUnit (0 : Fin n) 0) := by
  have h := CStarMatrix.isStarProjection_matrixUnit (0 : Fin n)
  refine ⟨?_, ?_⟩
  · ext i j
    simp [Matrix.mul_apply, h.isIdempotentElem.eq]
  · ext i j
    simp [h.isSelfAdjoint.star_eq]

/-- The rank-one projection `e₀₀` pairs to `1 / n` under the normalized trace. -/
theorem normalizedTrace_kZeroPairing_of_mk_matrixUnit :
    (normalizedTrace n).kZeroPairing
      (GrothendieckAddGroup.of (ProjectionMonoid.mk _ (isStarProjection_of_matrixUnit n))) =
        1 / n := by
  rw [PositiveTracialFunctional.kZeroPairing_of_mk]
  simp [CStarMatrix.normalizedTrace_matrixUnit]

/-- The identity of `M_k(Mₙ(ℂ))` pairs to `k` under the normalized trace. -/
theorem normalizedTrace_kZeroPairing_of_mk_one (k : ℕ) :
    (normalizedTrace n).kZeroPairing (GrothendieckAddGroup.of
      (ProjectionMonoid.mk (1 : Matrix (Fin k) (Fin k) (CStarMatrix (Fin n) (Fin n) ℂ))
        (.one _))) = k := by
  rw [PositiveTracialFunctional.kZeroPairing_of_mk_one]
  simp [CStarMatrix.normalizedTrace_one]

end TauCeti.NormalizedTracePairingExample
