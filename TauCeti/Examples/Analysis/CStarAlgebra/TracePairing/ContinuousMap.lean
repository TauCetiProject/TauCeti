/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Star
public import TauCeti.Examples.Analysis.CStarAlgebra.TracePairing.Basic
import TauCeti.LinearAlgebra.Trace.Idempotent

/-!
# Check: the trace pairing on `C(X)` is the rank at a point

For a compact space `X`, a point `x ∈ X` and the evaluation `τ = δ_x` at `x`, a positive
tracial functional on `C(X)`, the trace pairing sends the class of a projection `p ∈ M_m(C(X))` to
the unnormalized trace `Σᵢ pᵢᵢ(x)` of the projection `p(x) ∈ M_m(ℂ)`, which is the rank of `p(x)`
(the rank of the bundle of `p` at `x`): a natural number. A pairing through the normalized matrix
trace would give that rank divided by `m`; for the identity of `M_m(C(X))` the pairing is `m`.
-/

public section

open Matrix Algebra
open scoped ComplexOrder

namespace TauCeti.TracePairingExample

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] {m : Type*} [Fintype m]

/-- The evaluation `δ_x` at a point `x` as a positive tracial functional on `C(X)`. -/
noncomputable def evalTrace (x : X) : PositiveTracialFunctional C(X, ℂ) :=
  idTrace.comp (ContinuousMap.evalStarAlgHom ℂ ℂ x)

@[simp]
theorem evalTrace_apply (x : X) (f : C(X, ℂ)) : evalTrace x f = f x := by
  simp [evalTrace]

/-- **The pairing with `δ_x` is the rank at `x`.** The class of a projection `p ∈ M_m(C(X))` pairs
with the evaluation at `x` to the rank of the matrix projection `p(x) ∈ M_m(ℂ)`. -/
theorem evalTrace_kZeroPairing_of_mk (x : X) {p : Matrix m m C(X, ℂ)} (hp : IsStarProjection p) :
    (evalTrace x).kZeroPairing (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp)) =
      (p.map fun f ↦ f x).rank := by
  classical
  have hmap : (ContinuousMap.evalAlgHom ℂ ℂ x).mapMatrix p = p.map fun f ↦ f x := by
    ext; simp
  have hidem : IsIdempotentElem (p.map fun f ↦ f x) :=
    hmap ▸ hp.isIdempotentElem.map (ContinuousMap.evalAlgHom ℂ ℂ x).mapMatrix
  have htr := hidem.trace_eq_rank
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply] at htr
  rw [PositiveTracialFunctional.kZeroPairing_of_mk]
  simp only [evalTrace_apply]
  rw [htr]
  simp

/-- The pairing with `δ_x` of the class of a projection is a natural number. -/
theorem exists_evalTrace_kZeroPairing_of_mk_eq_natCast (x : X) {p : Matrix m m C(X, ℂ)}
    (hp : IsStarProjection p) :
    ∃ k : ℕ, (evalTrace x).kZeroPairing (GrothendieckAddGroup.of (ProjectionMonoid.mk p hp)) = k :=
  ⟨_, evalTrace_kZeroPairing_of_mk x hp⟩

/-- The identity of `M_k(C(X))` pairs with `δ_x` to `k`, not to `1`. -/
theorem evalTrace_kZeroPairing_of_mk_one (x : X) (k : ℕ) :
    (evalTrace x).kZeroPairing (GrothendieckAddGroup.of
      (ProjectionMonoid.mk (1 : Matrix (Fin k) (Fin k) C(X, ℂ)) (.one _))) = k := by
  rw [PositiveTracialFunctional.kZeroPairing_of_mk_one]
  simp

end TauCeti.TracePairingExample
