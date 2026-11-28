/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# The trace ideal of a matrix representation

For a ring homomorphism `ρ : Λ →+* Matrix σ σ L` and an additive subgroup `𝒥` of `L`, the trace
ideal `TauCeti.traceIdeal ρ 𝒥` is the two-sided ideal of the `w ∈ Λ` such that `tr ρ (w * s) ∈ 𝒥`
for every `s ∈ Λ`. It contains the kernel of `ρ`, and it is the ideal `𝔞` to which Ribet's method
(`AlgHom.exists_ribet_polynomial`) is applied when the traces of a family of representations are
controlled by `𝒥`.

## Main definitions

* `TauCeti.traceIdeal`: the two-sided ideal of the `w ∈ Λ` with `tr ρ (w * s) ∈ 𝒥` for all `s`.

## Main results

* `TauCeti.mem_traceIdeal`: the membership criterion.
* `TauCeti.trace_mem_of_mem_traceIdeal`: an element of the trace ideal has its trace in `𝒥`.
* `TauCeti.mem_traceIdeal_of_map_eq_zero`: the kernel of `ρ` lies in the trace ideal.

## Provenance

`TauCeti.traceIdeal` follows `New.Selmer.traceIdeal` (file
`src/New/Congruences/FirstOrder/RibetMethod.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

open Matrix

namespace TauCeti

variable {Λ σ L F : Type*} [Ring Λ] [CommRing L] [Fintype σ] [DecidableEq σ]
  [FunLike F Λ (Matrix σ σ L)] [RingHomClass F Λ (Matrix σ σ L)]

/-- The trace ideal of `𝒥` along `ρ`: the two-sided ideal of the `w ∈ Λ` such that the trace of
`ρ (w * s)` lies in `𝒥` for every `s ∈ Λ`. It is a two-sided ideal because the trace is cyclic. -/
def traceIdeal (ρ : F) (𝒥 : AddSubgroup L) : TwoSidedIdeal Λ :=
  .mk' {w | ∀ s, (ρ (w * s)).trace ∈ 𝒥} (by simp)
    (fun hw hw' s ↦ by simpa [add_mul] using add_mem (hw s) (hw' s))
    (fun hw s ↦ by simpa using neg_mem (hw s))
    (fun {w w'} hw' s ↦ by simpa [mul_assoc, trace_mul_comm (ρ w)] using hw' (s * w))
    (fun {w w'} hw s ↦ by simpa [mul_assoc] using hw (w' * s))

@[simp]
theorem mem_traceIdeal {ρ : F} {𝒥 : AddSubgroup L} {w : Λ} :
    w ∈ traceIdeal ρ 𝒥 ↔ ∀ s, (ρ (w * s)).trace ∈ 𝒥 :=
  TwoSidedIdeal.mem_mk' ..

/-- An element of the trace ideal of `𝒥` has its trace in `𝒥`. -/
theorem trace_mem_of_mem_traceIdeal {ρ : F} {𝒥 : AddSubgroup L} {w : Λ}
    (hw : w ∈ traceIdeal ρ 𝒥) : (ρ w).trace ∈ 𝒥 := by
  simpa using mem_traceIdeal.1 hw 1

/-- The kernel of `ρ` lies in every trace ideal along `ρ`. -/
theorem mem_traceIdeal_of_map_eq_zero {ρ : F} (𝒥 : AddSubgroup L) {w : Λ} (hw : ρ w = 0) :
    w ∈ traceIdeal ρ 𝒥 := by
  simp [hw]

end TauCeti
