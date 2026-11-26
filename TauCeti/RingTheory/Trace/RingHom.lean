/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.Trace.Basic

/-!
# The trace as a sum over the extensions of a ring map

Mathlib's `trace_eq_sum_embeddings` writes the trace of a finite separable extension `L/K` as the
sum of the `K`-algebra maps `L → Ω` into an algebraically closed `K`-algebra `Ω`. This file states
it for an arbitrary ring map `φ₀ : K → Ω` in place of the algebra structure: `φ₀ (Tr_{L/K} x)` is
the sum of `φ x` over the ring maps `φ : L → Ω` extending `φ₀`. Summing over all `φ₀` in a set
then sums over all ring maps `L → Ω` whose restriction to `K` lies in that set, which is how traces
of induced data, such as induced CM types, are computed.

## Main results

* `RingHom.apply_trace_eq_finsum`: `φ₀ (Tr_{L/K} x) = ∑_{φ ∘ algebraMap K L = φ₀} φ x`.
-/

public section

namespace RingHom

variable {K L Ω : Type*} [Field K] [Field L] [Field Ω] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L] [IsAlgClosed Ω]

/-- For a finite separable extension `L/K` and a ring map `φ₀ : K → Ω` into an algebraically
closed field, `φ₀ (Tr_{L/K} x)` is the sum of `φ x` over the ring maps `φ : L → Ω` extending
`φ₀`. -/
theorem apply_trace_eq_finsum (φ₀ : K →+* Ω) (x : L) :
    φ₀ (Algebra.trace K L x) = ∑ᶠ φ ∈ {φ : L →+* Ω | φ.comp (algebraMap K L) = φ₀}, φ x := by
  let : Algebra K Ω := φ₀.toAlgebra
  have h := trace_eq_sum_embeddings Ω (K := K) (x := x)
  rw [RingHom.algebraMap_toAlgebra] at h
  rw [h, ← finsum_eq_sum_of_fintype, ← finsum_mem_univ]
  -- The `K`-algebra maps `L → Ω` are exactly the ring maps extending `φ₀`.
  refine finsum_mem_eq_of_bijOn (fun σ : L →ₐ[K] Ω ↦ (σ : L →+* Ω))
    ⟨fun σ _ ↦ σ.comp_algebraMap, fun σ _ τ _ h ↦ AlgHom.toRingHom_injective h,
      fun φ hφ ↦ ⟨{ toRingHom := φ, commutes' := RingHom.congr_fun hφ }, trivial, rfl⟩⟩
    fun _ _ ↦ rfl

end RingHom
