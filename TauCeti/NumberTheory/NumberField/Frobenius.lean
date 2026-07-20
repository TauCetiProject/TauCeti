/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.RingTheory.Frobenius

/-!
# Existence of Frobenius elements in Galois number fields

For a Galois number field `K/ℚ` and a nonzero prime `Q` of `𝓞 K`, Mathlib's
`IsArithFrobAt.exists_of_isInvariant` produces an arithmetic Frobenius at `Q` in `Gal(K/ℚ)`:
an automorphism `σ` with `σ x ≡ x ^ #(𝓞 K ⧸ Q ∩ ℤ) (mod Q)` for all `x : 𝓞 K`. This file
packages that existence with the number-field instances discharged — the residue field of a
nonzero prime is finite, and the Galois action on `𝓞 K` has invariants `ℤ` — in the form the
multiquadratic roadmap's Layer 1 consumes (`TauCeti.NumberTheory.Multiquadratic.Frobenius`
computes how these Frobenius elements act on the generators `√dᵢ`).

## Main results

* `TauCeti.NumberField.exists_isArithFrobAt`: a Frobenius exists at every nonzero prime.
* `TauCeti.NumberField.exists_isArithFrobAt_of_liesOver`: the specialization to a prime lying
  over a rational prime `p`.
-/

public section

open Ideal

open scoped NumberField

namespace TauCeti.NumberField

variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

/-- **Frobenius elements exist.** For a Galois number field `K/ℚ` and a nonzero prime `Q` of
`𝓞 K`, some `σ ∈ Gal(K/ℚ)` is an arithmetic Frobenius at `Q`. This is Mathlib's
`IsArithFrobAt.exists_of_isInvariant` with the number-field side conditions discharged. -/
theorem exists_isArithFrobAt (Q : Ideal (𝓞 K)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    ∃ σ : K ≃ₐ[ℚ] K, IsArithFrobAt ℤ σ Q := by
  haveI : Q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hQ ‹Q.IsPrime›
  exact IsArithFrobAt.exists_of_isInvariant ℤ (K ≃ₐ[ℚ] K) Q

/-- A Frobenius exists at every prime of `𝓞 K` lying over a rational prime `p`. -/
theorem exists_isArithFrobAt_of_liesOver {p : ℕ} [Fact p.Prime] (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})] :
    ∃ σ : K ≃ₐ[ℚ] K, IsArithFrobAt ℤ σ Q := by
  refine exists_isArithFrobAt K Q fun h0 => ?_
  -- If `Q` were zero it could not contain the image of `p`.
  have hp : algebraMap ℤ (𝓞 K) p ∈ Q :=
    (Ideal.mem_of_liesOver Q (span {(p : ℤ)}) (p : ℤ)).mp (mem_span_singleton_self _)
  rw [h0, Ideal.mem_bot] at hp
  exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast (FaithfulSMul.algebraMap_injective ℤ (𝓞 K)
    (hp.trans (map_zero _).symm)))

end TauCeti.NumberField
