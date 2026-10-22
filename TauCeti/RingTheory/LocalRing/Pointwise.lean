/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# The maximal-ideal filtration is invariant under ring automorphisms

A group acting on a local ring by ring automorphisms acts by surjective local homomorphisms, so it
fixes the maximal ideal and every one of its powers. This file records that invariance, both as an
equality of ideals for the pointwise action and in the membership form its consumers use.

## Main results

* `TauCeti.IsLocalRing.smul_maximalIdeal_pow`: the pointwise action fixes `𝔪 ^ n`.
* `TauCeti.IsLocalRing.smul_mem_maximalIdeal_pow`: the membership form of the same statement.
-/

public section

open IsLocalRing

open scoped Pointwise

namespace TauCeti.IsLocalRing

variable {G : Type*} [Group G] {S : Type*} [CommRing S] [IsLocalRing S] [MulSemiringAction G S]

/-- A group acting by ring automorphisms on a local ring fixes every power of the maximal ideal:
each automorphism is a surjective ring homomorphism, hence maps `𝔪` onto `𝔪`. -/
@[simp]
theorem smul_maximalIdeal_pow (σ : G) (n : ℕ) :
    σ • (maximalIdeal S ^ n) = maximalIdeal S ^ n := by
  have hsurj : Function.Surjective (MulSemiringAction.toRingHom G S σ) :=
    fun y ↦ ⟨σ⁻¹ • y, smul_inv_smul σ y⟩
  rw [Ideal.pointwise_smul_def, Ideal.map_pow,
    IsLocalRing.map_maximalIdeal_of_surjective _ hsurj]

/-- A group acting by ring automorphisms on a local ring preserves the powers of the maximal
ideal. -/
theorem smul_mem_maximalIdeal_pow (σ : G) {n : ℕ} {x : S} (hx : x ∈ maximalIdeal S ^ n) :
    σ • x ∈ maximalIdeal S ^ n := by
  rw [← smul_maximalIdeal_pow σ n]
  exact Ideal.smul_mem_pointwise_smul σ x _ hx

end TauCeti.IsLocalRing
