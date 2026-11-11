/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# The maximal-ideal filtration is invariant under ring automorphisms

A group acting on a local (commutative) semiring by ring automorphisms sends the maximal ideal to a
maximal ideal, hence fixes it and every one of its powers. This file records that invariance, both
as an equality of ideals for the pointwise action and in membership form.

## Main results

* `TauCeti.IsLocalRing.smul_maximalIdeal`: the pointwise action fixes `𝔪`.
* `TauCeti.IsLocalRing.smul_maximalIdeal_pow`: the pointwise action fixes `𝔪 ^ n`.
* `TauCeti.IsLocalRing.smul_mem_maximalIdeal_pow_iff`: the membership form of the same
  statement.
-/

public section

open IsLocalRing

open scoped Pointwise

namespace TauCeti.IsLocalRing

variable {G : Type*} [Group G] {S : Type*} [CommSemiring S] [IsLocalRing S]
  [MulSemiringAction G S]

/-- A group acting by ring automorphisms on a local ring fixes its maximal ideal. -/
@[simp] theorem smul_maximalIdeal (σ : G) : σ • maximalIdeal S = maximalIdeal S := by
  rw [Ideal.pointwise_smul_eq_comap]
  exact eq_maximalIdeal inferInstance

/-- A group acting by ring automorphisms on a local ring fixes every power of the maximal
ideal. -/
@[simp] theorem smul_maximalIdeal_pow (σ : G) (n : ℕ) :
    σ • (maximalIdeal S ^ n) = maximalIdeal S ^ n := by
  rw [Ideal.pointwise_smul_def, Ideal.map_pow, ← Ideal.pointwise_smul_def, smul_maximalIdeal]

/-- An automorphism from a group acting on a local ring moves an element into a power of the
maximal ideal if and only if the element already lies in it. -/
@[simp] theorem smul_mem_maximalIdeal_pow_iff (σ : G) {n : ℕ} {x : S} :
    σ • x ∈ maximalIdeal S ^ n ↔ x ∈ maximalIdeal S ^ n := by
  rw [← Ideal.mem_inv_pointwise_smul_iff, smul_maximalIdeal_pow]

end TauCeti.IsLocalRing
