/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# The elements of one ideal congruent to one modulo another

For ideals `I` and `J` of a commutative ring, the elements of `I` congruent to `1` modulo `J` form
a coset of `I ⊓ J` inside `I`, translated by any one of them.  Such an element exists exactly when
`I` and `J` are coprime, and coprimality also turns `I ⊓ J` into `I * J`.

This is the shape a counting argument wants: the set is a translate of a fixed subgroup, so it can
be enumerated by translating that subgroup once.

## Main results

* `Ideal.isCoprime_iff_exists_mem_and_sub_one_mem`: the set is nonempty exactly when `I`
  and `J` are coprime;
* `Ideal.setOf_mem_and_sub_one_mem_eq_vadd_inf`: the set is a coset of `I ⊓ J`;
* `Ideal.setOf_mem_and_sub_one_mem_eq_vadd_mul`: the same coset written over `I * J`.
-/

public section

namespace Ideal

section Ring

variable {R : Type*} [Ring R] {I J : Ideal R}

open Pointwise in
/-- **The set is a coset of `I ⊓ J`.**  The elements of `I` congruent to `1` modulo `J` are a
translate of `I ⊓ J` by any one of them.  Only the additive structure of the ideals is used. -/
theorem setOf_mem_and_sub_one_mem_eq_vadd_inf {ξ : R} (hξI : ξ ∈ I) (hξJ : ξ - 1 ∈ J) :
    {x : R | x ∈ I ∧ x - 1 ∈ J} = ξ +ᵥ ((I ⊓ J : Ideal R) : Set R) := by
  ext x
  constructor
  · rintro ⟨hxI, hxJ⟩
    -- the difference of two elements is in `I` because both are, and in `J` because both are `1`
    refine ⟨x - ξ, ⟨I.sub_mem hxI hξI, ?_⟩, add_sub_cancel ξ x⟩
    simpa using J.sub_mem hxJ hξJ
  · rintro ⟨d, ⟨hdI, hdJ⟩, rfl⟩
    refine ⟨I.add_mem hξI hdI, ?_⟩
    -- `ξ +ᵥ d` is `ξ + d` by definition of the additive action of a ring on itself; no
    -- simp lemma states this, because `vadd_eq_add` is about the unbundled `+ᵥ` and the goal
    -- here is the beta-unreduced application left by `rintro`.
    change ξ + d - 1 ∈ J
    have : ξ + d - 1 = ξ - 1 + d := by abel
    rw [this]
    exact J.add_mem hξJ hdJ

end Ring

section CommRing

variable {R : Type*} [CommRing R] {I J : Ideal R}

/-- **Coprimality is the existence of an element of `I` congruent to one modulo `J`.**  Writing
`1` as a sum of an element of each ideal is the same data as such an element. -/
theorem isCoprime_iff_exists_mem_and_sub_one_mem :
    IsCoprime I J ↔ ∃ x, x ∈ I ∧ x - 1 ∈ J := by
  rw [isCoprime_iff_exists]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨a, ha, ?_⟩
    have : a - 1 = -b := by rw [← hab]; ring
    rw [this]
    exact J.neg_mem hb
  · rintro ⟨x, hxI, hxJ⟩
    refine ⟨x, hxI, 1 - x, ?_, by ring⟩
    have : 1 - x = -(x - 1) := by ring
    rw [this]
    exact J.neg_mem hxJ

open Pointwise in
/-- **The set is a coset of `I * J`.**  The elements of `I` congruent to `1` modulo `J` are a
translate of `I * J` by any one of them. -/
theorem setOf_mem_and_sub_one_mem_eq_vadd_mul {ξ : R} (hξI : ξ ∈ I) (hξJ : ξ - 1 ∈ J) :
    {x : R | x ∈ I ∧ x - 1 ∈ J} = ξ +ᵥ ((I * J : Ideal R) : Set R) := by
  -- the `Ideal R` ascription keeps `*` the ideal product: `open Pointwise` also gives `Set R` one
  rw [mul_eq_inf_of_isCoprime (isCoprime_iff_exists_mem_and_sub_one_mem.mpr ⟨ξ, hξI, hξJ⟩),
    setOf_mem_and_sub_one_mem_eq_vadd_inf hξI hξJ]

end CommRing

end Ideal
