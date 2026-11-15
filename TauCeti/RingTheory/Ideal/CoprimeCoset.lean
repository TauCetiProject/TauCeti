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
  simp only [Set.mem_ofPred_eq, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub,
    SetLike.mem_coe, mem_inf]
  -- `x - ξ` lies in `I` iff `x` does; as `(x - 1) - (ξ - 1)`, it lies in `J` iff `x - 1` does
  rw [I.sub_mem_iff_left hξI, ← sub_sub_sub_cancel_right x ξ 1, J.sub_mem_iff_left hξJ]

end Ring

section CommRing

variable {R : Type*} [CommRing R] {I J : Ideal R}

/-- **Coprimality is the existence of an element of `I` congruent to one modulo `J`.**  Writing
`1` as a sum of an element of each ideal is the same data as such an element. -/
theorem isCoprime_iff_exists_mem_and_sub_one_mem :
    IsCoprime I J ↔ ∃ x ∈ I, x - 1 ∈ J := by
  rw [isCoprime_iff_exists]
  refine ⟨fun ⟨a, ha, b, hb, hab⟩ ↦ ⟨a, ha, ?_⟩,
    fun ⟨x, hx, hx1⟩ ↦ ⟨x, hx, 1 - x, ?_, add_sub_cancel x 1⟩⟩
  · rw [← hab, sub_add_cancel_left]
    exact neg_mem hb
  · rw [← neg_sub]
    exact neg_mem hx1

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
