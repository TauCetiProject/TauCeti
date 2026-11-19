/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs

/-!
# Basic facts about submonoid classes

An element outside any `OneMemClass` subset differs from `1`; additively, an element outside any
`ZeroMemClass` subset (such as an additive submonoid, subgroup, ideal, or submodule) is nonzero.

If elements of a submonoid `P` can be moved past `z` to the right, then powers of `z * w` with
`w ∈ P` factor as `z ^ n` times an element of `P`.

## Main results

* `TauCeti.ne_one_of_notMem` and `TauCeti.ne_zero_of_notMem`: `x ∉ s → x ≠ 1` and `x ∉ s → x ≠ 0`.
* `TauCeti.exists_mul_pow_eq_pow_mul_of_mem`: if `P * z ⊆ z * P` and `w ∈ P`, then
  `(z * w) ^ n = z ^ n * v` for some `v ∈ P`.
-/

public section

namespace TauCeti

/-- An element outside a subset containing `1` is not `1`. -/
@[to_additive /-- An element outside a subset containing `0` is nonzero. -/]
theorem ne_one_of_notMem {S M : Type*} [One M] [SetLike S M] [OneMemClass S M] {s : S} {x : M}
    (hx : x ∉ s) : x ≠ 1 :=
  (ne_of_mem_of_not_mem (one_mem s) hx).symm

/-- If every element `a ∈ P` satisfies `a * z = z * b` for some `b ∈ P`, then for every `w ∈ P`
and `n : ℕ`, the power `(z * w) ^ n` equals `z ^ n * v` for some `v ∈ P`. -/
theorem exists_mul_pow_eq_pow_mul_of_mem {M S : Type*} [Monoid M] [SetLike S M]
    [SubmonoidClass S M] {P : S} {z w : M}
    (hz : ∀ a ∈ P, ∃ b ∈ P, a * z = z * b) (hw : w ∈ P) (n : ℕ) :
    ∃ v ∈ P, (z * w) ^ n = z ^ n * v := by
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
    obtain ⟨v, hv, he⟩ := ih
    obtain ⟨b, hb, hf⟩ := hz v hv
    refine ⟨b * w, mul_mem hb hw, ?_⟩
    calc
      (z * w) ^ (n + 1) = z ^ n * (v * z) * w := by rw [pow_succ, he]; simp [mul_assoc]
      _ = z ^ (n + 1) * (b * w) := by rw [hf, pow_succ]; simp [mul_assoc]

end TauCeti

end
