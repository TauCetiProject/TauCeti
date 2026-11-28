/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Unitary elements of a field with a nontrivial involution

A field `K` of characteristic zero whose involution `star` is not the identity has infinitely many
unitary elements, that is elements `u` with `star u * u = 1`
(`Unitary.infinite_of_exists_star_ne`). If `w = z - star z ≠ 0`, then `star w = -w`, and the
quotients `(m + w) / (m - w)` for `m ∈ ℕ` are pairwise distinct elements of norm one. For a CM
field with complex conjugation these are the norm-one elements of the field, the unitary scalars
of every unitary group over it.
-/

public section

namespace Unitary

/-- **A field of characteristic zero with a nontrivial involution has infinitely many unitary
elements.** If `star z ≠ z` for some `z`, then `w = z - star z` satisfies `star w = -w`, and the
elements `(m + w) / (m - w)`, `m ∈ ℕ`, are unitary and pairwise distinct. -/
theorem infinite_of_exists_star_ne {K : Type*} [Field K] [CharZero K] [StarRing K]
    (h : ∃ z : K, star z ≠ z) : Infinite (unitary K) := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨w, hw, hsw⟩ : ∃ w : K, w ≠ 0 ∧ star w = -w :=
    ⟨z - star z, sub_ne_zero.2 (Ne.symm hz), by rw [star_sub, star_star, neg_sub]⟩
  -- `m ± w ≠ 0`: otherwise `w` would be the natural number `∓m`, fixed by `star`, so `w = 0`.
  have hadd : ∀ m : ℕ, (m : K) + w ≠ 0 := fun m hm ↦ hw <| by
    have h1 : w = -m := eq_neg_of_add_eq_zero_right hm
    have h2 : star w = -m := by rw [h1, star_neg, star_natCast]
    linear_combination (h1 - h2 + hsw) / 2
  have hsub : ∀ m : ℕ, (m : K) - w ≠ 0 := fun m hm ↦ hw <| by
    have h1 : w = m := (sub_eq_zero.1 hm).symm
    have h2 : star w = m := by rw [h1, star_natCast]
    linear_combination (h1 - h2 + hsw) / 2
  have hmem : ∀ m : ℕ, ((m : K) + w) / (m - w) ∈ unitary K := fun m ↦ by
    have hstar : star (((m : K) + w) / (m - w)) = (m - w) / (m + w) := by
      rw [star_div₀, star_add, star_sub, star_natCast, hsw, ← sub_eq_add_neg, sub_neg_eq_add]
    rw [mem_iff_star_mul_self, hstar, div_mul_div_comm, mul_comm ((m : K) - w),
      div_self (mul_ne_zero (hadd m) (hsub m))]
  refine Infinite.of_injective (fun m : ℕ ↦ ⟨_, hmem m⟩) fun m m' hmm' ↦ ?_
  -- Cross-multiplying `(m + w) (m' - w) = (m' + w) (m - w)` gives `2 (m' - m) w = 0`.
  have h := congrArg Subtype.val hmm'
  simp only at h
  rw [div_eq_div_iff (hsub m) (hsub m')] at h
  have h' : (2 * w) * ((m' : K) - m) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h0 | h0
  · exact absurd h0 (mul_ne_zero two_ne_zero hw)
  · exact_mod_cast (sub_eq_zero.1 h0).symm

end Unitary
