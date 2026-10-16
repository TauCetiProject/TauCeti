/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card

/-!
# Cardinalities of preimages under division

For `n > 0`, every natural number `j` is the quotient `i / n` of exactly the `n` natural numbers
`n * j, …, n * j + n - 1`. Hence for `n > 0` the preimage of a finite set `S ⊆ ℕ` under
`i ↦ i / n` has `n` times as many elements as `S`. This is the counting fact behind sequences that
repeat each term `n` times, such as the singular values of a block sum of `n` copies of one map.

The statement `Set.ncard_preimage_div` needs no hypotheses: `Set.ncard` is `0` on infinite sets,
and `i / 0 = 0` makes the preimage under division by zero either `∅` or all of `ℕ`, so both
sides are `0` when `S` is infinite or `n = 0`.
-/

public section

namespace Set

/-- The preimage of a set `S ⊆ ℕ` under `i ↦ i / n` has `n` times as many elements as `S`. Both
sides are `0` when `S` is infinite or `n = 0`. -/
theorem ncard_preimage_div (S : Set ℕ) (n : ℕ) : ((· / n) ⁻¹' S).ncard = S.ncard * n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · -- Division by zero is constantly zero, so the preimage is `∅` or all of `ℕ`.
    by_cases h0 : 0 ∈ S
    · simp [Set.preimage, Nat.div_zero, h0]
    · simp [Set.preimage, Nat.div_zero, h0]
  have h : (· / n) ⁻¹' S = (fun p : ℕ × Fin n ↦ n * p.1 + p.2) '' (S ×ˢ univ) := by
    ext i
    simp only [mem_preimage, mem_image, mem_prod, mem_univ, and_true, Prod.exists]
    refine ⟨fun hi ↦ ⟨i / n, ⟨i % n, Nat.mod_lt _ hn⟩, hi, Nat.div_add_mod i n⟩, ?_⟩
    rintro ⟨j, b, hj, rfl⟩
    rwa [Nat.mul_add_div hn, Nat.div_eq_of_lt b.isLt, add_zero]
  rw [h, ncard_image_of_injective _ fun p q hpq ↦ ?_, ncard_prod, ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  have hp := p.2.isLt
  have hq := q.2.isLt
  have h₁ : p.1 = q.1 := by
    simpa [Nat.mul_add_div hn, Nat.div_eq_of_lt hp, Nat.div_eq_of_lt hq] using
      congrArg (· / n) hpq
  exact Prod.ext h₁ (Fin.ext (by simpa [h₁] using hpq))

end Set
