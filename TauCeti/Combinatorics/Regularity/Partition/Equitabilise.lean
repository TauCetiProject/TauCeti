/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise
import Mathlib.Tactic.Ring
import TauCeti.Order.Partition.Finpartition

/-!
# Equitable exact refinements of equipartitions

An equipartition `P` of `s` can be refined *exactly* by an equipartition with `a` times as many
parts, as soon as `a * #P.parts ≤ #s`: equitabilise every part of `P` into `a` pieces. Since the
parts of `P` have size `#s / #P.parts` or one more, all the pieces have size `q` or `q + 1`, where
`q = #s / #P.parts / a`.

Exact refinement by equipartitions is what iterated regularity arguments need when they nest
regular partitions: Mathlib's `Finpartition.exists_equipartition_card_eq` produces an equipartition
with a prescribed number of parts but relates it to no given partition.

## Main declarations

* `Finpartition.IsEquipartition.exists_refining_equipartition_card_eq_mul`: an equipartition
  with `k` parts is refined by an equipartition with exactly `a * k` parts, provided `a ≠ 0` and
  `a * k ≤ #s`.
-/

public section

open Finset

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s : Finset α} {P : Finpartition s}

/-- An equipartition `P` of `s` is refined by an equipartition of `s` with exactly `a * #P.parts`
parts, for any `a ≠ 0` with `a * #P.parts ≤ #s`. Each part of `P` is equitabilised into `a`
pieces. -/
theorem IsEquipartition.exists_refining_equipartition_card_eq_mul (hP : P.IsEquipartition)
    {a : ℕ} (ha : a ≠ 0) (hs : a * #P.parts ≤ #s) :
    ∃ Q : Finpartition s, Q.IsEquipartition ∧ #Q.parts = a * #P.parts ∧ Q ≤ P := by
  -- Every part of `P` has size between `a * q` and `a * (q + 1)`.
  set q := #s / #P.parts / a
  have hcard (A : Finset α) (hA : A ∈ P.parts) : a * q ≤ #A ∧ #A ≤ a * (q + 1) := by
    have h₁ : a * q ≤ #s / #P.parts := by
      rw [mul_comm]
      exact Nat.div_mul_le_self _ _
    have h₂ : #s / #P.parts < a * q + a := by
      simpa [mul_add] using Nat.lt_mul_div_succ (#s / #P.parts) (Nat.pos_of_ne_zero ha)
    have h₃ := hP.average_le_card_part hA
    have h₄ := hP.card_part_le_average_add_one hA
    rw [mul_add, mul_one]
    omega
  -- So it splits into `a` pieces, `#A - a * q` of size `q + 1` and the rest of size `q`.
  have hsplit (A : Finset α) (hA : A ∈ P.parts) :
      (a - (#A - a * q)) * q + (#A - a * q) * (q + 1) = #A := by
    obtain ⟨hl, hu⟩ := hcard A hA
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hl
    obtain ⟨t, ht⟩ : ∃ t, a = r + t := Nat.exists_eq_add_of_le (by rw [mul_add] at hu; omega)
    rw [hr, Nat.add_sub_cancel_left, ht, Nat.add_sub_cancel_left]
    ring
  refine ⟨P.bind fun A hA ↦ (⊥ : Finpartition A).equitabilise (hsplit A hA),
    Set.equitableOn_iff_exists_eq_eq_add_one.2 ⟨q, fun t ht ↦ ?_⟩, ?_, bind_le _ _⟩
  · obtain ⟨A, hA, ht⟩ := mem_bind.1 ht
    exact card_eq_of_mem_parts_equitabilise ht
  · rw [card_bind, sum_const_nat (m := a) fun A _ ↦ ?_, card_attach, mul_comm]
    -- The pieces are nonempty since `1 ≤ q`.
    have hq : q ≠ 0 := by
      have hk : 0 < #P.parts := card_pos.2 ⟨A, A.2⟩
      refine (Nat.div_pos ?_ (Nat.pos_of_ne_zero ha)).ne'
      rwa [Nat.le_div_iff_mul_le hk]
    have hA := (hcard A A.2).2
    rw [mul_add, mul_one] at hA
    rw [card_parts_equitabilise _ _ hq]
    omega

end Finpartition
