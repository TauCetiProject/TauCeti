/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import TauCeti.Order.Partition.Finpartition

/-!
# Equitable exact refinements of equipartitions

An equipartition `P` of `s` can be refined *exactly* by an equipartition with `a` times as many
parts, as soon as `a * #P.parts ≤ #s`: equitabilise every part of `P` into `a` pieces. Since the
parts of `P` have size `#s / #P.parts` or one more, all the pieces have size `q` or `q + 1`, where
`q = #s / #P.parts / a`. More generally, given a refinement `R ≤ P`, equitabilising its
restrictions inside the parts of `P` preserves exact refinement of `P` and moves at most
`#R.parts * q` points relative to `R`.

Exact refinement by equipartitions is what iterated regularity arguments need when they nest
regular partitions: Mathlib's `Finpartition.exists_equipartition_card_eq` produces an equipartition
with a prescribed number of parts but relates it to no given partition.

Equitabilising an arbitrary partition `P` does not refine it, but it moves few points: at most
`m` points of each part of `P` lie in a part of `P.equitabilise h` that is not contained in it.
This controls how much a quantity defined part by part, such as an energy, can change.

## Main declarations

* `Finpartition.IsEquipartition.exists_refining_equipartition_card_eq_mul`: an equipartition
  with `k` parts is refined by an equipartition with exactly `a * k` parts, provided `a ≠ 0` and
  `a * k ≤ #s`, with a moved-point bound relative to any refinement of `P`.
* `Finpartition.card_filter_not_part_equitabilise_subset_part_le`: at most `#P.parts * m` points
  of `s` have a part in `P.equitabilise h` not contained in their part in `P`.
* `Finpartition.exists_card_parts_equitabilise_eq`: `P.equitabilise` can produce any number
  `n ≤ #s` of parts.
* `Finpartition.exists_equipartition_card_eq_card_filter_not_part_subset_le`: every partition is
  close, in this sense, to an equipartition with any number `n ≤ #s` of parts.
-/

public section

open Finset

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s : Finset α} {P : Finpartition s}

variable (P) in
/-- **Equitabilising moves few points.** At most `#P.parts * m` points of `s` lie in a part of
`P.equitabilise h` that is not contained in their part of `P`, where the parts of
`P.equitabilise h` have size `m` or `m + 1`. -/
theorem card_filter_not_part_equitabilise_subset_part_le {a b m : ℕ}
    (h : a * m + b * (m + 1) = #s) :
    #{x ∈ s | ¬(P.equitabilise h).part x ⊆ P.part x} ≤ #P.parts * m := by
  set Q := P.equitabilise h
  -- Such a point is one of the at most `m` points of its part of `P` outside the parts of `Q`
  -- contained in that part.
  calc #{x ∈ s | ¬Q.part x ⊆ P.part x}
      ≤ #(P.parts.biUnion fun t ↦ t \ {u ∈ Q.parts | u ⊆ t}.biUnion id) := by
        refine card_le_card fun x hx ↦ ?_
        obtain ⟨hxs, hx⟩ := mem_filter.1 hx
        refine mem_biUnion.2 ⟨P.part x, P.part_mem.2 hxs, mem_sdiff.2 ⟨P.mem_part hxs, ?_⟩⟩
        simp only [mem_biUnion, mem_filter, id]
        rintro ⟨u, ⟨hu, hut⟩, hxu⟩
        exact hx (Q.part_eq_of_mem hu hxu ▸ hut)
    _ ≤ ∑ t ∈ P.parts, #(t \ {u ∈ Q.parts | u ⊆ t}.biUnion id) := card_biUnion_le
    _ ≤ ∑ _t ∈ P.parts, m := sum_le_sum fun t ht ↦ card_parts_equitabilise_subset_le P h ht
    _ = #P.parts * m := sum_const_nat fun _ _ ↦ rfl

/-- Rebalance a refinement `R` of an equipartition `P` by equitabilising inside each part of
`P`. The result still refines `P` exactly, has `a * #P.parts` parts, and disagrees with `R`
through at most `#R.parts * (#s / #P.parts / a)` points, in the sense that its part through any
other point is contained in the corresponding part of `R`. -/
theorem IsEquipartition.exists_refining_equipartition_card_eq_mul (hP : P.IsEquipartition)
    (R : Finpartition s) (hRP : R ≤ P) {a : ℕ} (ha : a ≠ 0) (hs : a * #P.parts ≤ #s) :
    ∃ Q : Finpartition s, Q.IsEquipartition ∧ #Q.parts = a * #P.parts ∧ Q ≤ P ∧
      #{x ∈ s | ¬Q.part x ⊆ R.part x} ≤ #R.parts * (#s / #P.parts / a) := by
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
  let E (A : Finset α) (hA : A ∈ P.parts) :=
    (R.restrict (P.le hA)).equitabilise (hsplit A hA)
  let Q := P.bind E
  refine ⟨Q, Set.equitableOn_iff_exists_eq_eq_add_one.2 ⟨q, fun t ht ↦ ?_⟩,
    ?_, bind_le _ _, ?_⟩
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
  · -- Sum the local exceptional sets; their restrictions reconstruct `R`.
    have hsub : {x ∈ s | ¬Q.part x ⊆ R.part x} ⊆
        P.parts.biUnion fun A ↦ {x ∈ A | ¬Q.part x ⊆ R.part x} := by
      intro x hx
      exact mem_biUnion.2 ⟨P.part x, P.part_mem.2 (mem_filter.1 hx).1,
        mem_filter.2 ⟨P.mem_part (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩⟩
    calc #{x ∈ s | ¬Q.part x ⊆ R.part x}
        ≤ ∑ A ∈ P.parts, #{x ∈ A | ¬Q.part x ⊆ R.part x} :=
          (card_le_card hsub).trans card_biUnion_le
      _ ≤ ∑ A ∈ P.parts.attach, #(R.restrict (P.le A.2)).parts * q := by
        rw [← sum_attach P.parts (fun A ↦ #{x ∈ A | ¬Q.part x ⊆ R.part x})]
        exact sum_le_sum fun A _ ↦ by
          have hlocal := card_filter_not_part_equitabilise_subset_part_le
            (R.restrict (P.le A.2)) (hsplit A A.2)
          have heq : {x ∈ A.1 | ¬Q.part x ⊆ R.part x} =
              {x ∈ A.1 | ¬(E A A.2).part x ⊆ (R.restrict (P.le A.2)).part x} := by
            apply filter_congr
            intro x hx
            simp only [Q, part_bind A.2 hx, part_restrict _ _ hx,
              inter_eq_left.2 ((part_mono hRP x).trans
                (le_of_eq (P.part_eq_of_mem A.2 hx)))]
          rw [heq]
          exact hlocal
      _ = #R.parts * q := by
        rw [← sum_mul, ← card_bind (fun A hA ↦ R.restrict (P.le hA)), bind_restrict hRP]

variable (P) in
/-- For `0 < n ≤ #s`, some instance of `P.equitabilise` has exactly `n` parts, of sizes `#s / n`
and `#s / n + 1`. -/
theorem exists_card_parts_equitabilise_eq {n : ℕ} (hn : n ≠ 0) (hns : n ≤ #s) :
    ∃ (a b : ℕ) (h : a * (#s / n) + b * (#s / n + 1) = #s), #(P.equitabilise h).parts = n := by
  have hsum : (n - #s % n) * (#s / n) + #s % n * (#s / n + 1) = #s := by
    rw [Nat.sub_mul, mul_add, ← add_assoc,
      tsub_add_cancel_of_le (Nat.mul_le_mul_right _ (Nat.mod_lt _ hn.bot_lt).le), mul_one,
      add_comm, Nat.mod_add_div]
  refine ⟨_, _, hsum, ?_⟩
  rw [card_parts_equitabilise _ _ (Nat.div_pos hns hn.bot_lt).ne',
    tsub_add_cancel_of_le (Nat.mod_lt _ hn.bot_lt).le]

variable (P) in
/-- Every partition `P` of `s` is close to an equipartition of `s` into any number `n` of parts
with `0 < n ≤ #s`: at most `#P.parts * (#s / n)` points of `s` lie in a part of the equipartition
not contained in their part of `P`. -/
theorem exists_equipartition_card_eq_card_filter_not_part_subset_le {n : ℕ} (hn : n ≠ 0)
    (hns : n ≤ #s) :
    ∃ Q : Finpartition s, Q.IsEquipartition ∧ #Q.parts = n ∧
      #{x ∈ s | ¬Q.part x ⊆ P.part x} ≤ #P.parts * (#s / n) := by
  obtain ⟨a, b, h, hcard⟩ := P.exists_card_parts_equitabilise_eq hn hns
  exact ⟨P.equitabilise h, equitabilise_isEquipartition, hcard,
    card_filter_not_part_equitabilise_subset_part_le P h⟩

end Finpartition
