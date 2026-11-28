/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Order.Partition.Equipartition
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.Ring

/-!
# Cell-size bounds for finite equipartitions

This file collects elementary upper and lower bounds on cell sizes and within-cell pair counts of a
finite equipartition `P : Finpartition s` (`Finpartition.IsEquipartition`):

* `Finpartition.IsEquipartition.sum_card_mul_sub_one_le` and
  `Finpartition.IsEquipartition.cast_sum_card_mul_sub_one_le`: the total number of ordered distinct
  pairs lying inside cells of `P` is at most `#s * (#s / #P.parts)`, hence at most
  `(#s : K) ^ 2 / #P.parts` in any linearly ordered semifield `K`.
* `Finpartition.IsEquipartition.le_card_part_of_mul_le`: if `#P.parts ≤ k` and `k * m ≤ #s`, every
  cell of `P` has size at least `m`.
* `Finpartition.IsEquipartition.le_mul_card_part_of_sup_mul_le`: if `#s` is at least `k` times the
  supremum of `⌈a / g j⌉₊` over `j ≤ k`, then `a ≤ g t * #C` for every cell `C ∈ P.parts` and every
  `t ≤ k` with `0 < g t`.
-/

public section

open Finset

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s : Finset α} {P : Finpartition s}

/-- In an equipartition `P` of `s`, the within-cell ordered distinct-pair count
`∑ A ∈ P.parts, #A * (#A - 1)` is at most `#s * (#s / #P.parts)`. -/
theorem IsEquipartition.sum_card_mul_sub_one_le (hP : P.IsEquipartition) :
    ∑ A ∈ P.parts, #A * (#A - 1) ≤ #s * (#s / #P.parts) := by
  calc ∑ A ∈ P.parts, #A * (#A - 1)
      ≤ ∑ A ∈ P.parts, #A * (#s / #P.parts) :=
        sum_le_sum fun A hA ↦
          Nat.mul_le_mul_left _ (Nat.sub_le_of_le_add (hP.card_part_le_average_add_one hA))
    _ = (∑ A ∈ P.parts, #A) * (#s / #P.parts) := (sum_mul _ _ _).symm
    _ = #s * (#s / #P.parts) := by rw [P.sum_card_parts]

/-- In a linearly ordered semifield `K`, the within-cell ordered distinct-pair count of an
equipartition `P` of `s` is at most `(#s : K) ^ 2 / #P.parts`. -/
theorem IsEquipartition.cast_sum_card_mul_sub_one_le {K : Type*} [Semifield K] [LinearOrder K]
    [IsStrictOrderedRing K] (hP : P.IsEquipartition) :
    ((∑ A ∈ P.parts, #A * (#A - 1) : ℕ) : K) ≤ (#s : K) ^ 2 / #P.parts := by
  calc ((∑ A ∈ P.parts, #A * (#A - 1) : ℕ) : K)
      ≤ (#s : K) * (#s / #P.parts : ℕ) := by exact_mod_cast hP.sum_card_mul_sub_one_le
    _ ≤ (#s : K) * ((#s : K) / #P.parts) :=
        mul_le_mul_of_nonneg_left Nat.cast_div_le (Nat.cast_nonneg _)
    _ = (#s : K) ^ 2 / #P.parts := by ring

/-- If an equipartition `P` of `s` has at most `k` parts and `k * m ≤ #s`, then every part of `P`
has cardinality at least `m`. -/
theorem IsEquipartition.le_card_part_of_mul_le (hP : P.IsEquipartition) {k m : ℕ}
    (hk : #P.parts ≤ k) (hkm : k * m ≤ #s) {C : Finset α} (hC : C ∈ P.parts) :
    m ≤ #C := by
  have hP_pos : 0 < #P.parts := card_pos.2 ⟨C, hC⟩
  have hk_pos : 0 < k := hP_pos.trans_le hk
  have hm_le : m ≤ #s / k := (Nat.le_div_iff_mul_le hk_pos).2 (by rwa [mul_comm])
  exact hm_le.trans ((Nat.div_le_div_left hk hP_pos).trans (hP.average_le_card_part hC))

/-- If `#s` is at least `k` times the supremum of `⌈a / g j⌉₊` over `j ≤ k`, then every part `C` of
an equipartition `P` of `s` with `#P.parts ≤ k` satisfies `a ≤ g t * #C` whenever `t ≤ k` and
`0 < g t`. -/
theorem IsEquipartition.le_mul_card_part_of_sup_mul_le {R : Type*} [Semifield R] [LinearOrder R]
    [IsStrictOrderedRing R] [FloorSemiring R] (hP : P.IsEquipartition) {k t : ℕ} {a : R}
    {g : ℕ → R} (hk : #P.parts ≤ k) (ht : t ≤ k) (hg : 0 < g t)
    (hks : k * ((range (k + 1)).sup fun j ↦ ⌈a / g j⌉₊) ≤ #s) {C : Finset α} (hC : C ∈ P.parts) :
    a ≤ g t * #C := by
  have hceil_le : ⌈a / g t⌉₊ ≤ (range (k + 1)).sup fun j ↦ ⌈a / g j⌉₊ :=
    le_sup (f := fun j ↦ ⌈a / g j⌉₊) (mem_range.2 (Nat.lt_succ_of_le ht))
  have hcard : ⌈a / g t⌉₊ ≤ #C := hceil_le.trans (hP.le_card_part_of_mul_le hk hks hC)
  have hdiv : a / g t ≤ #C := (Nat.le_ceil _).trans (by exact_mod_cast hcard)
  exact (div_le_iff₀' hg).1 hdiv

end Finpartition
