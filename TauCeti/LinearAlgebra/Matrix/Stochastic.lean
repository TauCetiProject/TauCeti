/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Stochastic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Order.BigOperators.Sum.PosPart

/-!
# Row-stochastic transition couplings

Given two vectors `p q : ι → R` on a finite index type with equal total sum and `q` nonnegative
over a linearly ordered field, `Matrix.exists_mem_rowStochastic_vecMul_eq` constructs a
row-stochastic matrix `M ∈ Matrix.rowStochastic R ι` satisfying `p ᵥ* M = q` whose off-diagonal
transported mass from each index `i` equals `max (p i - q i) 0`.

For probability distributions on `ι`, this yields an optimal Markov transition kernel mapping `p`
to `q` whose total probability of changing state equals the total-variation distance
`∑ i, max (p i - q i) 0 = (1 / 2) ∑ i, |p i - q i|`.

## Main results

* `Matrix.exists_mem_rowStochastic_vecMul_eq`: existence of a row-stochastic transition matrix
  mapping `p` to `q` with minimal off-diagonal mass `p i * (1 - M i i) = max (p i - q i) 0`.
-/

public section

namespace Matrix

open Finset

/-- Given vectors `p q : ι → R` with equal total sum and `q` nonnegative over a linearly ordered
field, there exists a row-stochastic matrix `M` satisfying `p ᵥ* M = q` such that each index `i`
transports mass `p i * (1 - M i i) = max (p i - q i) 0` off the diagonal. -/
theorem exists_mem_rowStochastic_vecMul_eq {R ι : Type*} [Fintype ι] [DecidableEq ι]
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] {p q : ι → R}
    (hsum : ∑ i, p i = ∑ i, q i) (hq : ∀ i, 0 ≤ q i) :
    ∃ M ∈ rowStochastic R ι,
      p ᵥ* M = q ∧ ∀ i, p i * (1 - M i i) = max (p i - q i) 0 := by
  let pos : ι → R := fun i ↦ max (q i - p i) 0
  let neg : ι → R := fun i ↦ max (p i - q i) 0
  set Δ : R := ∑ i, pos i with hΔ_def
  have hpos_nonneg (i : ι) : 0 ≤ pos i := le_max_right _ _
  have hneg_nonneg (i : ι) : 0 ≤ neg i := le_max_right _ _
  have hbal : ∑ i, (q i - p i) = 0 := by
    rw [sum_sub_distrib, hsum, sub_self]
  have hΔ_neg : ∑ i, neg i = Δ := by
    have hneg_eq : ∀ i, neg i = max (-(q i - p i)) 0 := fun i ↦ by
      simp only [neg, neg_sub]
    simp_rw [hneg_eq]
    exact sum_max_neg_eq_sum_max univ (fun i ↦ q i - p i) hbal
  let M : Matrix ι ι R := fun i j ↦
    if q i < p i then
      (if j = i then q i / p i else 0) + (p i - q i) / p i * (pos j / Δ)
    else
      if j = i then 1 else 0
  have hΔ_pos_of_lt {i : ι} (hlt : q i < p i) : 0 < Δ := by
    have hni : 0 < neg i := lt_of_lt_of_le (sub_pos.2 hlt) (le_max_left _ _)
    have hle : neg i ≤ ∑ j, neg j := single_le_sum (fun j _ ↦ hneg_nonneg j) (mem_univ i)
    linarith
  have hM_mem : M ∈ rowStochastic R ι := by
    rw [mem_rowStochastic_iff_sum]
    refine ⟨fun i j ↦ ?_, fun i ↦ ?_⟩
    · dsimp only [M]
      by_cases hlt : q i < p i
      · have : 0 < p i := lt_of_le_of_lt (hq i) hlt
        have : 0 < Δ := hΔ_pos_of_lt hlt
        have : 0 ≤ q i := hq i
        have : 0 ≤ p i - q i := sub_nonneg.2 hlt.le
        have : 0 ≤ pos j := hpos_nonneg j
        simp only [hlt, ↓reduceIte]
        split_ifs <;> positivity
      · simp only [hlt, ↓reduceIte]
        split_ifs
        · exact zero_le_one
        · exact le_rfl
    · dsimp only [M]
      split_ifs with hlt
      · have hp : p i ≠ 0 := (lt_of_le_of_lt (hq i) hlt).ne'
        have hΔne : Δ ≠ 0 := (hΔ_pos_of_lt hlt).ne'
        rw [sum_add_distrib, sum_ite_eq' univ i, ← mul_sum, ← sum_div, ← hΔ_def, div_self hΔne,
          mul_one]
        simp only [mem_univ, ↓reduceIte]
        field_simp [hp]
        ring
      · simp
  have hvecMul : p ᵥ* M = q := by
    ext j
    simp only [vecMul, dotProduct]
    have hterm (i : ι) :
        p i * M i j = (if j = i then p i - neg i else 0) + neg i * (pos j / Δ) := by
      dsimp only [M]
      by_cases hlt : q i < p i
      · have hp : p i ≠ 0 := (lt_of_le_of_lt (hq i) hlt).ne'
        have hneg : neg i = p i - q i := max_eq_left (sub_nonneg.2 hlt.le)
        simp only [hlt, ↓reduceIte, hneg]
        split_ifs <;> field_simp [hp] <;> ring
      · have hneg : neg i = 0 := max_eq_right (sub_nonpos.2 (not_lt.1 hlt))
        simp [hlt, hneg]
    simp_rw [hterm]
    rw [sum_add_distrib, sum_ite_eq univ j, ← sum_mul, hΔ_neg]
    simp only [mem_univ, ↓reduceIte]
    have hdiff : pos j - neg j = q j - p j := by
      dsimp only [pos, neg]
      rw [← neg_sub (q j) (p j), max_zero_sub_max_neg_zero_eq_self]
    by_cases hΔ0 : Δ = 0
    · have : pos j = 0 := le_antisymm
        ((single_le_sum (fun i _ ↦ hpos_nonneg i) (mem_univ j)).trans (by rw [← hΔ_def, hΔ0]))
        (hpos_nonneg j)
      have : neg j = 0 := le_antisymm
        ((single_le_sum (fun i _ ↦ hneg_nonneg i) (mem_univ j)).trans (by rw [hΔ_neg, hΔ0]))
        (hneg_nonneg j)
      rw [hΔ0, zero_mul, add_zero]
      linarith
    · rw [mul_div_cancel₀ _ hΔ0]
      linarith
  have hdiag (i : ι) : p i * (1 - M i i) = max (p i - q i) 0 := by
    dsimp only [M]
    by_cases hlt : q i < p i
    · have hp : p i ≠ 0 := (lt_of_le_of_lt (hq i) hlt).ne'
      have hposi : pos i = 0 := max_eq_right (sub_nonpos.2 hlt.le)
      simp only [hlt, ↓reduceIte, hposi, zero_div, mul_zero, add_zero,
        max_eq_left (sub_nonneg.2 hlt.le)]
      field_simp [hp]
    · simp only [hlt, ↓reduceIte, sub_self, mul_zero,
        max_eq_right (sub_nonpos.2 (not_lt.1 hlt))]
  exact ⟨M, hM_mem, hvecMul, hdiag⟩

end Matrix
