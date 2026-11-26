/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Stochastic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Order.BigOperators.Sum.PosPart
import TauCeti.Algebra.Ring.Invertible

/-!
# Row-stochastic matrices: transition couplings and discounted resolvents

Given two vectors `p q : ι → R` on a finite index type with equal total sum and `q` nonnegative
over a linearly ordered field, `Matrix.exists_mem_rowStochastic_vecMul_eq` constructs a
row-stochastic matrix `M ∈ Matrix.rowStochastic R ι` satisfying `p ᵥ* M = q` whose off-diagonal
transported mass from each index `i` equals `max (p i - q i) 0`.

For probability distributions on `ι`, this yields an optimal Markov transition kernel mapping `p`
to `q` whose total probability of changing state equals the total-variation distance
`∑ i, max (p i - q i) 0 = (1 / 2) ∑ i, |p i - q i|`.

For a row-stochastic matrix `P` and a discount `0 ≤ c < 1`, the matrix `1 - c • P` is
invertible, and its inverse `Ring.inverse (1 - c • P)`, the discounted resolvent
`∑ₙ cⁿ Pⁿ`, has nonnegative entries and row sums `(1 - c)⁻¹`. These facts are proved by the
discrete maximum principle `Matrix.nonneg_of_eq_add_smul_mulVec`, without norms or series: a
solution of `x = b + c • P *ᵥ x` with `b ≥ 0` is nonnegative, because at a minimal coordinate
`x i ≥ c x i`.

## Main results

* `Matrix.exists_mem_rowStochastic_vecMul_eq`: existence of a row-stochastic transition matrix
  mapping `p` to `q` with minimal off-diagonal mass `p i * (1 - M i i) = max (p i - q i) 0`.
* `Matrix.isUnit_one_sub_smul_of_mem_rowStochastic`: `1 - c • P` is a unit for `0 ≤ c < 1`.
* `Matrix.ringInverse_one_sub_smul_nonneg`: the entries of `Ring.inverse (1 - c • P)` are
  nonnegative.
* `Matrix.ringInverse_one_sub_smul_mulVec_one`: the row sums of `Ring.inverse (1 - c • P)` are
  `(1 - c)⁻¹`.
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

section Resolvent

variable {R n : Type*} [Fintype n] [DecidableEq n] [Field R] [LinearOrder R]
  [IsStrictOrderedRing R] {P : Matrix n n R} {c : R}

/-- **Discrete maximum principle.** For a row-stochastic matrix `P` and `0 ≤ c < 1`, a solution
of `x = b + c • P *ᵥ x` with nonnegative `b` is nonnegative. -/
theorem nonneg_of_eq_add_smul_mulVec (hP : P ∈ rowStochastic R n) (hc₀ : 0 ≤ c) (hc₁ : c < 1)
    {b x : n → R} (hb : 0 ≤ b) (hx : x = b + c • P *ᵥ x) : 0 ≤ x := by
  cases isEmpty_or_nonempty n
  · exact fun i ↦ isEmptyElim i
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  have hmin (j : n) : x i₀ ≤ x j := hi₀ j (Finset.mem_univ j)
  -- At a minimal coordinate, the average `(P *ᵥ x) i₀` is at least `x i₀`.
  have hP_ge : x i₀ ≤ (P *ᵥ x) i₀ := by
    calc x i₀ = ∑ j, P i₀ j * x i₀ := by
          rw [← Finset.sum_mul, sum_row_of_mem_rowStochastic hP, one_mul]
      _ ≤ ∑ j, P i₀ j * x j :=
          Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (hmin j) (hP.1 _ _)
  have hxi₀ : x i₀ = b i₀ + c * (P *ᵥ x) i₀ := by
    simpa using congrFun hx i₀
  have h₀ : 0 ≤ x i₀ := by
    have hb₀ : 0 ≤ b i₀ := hb i₀
    have h : 0 ≤ (1 - c) * x i₀ := by
      linarith [mul_le_mul_of_nonneg_left hP_ge hc₀]
    exact (mul_nonneg_iff_of_pos_left (sub_pos.2 hc₁)).1 h
  exact fun i ↦ h₀.trans (hmin i)

/-- For a row-stochastic matrix `P` and `0 ≤ c < 1`, the matrix `1 - c • P` is a unit. -/
theorem isUnit_one_sub_smul_of_mem_rowStochastic (hP : P ∈ rowStochastic R n) (hc₀ : 0 ≤ c)
    (hc₁ : c < 1) : IsUnit (1 - c • P) := by
  have key (z : n → R) (hz : (1 - c • P) *ᵥ z = 0) : 0 ≤ z :=
    nonneg_of_eq_add_smul_mulVec hP hc₀ hc₁ le_rfl <| by
      rw [sub_mulVec, one_mulVec, smul_mulVec, sub_eq_zero] at hz
      rw [zero_add, ← hz]
  rw [← mulVec_injective_iff_isUnit]
  intro x y hxy
  have h₁ := key (x - y) (by rw [mulVec_sub, hxy, sub_self])
  have h₂ := key (y - x) (by rw [mulVec_sub, hxy, sub_self])
  exact le_antisymm (sub_nonneg.1 h₂) (sub_nonneg.1 h₁)

/-- For a row-stochastic matrix `P` and `0 ≤ c < 1`, the resolvent `Ring.inverse (1 - c • P)`
maps nonnegative vectors to nonnegative vectors. -/
theorem ringInverse_one_sub_smul_mulVec_nonneg (hP : P ∈ rowStochastic R n) (hc₀ : 0 ≤ c)
    (hc₁ : c < 1) {b : n → R} (hb : 0 ≤ b) : 0 ≤ Ring.inverse (1 - c • P) *ᵥ b := by
  refine nonneg_of_eq_add_smul_mulVec hP hc₀ hc₁ hb ?_
  conv_lhs => rw [Ring.inverse_one_sub_eq (isUnit_one_sub_smul_of_mem_rowStochastic hP hc₀ hc₁)]
  rw [add_mulVec, one_mulVec, smul_mul_assoc, smul_mulVec, mulVec_mulVec]

/-- For a row-stochastic matrix `P` and `0 ≤ c < 1`, the entries of the resolvent
`Ring.inverse (1 - c • P)` are nonnegative. -/
theorem ringInverse_one_sub_smul_nonneg (hP : P ∈ rowStochastic R n) (hc₀ : 0 ≤ c)
    (hc₁ : c < 1) (i j : n) : 0 ≤ Ring.inverse (1 - c • P) i j := by
  have h := ringInverse_one_sub_smul_mulVec_nonneg hP hc₀ hc₁
    (b := Pi.single j 1) (Pi.single_nonneg.2 zero_le_one) i
  rwa [mulVec_single_one] at h

/-- For a row-stochastic matrix `P` and `0 ≤ c < 1`, the entries of `P * Ring.inverse (1 - c • P)`
are nonnegative. -/
theorem mul_ringInverse_one_sub_smul_nonneg (hP : P ∈ rowStochastic R n) (hc₀ : 0 ≤ c)
    (hc₁ : c < 1) (i j : n) : 0 ≤ (P * Ring.inverse (1 - c • P)) i j := by
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg fun k _ ↦
    mul_nonneg (hP.1 i k) (ringInverse_one_sub_smul_nonneg hP hc₀ hc₁ k j)

/-- For a row-stochastic matrix `P` and `0 ≤ c < 1`, the resolvent `Ring.inverse (1 - c • P)`
has row sums `(1 - c)⁻¹`. -/
theorem ringInverse_one_sub_smul_mulVec_one (hP : P ∈ rowStochastic R n) (hc₀ : 0 ≤ c)
    (hc₁ : c < 1) : Ring.inverse (1 - c • P) *ᵥ 1 = (1 - c)⁻¹ • 1 := by
  have hu := isUnit_one_sub_smul_of_mem_rowStochastic hP hc₀ hc₁
  have h : (1 - c • P) *ᵥ ((1 - c)⁻¹ • 1) = 1 := by
    rw [mulVec_smul, sub_mulVec, one_mulVec, smul_mulVec, one_vecMul_of_mem_rowStochastic hP]
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (sub_ne_zero.2 hc₁.ne')
  calc Ring.inverse (1 - c • P) *ᵥ 1
      = Ring.inverse (1 - c • P) *ᵥ ((1 - c • P) *ᵥ ((1 - c)⁻¹ • 1)) := by rw [h]
    _ = (1 - c)⁻¹ • 1 := by rw [mulVec_mulVec, Ring.inverse_mul_cancel _ hu, one_mulVec]

end Resolvent

end Matrix
