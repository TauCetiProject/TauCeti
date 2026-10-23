/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Central binomial bounds for coefficient estimates

The largest binomial coefficient in row `k`, multiplied by `√(k + 1)`, is at most
`2 ^ k`. Together with the supermultiplicativity of the middle coefficients, this
combines the coefficient-to-Mahler and Landau bounds without an extra degree factor.

## References

* Xiaorun Wu, *Diophantine geometry, week 08: arithmetic heights* (2023), Lemma 3.5.
* Lukas Pottmeyer, *Diophantine Approximation* (2022), Lemmas 3.2.8 and 3.2.9.
-/

public section

namespace TauCeti

/-- The central binomial coefficient satisfies the square-root upper bound
`C(2n,n) √(2n+1) ≤ 4^n`. -/
theorem _root_.Nat.centralBinom_mul_sqrt_le_four_pow (n : ℕ) :
    (n.centralBinom : ℝ) * Real.sqrt (2 * n + 1) ≤ 4 ^ n := by
  have hsq : ∀ n : ℕ, (n.centralBinom : ℝ) ^ 2 * (2 * n + 1) ≤ 16 ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have hrec : ((n + 1 : ℕ) : ℝ) * (Nat.centralBinom (n + 1) : ℝ) =
          2 * (2 * n + 1) * (n.centralBinom : ℝ) := by
        exact_mod_cast Nat.succ_mul_centralBinom_succ n
      have hrec_sq := congrArg (fun x : ℝ ↦ x ^ 2) hrec
      have hpos : 0 < (n + 1 : ℝ) ^ 2 := by positivity
      apply (mul_le_mul_iff_right₀ hpos).mp
      simp only [Nat.cast_add, Nat.cast_one, pow_succ] at *
      nlinarith [mul_le_mul_of_nonneg_left ih (by positivity : 0 ≤ 16 * (n + 1 : ℝ) ^ 2),
        sq_nonneg (n.centralBinom : ℝ)]
  have hsqrt : Real.sqrt (2 * n + 1) ^ 2 = (2 * n + 1 : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hpow : ((4 : ℝ) ^ n) ^ 2 = 16 ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul]
    norm_num
  rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow, hsqrt, hpow]
  exact hsq n

/-- The largest binomial coefficient in row `k`, times `√(k+1)`, is at most `2^k`. -/
theorem _root_.Nat.choose_middle_mul_sqrt_le_two_pow (k : ℕ) :
    (k.choose (k / 2) : ℝ) * Real.sqrt (k + 1) ≤ 2 ^ k := by
  obtain ⟨n, rfl | rfl⟩ : ∃ n, k = 2 * n ∨ k = 2 * n + 1 := ⟨k / 2, by omega⟩
  · convert Nat.centralBinom_mul_sqrt_le_four_pow n using 1 <;>
      norm_num [Nat.centralBinom, pow_mul]
  · have hchoose : 2 * (Nat.choose (2 * n + 1) n : ℝ) =
        (Nat.centralBinom (n + 1) : ℝ) := by
      have hrow : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      rw [Nat.centralBinom, hrow, Nat.choose_succ_succ', Nat.choose_symm_half]
      push_cast
      ring
    have hsqrt : Real.sqrt ((2 * n + 1 : ℕ) + 1) ≤ Real.sqrt (2 * (n + 1) + 1) := by
      apply Real.sqrt_le_sqrt
      push_cast
      linarith
    have h := Nat.centralBinom_mul_sqrt_le_four_pow (n + 1)
    have hdiv : (2 * n + 1) / 2 = n := by omega
    rw [hdiv]
    have hpow : (4 : ℝ) ^ (n + 1) = 2 * 2 ^ (2 * n + 1) := by
      rw [pow_succ, pow_succ, pow_mul]
      norm_num
      ring
    rw [hpow, ← hchoose] at h
    push_cast at h hsqrt ⊢
    nlinarith [mul_le_mul_of_nonneg_left hsqrt (by positivity :
      0 ≤ (Nat.choose (2 * n + 1) n : ℝ))]

/-- Middle binomial coefficients are supermultiplicative in the row index. -/
theorem _root_.Nat.choose_middle_mul_choose_middle_le (a b : ℕ) :
    a.choose (a / 2) * b.choose (b / 2) ≤ (a + b).choose ((a + b) / 2) := by
  calc
    a.choose (a / 2) * b.choose (b / 2) ≤
        (a + b).choose (a / 2 + b / 2) := by
      rw [Nat.add_choose_eq]
      have hmem : (a / 2, b / 2) ∈ Finset.antidiagonal (a / 2 + b / 2) := by simp
      exact Finset.single_le_sum (f := fun ij : ℕ × ℕ ↦ a.choose ij.1 * b.choose ij.2)
        (fun _ _ ↦ Nat.zero_le _) hmem
    _ ≤ (a + b).choose ((a + b) / 2) := Nat.choose_le_middle _ _

/-- A finite product of middle binomial coefficients is bounded by the middle
coefficient of the sum of their row indices. -/
theorem _root_.Nat.prod_choose_middle_le_choose_sum_middle {ι : Type*} (s : Finset ι) (d : ι → ℕ) :
    ∏ i ∈ s, (d i).choose (d i / 2) ≤ (∑ i ∈ s, d i).choose ((∑ i ∈ s, d i) / 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (Nat.mul_le_mul_left _ ih).trans (Nat.choose_middle_mul_choose_middle_le _ _)

end TauCeti
