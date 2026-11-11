/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Analysis.Real.Sqrt
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

namespace Nat

/-- The central binomial coefficient satisfies the square-root upper bound
`C(2n,n) √(2n+1) ≤ 4^n`. -/
theorem centralBinom_mul_sqrt_le_four_pow (n : ℕ) :
    (n.centralBinom : ℝ) * √(2 * n + 1) ≤ 4 ^ n := by
  have hsq : (n.centralBinom : ℝ) ^ 2 * (2 * n + 1) ≤ 16 ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      have hrec : (n + 1 : ℝ) * (n + 1).centralBinom = 2 * (2 * n + 1) * n.centralBinom := by
        exact_mod_cast succ_mul_centralBinom_succ n
      refine le_of_mul_le_mul_left ?_ (by positivity : 0 < (n + 1 : ℝ) ^ 2)
      push_cast
      rw [_root_.pow_succ 16]
      nlinarith [mul_le_mul_of_nonneg_left ih (by positivity : 0 ≤ 16 * (n + 1 : ℝ) ^ 2),
        sq_nonneg (n.centralBinom : ℝ), congrArg (· ^ 2) hrec]
  rw [← sq_le_sq₀ (by positivity) (by positivity), mul_pow, Real.sq_sqrt (by positivity),
    pow_right_comm]
  norm_num [hsq]

/-- The largest binomial coefficient in row `k`, times `√(k+1)`, is at most `2^k`. -/
theorem choose_middle_mul_sqrt_le_two_pow (k : ℕ) :
    (k.choose (k / 2) : ℝ) * √(k + 1) ≤ 2 ^ k := by
  obtain ⟨n, rfl | rfl⟩ := k.even_or_odd'
  · convert centralBinom_mul_sqrt_le_four_pow n using 1 <;> norm_num [centralBinom, pow_mul]
  · have hchoose : (centralBinom (n + 1) : ℝ) = 2 * (2 * n + 1).choose n := by
      rw [centralBinom, mul_add_one, choose_succ_succ', choose_symm_half]
      push_cast
      ring
    have hsqrt : √((2 * n + 1 : ℝ) + 1) ≤ √(2 * (n + 1) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have hdiv : (2 * n + 1) / 2 = n := by omega
    have h := centralBinom_mul_sqrt_le_four_pow (n + 1)
    rw [hchoose, _root_.pow_succ', mul_assoc] at h
    rw [hdiv, _root_.pow_succ, _root_.pow_mul]
    norm_num at h ⊢
    nlinarith [mul_le_mul_of_nonneg_left hsqrt (cast_nonneg ((2 * n + 1).choose n))]

/-- Middle binomial coefficients are supermultiplicative in the row index. -/
theorem choose_middle_mul_choose_middle_le (a b : ℕ) :
    a.choose (a / 2) * b.choose (b / 2) ≤ (a + b).choose ((a + b) / 2) :=
  calc a.choose (a / 2) * b.choose (b / 2)
    _ ≤ (a + b).choose (a / 2 + b / 2) := by
      rw [add_choose_eq]
      exact Finset.single_le_sum_of_canonicallyOrdered
        (f := fun ij : ℕ × ℕ ↦ a.choose ij.1 * b.choose ij.2) (i := (a / 2, b / 2)) (by simp)
    _ ≤ (a + b).choose ((a + b) / 2) := choose_le_middle _ _

/-- A finite product of middle binomial coefficients is bounded by the middle
coefficient of the sum of their row indices. -/
theorem prod_choose_middle_le_choose_sum_middle {ι : Type*} (s : Finset ι) (d : ι → ℕ) :
    ∏ i ∈ s, (d i).choose (d i / 2) ≤ (∑ i ∈ s, d i).choose ((∑ i ∈ s, d i) / 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi, Finset.sum_insert hi]
    exact (mul_le_mul_left _ ih).trans (choose_middle_mul_choose_middle_le _ _)

end Nat
