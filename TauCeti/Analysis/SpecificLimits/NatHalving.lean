/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Normed.Group.Continuity
import TauCeti.Data.Nat.Log

/-!
# Accumulating half-interval errors at integer cutoffs

Successive integer halvings partition a summatory function into exact half-interval increments.
A continuous comparison function is evaluated at the real half-endpoints instead. A Lipschitz
bound pays for these endpoint mismatches, including the final change from `⌊X⌋` to `X`.
-/

public section

open Finset

namespace TauCeti

/-- Accumulate half-interval estimates for a summatory function `S` with comparison `-F`.
If the error at integer `k` is bounded by `A*k + B`, the linear costs sum to at most `2*A*X`,
and there are `J` constant costs. If `F` has Lipschitz constant `M` on `[1, ∞)`, the real
endpoints cost at most `M*(J/2 + 1)` in total. The lower endpoint is the first integer cutoff
below `K`. -/
theorem exists_norm_halving_error_le {E : Type*} [SeminormedAddCommGroup E]
    (S : ℕ → E) (F : ℝ → E) {X A B M : ℝ} {K : ℕ}
    (hX : 1 ≤ X) (hK : 2 ≤ K) (hA : 0 ≤ A)
    (hF : ∀ a b : ℝ, 1 ≤ a → a ≤ b → ‖F b - F a‖ ≤ M * (b - a))
    (hhalf : ∀ k : ℕ, K ≤ k → k ≤ ⌊X⌋₊ →
      ‖S k - S (k / 2) + (F k - F ((k : ℝ) / 2))‖ ≤ A * k + B) :
    ∃ J : ℕ, J ≤ Nat.log 2 ⌊X⌋₊ ∧ (∀ j < J, K ≤ ⌊X⌋₊ / 2 ^ j) ∧
      1 ≤ ⌊X⌋₊ / 2 ^ J ∧ ⌊X⌋₊ / 2 ^ J < K ∧
      ‖S ⌊X⌋₊ - S (⌊X⌋₊ / 2 ^ J) + (F X - F (↑(⌊X⌋₊ / 2 ^ J) : ℝ))‖ ≤
        2 * A * X + B * J + M * ((J : ℝ) / 2 + 1) := by
  obtain ⟨J, hJ, hbefore, hlast, hstop⟩ := Nat.exists_div_pow_two_lt (Nat.floor_pos.mpr hX) hK
  refine ⟨J, hJ, hbefore, hlast, hstop, ?_⟩
  let k (j : ℕ) := ⌊X⌋₊ / 2 ^ j
  have hk₀ : k 0 = ⌊X⌋₊ := by simp [k]
  have hnext (j : ℕ) : k (j + 1) = k j / 2 := by simp [k, pow_succ, Nat.div_div_eq_div_mul]
  have hM : 0 ≤ M := by simpa using (norm_nonneg _).trans (hF 1 2 le_rfl (by norm_num))
  have hlo (j : ℕ) : (2 : ℝ) * k (j + 1) ≤ k j := by
    exact_mod_cast (show 2 * k (j + 1) ≤ k j by rw [hnext]; omega)
  have hround (j : ℕ) (hj : j ∈ range J) :
      ‖F ((k j : ℝ) / 2) - F (k (j + 1))‖ ≤ M / 2 := by
    have hkj : K ≤ k j := hbefore _ (mem_range.mp hj)
    have hfloor : 1 ≤ k (j + 1) := by rw [hnext]; omega
    have hhi : (k j : ℝ) ≤ 2 * k (j + 1) + 1 := by
      exact_mod_cast (show k j ≤ 2 * k (j + 1) + 1 by rw [hnext]; omega)
    refine (hF _ _ (by exact_mod_cast hfloor) (by linarith [hlo j])).trans ?_
    simpa only [mul_one_div] using
      mul_le_mul_of_nonneg_left (by linarith : (k j : ℝ) / 2 - k (j + 1) ≤ 1 / 2) hM
  let G (j : ℕ) := S (k j) + F (k j)
  have hterm (j : ℕ) (hj : j ∈ range J) :
      ‖G j - G (j + 1)‖ ≤ 2 * A * ((k j : ℝ) - k (j + 1)) + (B + M / 2) := by
    have hle : (k j : ℝ) ≤ 2 * ((k j : ℝ) - (k (j + 1) : ℝ)) := by linarith [hlo j]
    have hv := hhalf (k j) (hbefore j (mem_range.mp hj)) (Nat.div_le_self ..)
    rw [← hnext] at hv
    calc
      _ ≤ (A * k j + B) + M / 2 := by
        dsimp only [G]
        rw [show S (k j) + F (k j) - (S (k (j + 1)) + F (k (j + 1))) =
          (S (k j) - S (k (j + 1)) + (F (k j) - F ((k j : ℝ) / 2))) +
            (F ((k j : ℝ) / 2) - F (k (j + 1))) by abel]
        exact (norm_add_le ..).trans (add_le_add hv (hround j hj))
      _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left hle hA]
  have htotal := (norm_sum_le (range J) (fun j ↦ G j - G (j + 1))).trans (sum_le_sum hterm)
  rw [sum_range_sub', sum_add_distrib, ← mul_sum, sum_range_sub', sum_const, card_range,
    nsmul_eq_mul, hk₀] at htotal
  have hfloor := Nat.floor_le (zero_le_one.trans hX)
  have hup : ‖F X - F ⌊X⌋₊‖ ≤ M :=
    (hF _ _ (by exact_mod_cast Nat.floor_pos.mpr hX) hfloor).trans
      (by simpa using mul_le_mul_of_nonneg_left (by linarith [Nat.lt_floor_add_one X] :
        X - ⌊X⌋₊ ≤ 1) hM)
  rw [show S ⌊X⌋₊ - S (⌊X⌋₊ / 2 ^ J) + (F X - F ↑(⌊X⌋₊ / 2 ^ J)) =
    (G 0 - G J) + (F X - F ⌊X⌋₊) by dsimp only [G, k]; simp only [pow_zero, Nat.div_one]; abel]
  refine (norm_add_le ..).trans ((add_le_add htotal hup).trans ?_)
  nlinarith only [mul_nonneg hA (sub_nonneg.mpr hfloor),
    mul_nonneg hA (Nat.cast_nonneg (α := ℝ) (k J))]

end TauCeti
