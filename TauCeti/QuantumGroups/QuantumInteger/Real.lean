/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.QuantumGroups.QuantumInteger.Order
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-!
# Signs of quantum integers at real loop parameters

When `sin θ ≠ 0`, the quantum integer `[n]` at `2 * cos θ` is `sin (n * θ) / sin θ`.
This determines the positive weights before the first zero at `θ = π / m`, and the first
negative weight when `π / θ` is not an integer. At parameters at least two every positive-index
quantum integer is positive. These sign results apply to the trace weights in Temperley–Lieb
algebras and the Jones–Wenzl recursion.

The trigonometric formula uses Mathlib's rescaled Chebyshev evaluation theorem
`Polynomial.Chebyshev.S_two_mul_real_cos`.

## References

* David Penneys, *Unitary Quantum Symmetries Lite*, Part I, Chapter 4, Exercise 4.3.3 and
  Lemma 4.3.8, for the quantum-integer sign criterion.
-/

public section

namespace TauCeti

open Real

/-- The sine multiplication formula for quantum integers, valid even when `sin θ = 0`. -/
@[simp]
theorem qInt_two_mul_cos_mul_sin (θ : ℝ) (n : ℕ) :
    qInt ℝ (2 * cos θ) n * sin θ = sin ((n : ℝ) * θ) := by
  simp [qInt_def]

/-- Quantum integers at a cosine parameter are ratios of sines. -/
theorem qInt_two_mul_cos {θ : ℝ} (hθ : sin θ ≠ 0) (n : ℕ) :
    qInt ℝ (2 * cos θ) n = sin ((n : ℝ) * θ) / sin θ := by
  exact (eq_div_iff hθ).2 (qInt_two_mul_cos_mul_sin θ n)

/-- Quantum integers are positive before the multiple of the angle reaches `π`. -/
theorem qInt_two_mul_cos_pos {θ : ℝ} (hθ : 0 < θ) {n : ℕ} (hn : 0 < n)
    (hnθ : (n : ℝ) * θ < π) : 0 < qInt ℝ (2 * cos θ) n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hθπ : θ < π := by nlinarith
  have hs := sin_pos_of_pos_of_lt_pi hθ hθπ
  rw [qInt_two_mul_cos hs.ne']
  exact div_pos (sin_pos_of_pos_of_lt_pi (mul_pos (by positivity) hθ) hnθ) hs

/-- At the discrete cosine parameter `2 * cos (π / m)`, the quantum integer `[m]` vanishes. -/
theorem qInt_two_mul_cos_pi_div_eq_zero {m : ℕ} (hm : 2 ≤ m) :
    qInt ℝ (2 * cos (π / m)) m = 0 := by
  have hm' : (1 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < sin (π / m) :=
    sin_pos_of_pos_of_lt_pi (by positivity) (div_lt_self pi_pos hm')
  rw [qInt_two_mul_cos hs.ne']
  simp [mul_div_cancel₀, (by positivity : (m : ℝ) ≠ 0)]

/-- The quantum integers before `[m]` are positive at `2 * cos (π / m)`. -/
theorem qInt_two_mul_cos_pi_div_pos {m n : ℕ} (hn : 0 < n) (hnm : n < m) :
    0 < qInt ℝ (2 * cos (π / m)) n := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (lt_trans hn hnm)
  apply qInt_two_mul_cos_pos (div_pos pi_pos hm) hn
  rw [← mul_div_assoc, div_lt_iff₀ hm]
  have hnm' : (n : ℝ) < m := by exact_mod_cast hnm
  nlinarith [pi_pos]

/-- For a nonintegral `π / θ`, every positive index at most its floor has positive weight. -/
theorem qInt_two_mul_cos_pos_of_le_floor {θ : ℝ} (hθ : 0 < θ)
    (hfloor : (⌊π / θ⌋₊ : ℝ) < π / θ) {n : ℕ} (hn : 0 < n)
    (hnfloor : n ≤ ⌊π / θ⌋₊) : 0 < qInt ℝ (2 * cos θ) n := by
  apply qInt_two_mul_cos_pos hθ hn
  apply (lt_div_iff₀ hθ).1
  exact lt_of_le_of_lt (by exact_mod_cast hnfloor) hfloor

/-- The index immediately after `⌊π / θ⌋` has negative weight for `0 < θ < π`.
Together with `qInt_two_mul_cos_pos_of_le_floor`, this identifies the first negative index
when `π / θ` is not an integer. -/
theorem qInt_two_mul_cos_floor_add_one_neg {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < π) :
    qInt ℝ (2 * cos θ) (⌊π / θ⌋₊ + 1) < 0 := by
  have hs := sin_pos_of_pos_of_lt_pi hθ hθπ
  have hlo : π < ((⌊π / θ⌋₊ : ℝ) + 1) * θ :=
    (div_lt_iff₀ hθ).1 (Nat.lt_floor_add_one (π / θ))
  have hhi : ((⌊π / θ⌋₊ : ℝ) + 1) * θ < 2 * π := by
    have hf := (le_div_iff₀ hθ).1 (Nat.floor_le (div_nonneg pi_pos.le hθ.le))
    nlinarith
  rw [qInt_two_mul_cos hs.ne']
  apply div_neg_of_neg_of_pos _ hs
  rw [Nat.cast_add, Nat.cast_one, ← sin_sub_two_pi]
  exact sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)

end TauCeti
