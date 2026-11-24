/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
public import TauCeti.NumberTheory.Height.ScalarSum

/-!
# The explicit constants of the perturbed unit equation

Evertse, Schlickewei and Schmidt bound the number of proper subspaces containing the solutions
`y = x z` of `y₁ + ⋯ + yₙ = 1`, where `x` lies in a group of rank `r` and the perturbation `z`
satisfies `h_aff(z) ≤ n⁻¹ exp(-(5n)^(3n)) (1 + h_aff(x))`. Their proof splits the solutions at
`h_aff(x) = 4 n log n`, and writes `q₀ = exp((4n)^(3n))` for the constant of the small-height
hyperplane theorem. This file proves the explicit numerical steps of that argument.

* `TauCeti.scalarSumHeight_lt_of_absoluteLogHeightAff_le`: in the small-height regime
  `h_aff(x) ≤ 4 n log n`, the perturbation has scalar-sum height `h_s(z) < 1 / (2 q₀)`.
* `TauCeti.scalarSumHeight_mul_lt_of_absoluteLogHeightAff_le`: hence if `w = x b⁻¹` has
  `h_s(w) < 1 / (2 q₀)` for a packing centre `b`, then `y b⁻¹ = w z` has `h_s(w z) < 1 / q₀`,
  which is the hypothesis of the small-height hyperplane theorem for `∑ bᵢ (yᵢ / bᵢ) = 1`.
* `TauCeti.two_pow_mul_pow_add_two_pow_add_exp_mul_pow_lt_exp`: for `n ≥ 2`, the large-solution
  bound `2^(2(n+9)²) (8n² + 2n)^(n+4+r)`, the `2ⁿ` subsum hyperplanes of the degenerate solutions
  and the small-solution bound `q₀ (16 n³ q₀)^r` add up to less than `exp((5n)^(3n) (r + 1))`.

The real inequality behind the first item, `TauCeti.exp_neg_mul_one_add_mul_log_lt_inv`, is where
the exponent `5n` of the perturbation budget is needed: with `4n` in its place the left side
exceeds `1 / q₀` as soon as `n ≥ 2`.

## References

* J.-H. Evertse, H. P. Schlickewei and W. M. Schmidt, *Linear equations in variables
  which lie in a multiplicative group*, Annals of Mathematics 155 (2002), §§10–11,
  Corollary 10.2, Lemma 11.2, Corollary 11.3 and (11.19).
-/

public section

open Real

namespace TauCeti

/-- `(5n)^(3n) = (5/4)^(3n) (4n)^(3n)`. -/
private lemma five_mul_pow_eq (n : ℕ) :
    (5 * n : ℝ) ^ (3 * n) = (5 / 4 : ℝ) ^ (3 * n) * (4 * n : ℝ) ^ (3 * n) := by
  rw [← mul_pow]
  ring_nf

/-- For `1 ≤ n` and `k ≤ n`, `(5n)^(3n) - (4n)^(3n) ≥ ((5/4)^(3k) - 1) (4n)^(3k)`. -/
private lemma sub_one_mul_pow_le_five_mul_pow_sub {k n : ℕ} (hn : 1 ≤ n) (hk : k ≤ n) :
    ((5 / 4 : ℝ) ^ (3 * k) - 1) * (4 * n : ℝ) ^ (3 * k) ≤
      (5 * n : ℝ) ^ (3 * n) - (4 * n : ℝ) ^ (3 * n) := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [five_mul_pow_eq, ← sub_one_mul]
  exact mul_le_mul
    (sub_le_sub_right (pow_le_pow_right₀ (by norm_num) (by omega)) 1)
    (pow_le_pow_right₀ (by linarith) (by omega)) (by positivity)
    (sub_nonneg.2 (one_le_pow₀ (by norm_num)))

/-- For `n ≥ 2`, `(5n)^(3n) ≥ (4n)^(3n) + 4096 n⁶`. -/
private lemma four_mul_pow_add_le_five_mul_pow {n : ℕ} (hn : 2 ≤ n) :
    (4 * n : ℝ) ^ (3 * n) + 4096 * (n : ℝ) ^ 6 ≤ (5 * n : ℝ) ^ (3 * n) := by
  have h := sub_one_mul_pow_le_five_mul_pow_sub (k := 2) (by omega) hn
  -- Evaluate the constant: `((5/4)^6 - 1) 4^6 = 5^6 - 4^6 = 11529`.
  have hc : ((5 / 4 : ℝ) ^ (3 * 2) - 1) * (4 * n : ℝ) ^ (3 * 2) = 11529 * (n : ℝ) ^ 6 := by ring
  rw [hc] at h
  nlinarith [pow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) 6]

/-- For `n ≥ 1`, the perturbation budget `exp(-(5n)^(3n)) (1 + 4 n log n)` is less than
`1 / (2 q₀)` with `q₀ = exp((4n)^(3n))`. It fails for `n = 0`, where the left side is `e⁻¹`. -/
theorem exp_neg_mul_one_add_mul_log_lt_inv {n : ℕ} (hn : 1 ≤ n) :
    exp (-((5 * n : ℝ) ^ (3 * n))) * (1 + 4 * n * log n) <
      (2 * exp ((4 * n : ℝ) ^ (3 * n)))⁻¹ := by
  set A := (5 * n : ℝ) ^ (3 * n)
  set B := (4 * n : ℝ) ^ (3 * n)
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : n * log n ≤ n * (n - 1) :=
    mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos (by linarith)) (by linarith)
  have hAB : 61 * (n : ℝ) ^ 3 ≤ A - B := by
    have h := sub_one_mul_pow_le_five_mul_pow_sub (k := 1) hn hn
    -- Evaluate the constant: `((5/4)^3 - 1) 4^3 = 5^3 - 4^3 = 61`.
    have hc : ((5 / 4 : ℝ) ^ (3 * 1) - 1) * (4 * n : ℝ) ^ (3 * 1) = 61 * (n : ℝ) ^ 3 := by ring
    rwa [hc] at h
  have hkey : 2 * (1 + 4 * n * log n) < exp (A - B) := by
    have hpoly : 2 * (1 + 4 * n * log n) < A - B := by
      obtain ⟨t, ht, ht'⟩ : ∃ t : ℝ, 0 ≤ t ∧ (n : ℝ) = 1 + t := ⟨n - 1, by linarith, by ring⟩
      rw [ht'] at hlog hAB ⊢
      nlinarith [pow_nonneg ht 2, pow_nonneg ht 3]
    linarith [add_one_le_exp (A - B)]
  have hinv : (2 * exp B)⁻¹ = exp (A - B) * exp (-A) / 2 := by
    rw [← exp_add, mul_inv, ← exp_neg]
    ring_nf
  rw [hinv, lt_div_iff₀ two_pos]
  have hA : 0 < exp (-A) := exp_pos _
  nlinarith

variable {F : Type*} [Field F] [CharZero F]

/-- In the small-height regime `h_aff(x) ≤ 4 n log n`, a perturbation `z` within the budget
`h_aff(z) ≤ n⁻¹ exp(-(5n)^(3n)) (1 + h_aff(x))` has scalar-sum height less than `1 / (2 q₀)`,
where `q₀ = exp((4n)^(3n))`. -/
theorem scalarSumHeight_lt_of_absoluteLogHeightAff_le {n : ℕ} {x z : Fin n → F}
    (hz : ∀ i, IsAlgebraic ℚ (z i)) (hx : absoluteLogHeightAff x ≤ 4 * n * log n)
    (hzx : absoluteLogHeightAff z ≤
      (n : ℝ)⁻¹ * exp (-((5 * n : ℝ) ^ (3 * n))) * (1 + absoluteLogHeightAff x)) :
    scalarSumHeight z < (2 * exp ((4 * n : ℝ) ^ (3 * n)))⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [scalarSumHeight_def, Finset.univ_eq_empty, Finset.sum_empty]
    positivity
  have hN : (n : ℝ) ≠ 0 := by positivity
  calc scalarSumHeight z ≤ n * absoluteLogHeightAff z :=
        scalarSumHeight_le_mul_absoluteLogHeightAff z hz
    _ ≤ n * ((n : ℝ)⁻¹ * exp (-((5 * n : ℝ) ^ (3 * n))) * (1 + absoluteLogHeightAff x)) :=
        mul_le_mul_of_nonneg_left hzx (Nat.cast_nonneg n)
    _ = exp (-((5 * n : ℝ) ^ (3 * n))) * (1 + absoluteLogHeightAff x) := by
        field_simp
    _ ≤ exp (-((5 * n : ℝ) ^ (3 * n))) * (1 + 4 * n * log n) := by
        gcongr
    _ < (2 * exp ((4 * n : ℝ) ^ (3 * n)))⁻¹ := exp_neg_mul_one_add_mul_log_lt_inv hn

/-- In the small-height regime `h_aff(x) ≤ 4 n log n`, if `w` has scalar-sum height less than
`1 / (2 q₀)`, with `q₀ = exp((4n)^(3n))`, and `z` is within the perturbation budget
`h_aff(z) ≤ n⁻¹ exp(-(5n)^(3n)) (1 + h_aff(x))`, then `w z` has scalar-sum height less than
`1 / q₀`. With `w = x b⁻¹` for a packing centre `b` and `y = x z`, this bounds `h_s(y b⁻¹)`. -/
theorem scalarSumHeight_mul_lt_of_absoluteLogHeightAff_le {n : ℕ} {w x z : Fin n → F}
    (hw : ∀ i, IsAlgebraic ℚ (w i)) (hz : ∀ i, IsAlgebraic ℚ (z i))
    (hwq : scalarSumHeight w < (2 * exp ((4 * n : ℝ) ^ (3 * n)))⁻¹)
    (hx : absoluteLogHeightAff x ≤ 4 * n * log n)
    (hzx : absoluteLogHeightAff z ≤
      (n : ℝ)⁻¹ * exp (-((5 * n : ℝ) ^ (3 * n))) * (1 + absoluteLogHeightAff x)) :
    scalarSumHeight (w * z) < (exp ((4 * n : ℝ) ^ (3 * n)))⁻¹ := by
  have hzq := scalarSumHeight_lt_of_absoluteLogHeightAff_le hz hx hzx
  have h2 : (exp ((4 * n : ℝ) ^ (3 * n)))⁻¹ =
      (2 * exp ((4 * n : ℝ) ^ (3 * n)))⁻¹ + (2 * exp ((4 * n : ℝ) ^ (3 * n)))⁻¹ := by
    rw [mul_inv]
    ring
  rw [h2]
  exact (scalarSumHeight_mul_le w z hw hz).trans_lt (add_lt_add hwq hzq)

/-- For `n ≥ 2` and `r ≥ 0`, the large-solution bound `2^(2(n+9)²) (8n² + 2n)^(n+4+r)`, the
number `2ⁿ` of subsum hyperplanes and the small-solution bound `q₀ (16 n³ q₀)^r`, with
`q₀ = exp((4n)^(3n))`, add up to less than `exp((5n)^(3n) (r + 1))`. For `n = 1` and `r = 0`
the first term alone exceeds `exp(125)`. -/
theorem two_pow_mul_pow_add_two_pow_add_exp_mul_pow_lt_exp {n : ℕ} (hn : 2 ≤ n) (r : ℕ) :
    (2 : ℝ) ^ (2 * (n + 9) ^ 2) * (8 * n ^ 2 + 2 * n : ℝ) ^ (n + 4 + r) + 2 ^ n +
        exp ((4 * n : ℝ) ^ (3 * n)) * (16 * n ^ 3 * exp ((4 * n : ℝ) ^ (3 * n))) ^ r <
      exp ((5 * n : ℝ) ^ (3 * n) * (r + 1)) := by
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hA : (0 : ℝ) ≤ (5 * n : ℝ) ^ (3 * n) := by positivity
  have hB : (0 : ℝ) ≤ (4 * n : ℝ) ^ (3 * n) := by positivity
  have hAB := four_mul_pow_add_le_five_mul_pow hn
  set A := (5 * n : ℝ) ^ (3 * n)
  set B := (4 * n : ℝ) ^ (3 * n)
  set N : ℝ := (n : ℝ)
  set R : ℝ := (r : ℝ)
  set M := A * (R + 1) - 2 with hM
  -- The three exponents are polynomial in `n` and `r`, and each is at most `M`.
  obtain ⟨t, ht, htN⟩ : ∃ t : ℝ, 0 ≤ t ∧ N = 2 + t := ⟨N - 2, by linarith, by ring⟩
  have hP : 4 * (N + 9) ^ 2 + (N + 4) * (8 * N ^ 2 + 2 * N) + 2 ≤ 4096 * N ^ 6 := by
    rw [htN]
    nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5,
      pow_nonneg ht 6]
  have hQ : 16 * N ^ 3 + 2 * N + 8 * N ^ 2 + 2 ≤ 4096 * N ^ 6 := by
    rw [htN]
    nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5,
      pow_nonneg ht 6]
  have hAR : A ≤ A * (R + 1) := le_mul_of_one_le_right (by linarith) (by linarith)
  have h₁ : (2 : ℝ) ^ (2 * (n + 9) ^ 2) * (8 * N ^ 2 + 2 * N) ^ (n + 4 + r) ≤ exp M := by
    have hb : (0 : ℝ) ≤ 8 * N ^ 2 + 2 * N := by positivity
    refine (mul_le_mul (pow_le_exp_mul zero_le_two _) (pow_le_exp_mul hb _)
      (pow_nonneg hb _) (exp_pos _).le).trans ?_
    rw [← exp_add, exp_le_exp]
    push_cast
    -- The base `8n² + 2n` is at most `A`, so its `r`-fold contribution is at most `r A`.
    have hbA : 8 * N ^ 2 + 2 * N ≤ A := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hbA hR]
  have h₂ : (2 : ℝ) ^ n ≤ exp M := by
    refine (pow_le_exp_mul zero_le_two n).trans (exp_le_exp.2 ?_)
    nlinarith
  have h₃ : exp B * (16 * N ^ 3 * exp B) ^ r ≤ exp M := by
    have hb : (0 : ℝ) ≤ 16 * N ^ 3 := by positivity
    rw [mul_pow, ← exp_natCast_mul]
    refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_exp_mul hb r)
      (exp_pos _).le) (exp_pos _).le).trans ?_
    rw [← exp_add, ← exp_add, exp_le_exp]
    -- Each of the `r` factors `16 n³ q₀` has logarithm at most `16 n³ + B ≤ A`.
    have hbA : 16 * N ^ 3 + B ≤ A := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hbA hR]
  -- Three terms of size at most `exp M` sum to less than `exp (M + 2)`.
  have h3 : 3 * exp M < exp (A * (R + 1)) := by
    have : exp (A * (R + 1)) = exp 2 * exp M := by rw [← exp_add, hM]; ring_nf
    rw [this]
    have h2 : (3 : ℝ) < exp 2 := by linarith [add_one_lt_exp (two_ne_zero (α := ℝ))]
    nlinarith [exp_pos M]
  linarith

/-! With `4n` in place of `5n`, the perturbation budget exceeds `1 / q₀` for every `n ≥ 2`. -/

example {n : ℕ} (hn : 2 ≤ n) :
    (exp ((4 * n : ℝ) ^ (3 * n)))⁻¹ < exp (-((4 * n : ℝ) ^ (3 * n))) * (1 + 4 * n * log n) := by
  have hlog : 0 < 4 * n * log n := by
    have : (1 : ℝ) < n := by exact_mod_cast hn
    have := log_pos this
    positivity
  rw [exp_neg]
  exact lt_mul_of_one_lt_right (by positivity) (by linarith)

end TauCeti
