/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Positivity of the `L`-function of a quadratic character on `[1, ∞)`

A quadratic Dirichlet character `χ` takes only the values `0`, `1` and `-1`. At a real point
`s > 1` every Euler factor `(1 - χ(p) p⁻ˢ)⁻¹` is then a positive real number, and the logarithmic
form of the Euler product writes `L(s, χ)` as the exponential of a real number. Hence `L(s, χ)` is
real and positive there. For nontrivial `χ` the continued `L`-function is continuous at `s = 1`, so
`L(1, χ)` is a nonnegative real number; Mathlib's nonvanishing theorem
`DirichletCharacter.LFunction_apply_one_ne_zero` then makes it positive.

Positivity is stated with `ComplexOrder`, where `0 < z` means that `z` is a positive real number.
The value `L(1, χ)` is the one that enters the analytic class number formula of a quadratic field,
where it is compared with real quantities.

## Main results

* `DirichletCharacter.LFunction_pos_of_one_lt`: for a quadratic character `χ` and real `s > 1`,
  `0 < L(s, χ)`.
* `DirichletCharacter.LFunction_apply_one_pos`: for a nontrivial quadratic character `χ`,
  `0 < L(1, χ)`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 4 (the nonvanishing of `L(1, χ)` for real
  characters).
-/

public section

open Complex
open scoped ComplexOrder

namespace DirichletCharacter

variable {N : ℕ} {χ : DirichletCharacter ℂ N}

/-- For a quadratic character and a real point `s ≥ 0`, the term `-log (1 - χ(n) n⁻ˢ)` of the
logarithmic Euler product is real when `n ≥ 1`: the argument of the logarithm is a nonnegative
real number. -/
private lemma im_neg_log_one_sub_mul_cpow_eq_zero (hχ : χ.IsQuadratic) {s : ℝ} (hs : 0 ≤ s)
    {n : ℕ} (hn : 1 ≤ n) :
    (-log (1 - χ n * (n : ℂ) ^ (-(s : ℂ)))).im = 0 := by
  have hx : (n : ℂ) ^ (-(s : ℂ)) = ((n : ℝ) ^ (-s) : ℝ) := by
    rw [ofReal_cpow n.cast_nonneg, ofReal_neg, ofReal_natCast]
  have hx₀ : 0 ≤ (n : ℝ) ^ (-s) := by positivity
  have hx₁ : (n : ℝ) ^ (-s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (mod_cast hn) (neg_nonpos.mpr hs)
  rw [neg_im, neg_eq_zero, log_im, hx]
  rcases hχ n with h | h | h <;> rw [h]
  · simp
  · rw [one_mul, ← ofReal_one, ← ofReal_sub, arg_ofReal_of_nonneg (by linarith)]
  · rw [neg_one_mul, sub_neg_eq_add, ← ofReal_one, ← ofReal_add,
      arg_ofReal_of_nonneg (by linarith)]

variable [NeZero N]

/-- The `L`-function of a quadratic Dirichlet character is a positive real number at every real
point `s > 1`. -/
theorem LFunction_pos_of_one_lt (hχ : χ.IsQuadratic) {s : ℝ} (hs : 1 < s) :
    0 < χ.LFunction s := by
  have hs' : 1 < (s : ℂ).re := by rwa [ofReal_re]
  rw [LFunction_eq_LSeries χ hs', ← LSeries_eulerProduct_exp_log χ hs']
  -- Every term of the logarithmic Euler product is real, so the sum is real.
  set f : Nat.Primes → ℂ := fun p ↦ -log (1 - χ p * (p : ℂ) ^ (-(s : ℂ)))
  have hf (p : Nat.Primes) : ((f p).re : ℂ) = f p :=
    Complex.ext (ofReal_re _) <| by
      rw [ofReal_im, im_neg_log_one_sub_mul_cpow_eq_zero hχ (by linarith) p.prop.one_lt.le]
  have hsum : ∑' p, f p = ((∑' p, (f p).re : ℝ) : ℂ) := by
    rw [ofReal_tsum]
    exact tsum_congr fun p ↦ (hf p).symm
  rw [hsum, ← ofReal_exp]
  exact zero_lt_real.mpr (Real.exp_pos _)

/-- The value at `s = 1` of the `L`-function of a nontrivial quadratic Dirichlet character is a
positive real number. -/
theorem LFunction_apply_one_pos (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) :
    0 < χ.LFunction 1 := by
  refine lt_of_le_of_ne ?_ (LFunction_apply_one_ne_zero hχ₁).symm
  -- `L(1, χ)` is the limit of the positive values `L(s, χ)` as `s → 1⁺`.
  have hc : ContinuousWithinAt (fun s : ℝ ↦ χ.LFunction s) (Set.Ioi 1) 1 :=
    ((differentiable_LFunction hχ₁).continuous.comp continuous_ofReal).continuousWithinAt
  rw [← ofReal_one]
  exact ge_of_tendsto hc.tendsto <| eventually_nhdsWithin_of_forall fun s hs ↦
    (LFunction_pos_of_one_lt hχ hs).le

end DirichletCharacter
