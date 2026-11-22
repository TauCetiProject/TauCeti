/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Conjugate

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

To the left of `1` the continued `L`-function is still real on the real axis, so by the
intermediate value theorem it stays positive until its first real zero. This is the sign
information about possible exceptional zeros used in Siegel's theorem.

## Main results

* `DirichletCharacter.LFunction_pos_of_one_lt`: for a quadratic character `χ` and real `s > 1`,
  `0 < L(s, χ)`.
* `DirichletCharacter.LFunction_apply_one_pos`: for a nontrivial quadratic character `χ`,
  `0 < L(1, χ)`.
* `DirichletCharacter.LFunction_pos_of_one_le`: for a nontrivial quadratic character `χ` and
  real `s ≥ 1`, `0 < L(s, χ)`.
* `DirichletCharacter.LFunction_pos_of_forall_ne_zero`,
  `DirichletCharacter.LFunction_nonneg_of_forall_ne_zero`: positivity persists to the left of `1`
  up to the first real zero. If `L(σ, χ) ≠ 0` for `β ≤ σ < 1`, then `0 < L(β, χ)`; if only
  `L(σ, χ) ≠ 0` for `β < σ < 1`, then `0 ≤ L(β, χ)`.

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

/-- The continued `L`-function of a nontrivial quadratic Dirichlet character is a positive real
number at every real point `s ≥ 1`. -/
theorem LFunction_pos_of_one_le (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) {s : ℝ} (hs : 1 ≤ s) :
    0 < χ.LFunction s := by
  rcases hs.eq_or_lt with rfl | hs
  · simpa using LFunction_apply_one_pos hχ hχ₁
  · exact LFunction_pos_of_one_lt hχ hs

/-- The continued `L`-function of a nontrivial quadratic Dirichlet character is a positive real
number at every real point `β` such that it has no zero in `[β, 1)`. -/
theorem LFunction_pos_of_forall_ne_zero (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) {β : ℝ}
    (h : ∀ σ ∈ Set.Ico β 1, χ.LFunction σ ≠ 0) : 0 < χ.LFunction β := by
  rcases le_or_gt 1 β with hβ | hβ
  · exact LFunction_pos_of_one_le hχ hχ₁ hβ
  have him (σ : ℝ) : (χ.LFunction σ).im = 0 := LFunction_im_eq_zero_of_isQuadratic hχ σ (.inr hχ₁)
  have h₁ := Complex.pos_iff.mp (LFunction_pos_of_one_le hχ hχ₁ le_rfl)
  refine Complex.pos_iff.mpr ⟨?_, (him β).symm⟩
  -- Otherwise the real part has a zero in `[β, 1]`, which is not `1` since `L(1, χ) > 0`.
  by_contra hle
  have hcont : ContinuousOn (fun σ : ℝ ↦ (χ.LFunction σ).re) (Set.Icc β 1) :=
    (continuous_re.comp ((differentiable_LFunction hχ₁).continuous.comp
      continuous_ofReal)).continuousOn
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hβ.le hcont ⟨not_lt.mp hle, by simpa using h₁.1.le⟩
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact h₁.1.ne' (by simpa using hc0)
  exact h c ⟨hc.1, lt_of_le_of_ne hc.2 hc1⟩ (Complex.ext hc0 (him c))

/-- The continued `L`-function of a nontrivial quadratic Dirichlet character is a nonnegative
real number at every real point `β` such that it has no zero in `(β, 1)`. -/
theorem LFunction_nonneg_of_forall_ne_zero (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) {β : ℝ}
    (h : ∀ σ ∈ Set.Ioo β 1, χ.LFunction σ ≠ 0) : 0 ≤ χ.LFunction β := by
  by_cases hβ : χ.LFunction β = 0
  · exact hβ.ge
  refine (LFunction_pos_of_forall_ne_zero hχ hχ₁ fun σ hσ ↦ ?_).le
  rcases hσ.1.eq_or_lt with rfl | h'
  · exact hβ
  · exact h σ ⟨h', hσ.2⟩

end DirichletCharacter
