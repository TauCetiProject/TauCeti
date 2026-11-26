/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ModularForms.LevelOne.JInputs
import TauCeti.Analysis.Normed.Ring.InfiniteProd.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.NegPiMulSqrt
import TauCeti.Analysis.SpecialFunctions.QPochhammer
import TauCeti.NumberTheory.ArithmeticFunction.Sigma.Evaluation
import TauCeti.NumberTheory.ModularForms.DedekindEta.Basic

/-!
# An explicit bound for the modular invariant

On the half-plane `Im τ ≥ √3 / 2`, which contains the standard fundamental domain, the modular
invariant `j` stays within an absolute constant of the leading term `q⁻¹` of its `q`-expansion,
`q = e^{2πiτ}`:

  `‖j τ - q⁻¹‖ ≤ 2114567 / 1000`, hence `‖j τ‖ ≤ e^{2π Im τ} + 2114567 / 1000`.

At the root `τ = (-b + i √D) / (2a)` of a reduced positive definite form `a x² + b x y + c y²`
of discriminant `-D`, which satisfies `Im τ ≥ √3 / 2`, this reads
`|j(τ)| ≤ e^{π √D / a} + 2114.567` (`TauCeti.BinaryQuadraticForm.norm_j_root_le`). This is the
unconditional bound on singular moduli used to bound the coefficients of Hilbert class
polynomials, and hence the precision needed to recover them from approximate roots or from
reductions modulo primes.

## Main results

* `TauCeti.ModularForm.norm_j_sub_inv_qParam_le`: `‖j τ - q⁻¹‖ ≤ 2114567 / 1000` for
  `√3 / 2 ≤ Im τ`.
* `TauCeti.ModularForm.norm_j_le`: `‖j τ‖ ≤ exp (2π Im τ) + 2114567 / 1000` for `√3 / 2 ≤ Im τ`.

## Implementation notes

The estimate uses only `Δ = q ∏ₙ (1 - qⁿ)²⁴` (Mathlib's `ModularForm.discriminant_eq_q_prod`)
and `E₄ = 1 + 240 ∑ σ₃(n) qⁿ`, with `|q| ≤ e^{-π√3} < 1/230`. Writing `P = ∏ₙ (1 - qⁿ)²⁴`, one
has `j - q⁻¹ = (E₄³ - P) / (q P)`. The Lambert bound for the divisor sum gives
`‖E₄ - 1‖ ≤ 250 |q|`, and the bound for the `q`-Pochhammer product
(`TauCeti.norm_tprod_one_sub_pow_mul_sub_one_le_div`) gives
`‖∏ₙ (1 - qⁿ) - 1‖ ≤ 1.01 |q|`. Expanding the cube and the twenty-fourth power then bounds
`‖E₄³ - P‖ / (|q| ‖P‖)` by about `2098`. Only the constant `2114567 / 1000` is taken from
Sutherland's lemma, so that the bound has the form in which it is quoted there.

## References

* A. V. Sutherland, *Computing Hilbert class polynomials with the Chinese Remainder Theorem*,
  Math. Comp. 80 (2011), Appendix 1, Lemma 8.
-/

public section

open UpperHalfPlane ModularForm
open scoped Real

local notation "𝕢" => Function.Periodic.qParam

namespace TauCeti.ModularForm

/-- On `Im τ ≥ √3 / 2` the nome satisfies `|q| ≤ 1/230`. -/
private theorem norm_qParam_le {τ : ℍ} (hτ : √3 / 2 ≤ τ.im) : ‖𝕢 1 (τ : ℂ)‖ ≤ 1 / 230 := by
  rw [Function.Periodic.norm_qParam, coe_im, div_one]
  calc Real.exp (-2 * π * τ.im) ≤ Real.exp (-(π * √3)) :=
        Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
    _ ≤ 1 / 230 := TauCeti.exp_neg_pi_mul_sqrt_le (s := 1.7320508) (c := 0.4413) 5
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num [Finset.sum_range_succ, Nat.factorial])

/-- `‖E₄ τ - 1‖ ≤ 250 |q|` when `|q| ≤ 1/230`: the Lambert bound for `E₄ - 1 = 240 s₃(q)`. -/
private theorem norm_E₄_sub_one_le {τ : ℍ} (hq : ‖𝕢 1 (τ : ℂ)‖ ≤ 1 / 230) :
    ‖E₄ τ - 1‖ ≤ 250 * ‖𝕢 1 (τ : ℂ)‖ := by
  have hexp : Complex.exp (2 * π * Complex.I * τ) = 𝕢 1 (τ : ℂ) := by
    simp [Function.Periodic.qParam]
  rw [E₄_apply_eq_divisorSumAt, hexp, add_sub_cancel_left, norm_mul,
    show ‖(240 : ℂ)‖ = 240 by norm_num]
  have hr1 : ‖𝕢 1 (τ : ℂ)‖ < 1 := by linarith
  have hσ := TauCeti.norm_divisorSumAt_le_tsum_div_one_sub (K := ℂ) 3 hr1
  set r := ‖𝕢 1 (τ : ℂ)‖
  have hr0 : 0 ≤ r := norm_nonneg _
  rw [tsum_pow_mul_geometric_of_norm_lt_one 3 (by rwa [Real.norm_of_nonneg hr0])] at hσ
  set b := (1 - r)⁻¹
  have hb : b ≤ 230 / 229 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  -- `∑ n³ rⁿ = r / (1 - r)² + 6 r² / (1 - r)³ + 6 r³ / (1 - r)⁴`
  replace hσ :
      ‖divisorSumAt 3 (𝕢 1 (τ : ℂ))‖ ≤ r * (b ^ 3 + 6 * r * b ^ 4 + 6 * r ^ 2 * b ^ 5) := by
    refine hσ.trans_eq ?_
    have h1 : Nat.stirlingSecond 3 1 = 1 := by decide
    have h2 : Nat.stirlingSecond 3 2 = 3 := by decide
    have h3 : Nat.stirlingSecond 3 3 = 1 := by decide
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, h1, h2, h3,
      Nat.stirlingSecond_succ_zero, Nat.factorial, b, div_eq_mul_inv, ← inv_pow]
    push_cast
    ring
  have hpoly : b ^ 3 + 6 * r * b ^ 4 + 6 * r ^ 2 * b ^ 5 ≤
      (230 / 229) ^ 3 + 6 * (1 / 230) * (230 / 229) ^ 4 + 6 * (1 / 230) ^ 2 * (230 / 229) ^ 5 := by
    gcongr
  have hnum : (240 : ℝ) * ((230 / 229) ^ 3 + 6 * (1 / 230) * (230 / 229) ^ 4 +
      6 * (1 / 230) ^ 2 * (230 / 229) ^ 5) ≤ 250 := by norm_num
  nlinarith [mul_le_mul_of_nonneg_left hpoly hr0, hnum]

/-- `‖∏ₙ (1 - qⁿ⁺¹) - 1‖ ≤ 1.01 |q|` when `|q| ≤ 1/230`. -/
private theorem norm_tprod_one_sub_eta_q_sub_one_le {τ : ℍ} (hq : ‖𝕢 1 (τ : ℂ)‖ ≤ 1 / 230) :
    ‖∏' n, (1 - eta_q n τ) - 1‖ ≤ 101 / 100 * ‖𝕢 1 (τ : ℂ)‖ := by
  have h := TauCeti.norm_tprod_one_sub_pow_mul_sub_one_le_div (q := 𝕢 1 (τ : ℂ)) (by linarith)
    (w := 1) (by simp)
  simp only [mul_one] at h
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith [norm_nonneg (𝕢 1 (τ : ℂ))]

/-- `j - q⁻¹ = (E₄³ - Q²⁴) / (q Q²⁴)` for the eta product `Q = ∏ₙ (1 - qⁿ⁺¹)`. -/
private theorem j_sub_inv_qParam_eq (τ : ℍ) :
    j τ - (𝕢 1 (τ : ℂ))⁻¹ = (E₄ τ ^ 3 - (∏' n, (1 - eta_q n τ)) ^ 24) /
      (𝕢 1 (τ : ℂ) * (∏' n, (1 - eta_q n τ)) ^ 24) := by
  have hQ0 : ∏' n, (1 - eta_q n τ) ≠ 0 := eta_tprod_ne_zero τ.coe_im_pos
  have hq0 : 𝕢 1 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
  rw [j_apply, TauCeti.ModularForm.discriminant_eq_qParam_mul_tprod_pow]
  field_simp

/-- The bound `‖j τ - q⁻¹‖ ≤ 2114567 / 1000` whenever `|q| ≤ 1/230`. -/
private theorem norm_j_sub_inv_qParam_le_of_norm_qParam_le {τ : ℍ}
    (hq : ‖𝕢 1 (τ : ℂ)‖ ≤ 1 / 230) : ‖j τ - (𝕢 1 (τ : ℂ))⁻¹‖ ≤ 2114567 / 1000 := by
  have hQ0 : ∏' n, (1 - eta_q n τ) ≠ 0 := eta_tprod_ne_zero τ.coe_im_pos
  have hq0 : 𝕢 1 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero _
  have hj := j_sub_inv_qParam_eq τ
  set q := 𝕢 1 (τ : ℂ)
  set r := ‖q‖
  set E := E₄ τ
  set Q := ∏' n, (1 - eta_q n τ)
  have hr0 : 0 < r := norm_pos_iff.2 hq0
  have hX := norm_E₄_sub_one_le hq
  have hu := norm_tprod_one_sub_eta_q_sub_one_le hq
  set X := ‖E - 1‖
  set u := ‖Q - 1‖
  have hu0 : 0 ≤ u := norm_nonneg _
  -- the eta product stays away from `0`
  have hQ : 1 - 101 / 100 * (1 / 230) ≤ ‖Q‖ := by
    have := norm_sub_norm_le 1 (1 - Q)
    rw [norm_one, sub_sub_cancel, norm_sub_rev] at this
    nlinarith
  -- the numerator: `‖E³ - 1‖ + ‖Q²⁴ - 1‖ ≤ r (1860.6 + 26.9)`
  have hE3 : ‖E ^ 3 - 1‖ ≤ 250 * r * (3 + 3 * (250 / 230) + (250 / 230) ^ 2) := by
    have hX' : X ≤ 250 / 230 := by nlinarith
    calc ‖E ^ 3 - 1‖ ≤ (1 + X) ^ 3 - 1 := TauCeti.norm_pow_sub_one_le E 3
      _ = X * (3 + 3 * X + X ^ 2) := by ring
      _ ≤ 250 * r * (3 + 3 * (250 / 230) + (250 / 230) ^ 2) := by gcongr
  have hP : ‖Q ^ 24 - 1‖ ≤ 101 / 100 * r * (24 * (1 + 101 / 100 * (1 / 230)) ^ 23) := by
    have hu' : u ≤ 101 / 100 * (1 / 230) := by nlinarith
    calc ‖Q ^ 24 - 1‖ ≤ (1 + u) ^ 24 - 1 ^ 24 := by
          simpa using TauCeti.norm_pow_sub_one_le Q 24
      _ ≤ |1 + u - 1| * (24 : ℕ) * max |1 + u| |1| ^ (24 - 1) :=
          (le_abs_self _).trans (abs_pow_sub_pow_le (1 + u) 1 24)
      _ = u * 24 * (1 + u) ^ 23 := by simp [abs_of_nonneg, hu0, add_nonneg zero_le_one hu0]
      _ ≤ 101 / 100 * r * (24 * (1 + 101 / 100 * (1 / 230)) ^ 23) := by
          rw [mul_assoc]
          gcongr
  -- the denominator: `‖q Q²⁴‖ ≥ r (1 - 1.01/230)²⁴`
  have hden : r * (1 - 101 / 100 * (1 / 230)) ^ 24 ≤ ‖q * Q ^ 24‖ := by
    rw [norm_mul, norm_pow]
    gcongr
  have hnum : ‖E ^ 3 - Q ^ 24‖ ≤ ‖E ^ 3 - 1‖ + ‖Q ^ 24 - 1‖ := by
    have := norm_sub_le (E ^ 3 - 1) (Q ^ 24 - 1)
    rwa [sub_sub_sub_cancel_right] at this
  have hconst : 250 * (3 + 3 * (250 / 230) + (250 / 230) ^ 2) +
      101 / 100 * (24 * (1 + 101 / 100 * (1 / 230)) ^ 23) ≤
      2114567 / 1000 * (1 - 101 / 100 * (1 / 230) : ℝ) ^ 24 := by norm_num
  rw [hj, norm_div, div_le_iff₀ (norm_pos_iff.2 (mul_ne_zero hq0 (pow_ne_zero _ hQ0)))]
  linarith [hnum, hE3, hP, hden, mul_le_mul_of_nonneg_left hconst hr0.le]

/-- **The modular invariant near the cusp.** On `Im τ ≥ √3 / 2`, a region containing the
standard fundamental domain, `j` differs from `q⁻¹`, `q = e^{2πiτ}`, by at most
`2114567 / 1000`. -/
theorem norm_j_sub_inv_qParam_le {τ : ℍ} (hτ : √3 / 2 ≤ τ.im) :
    ‖j τ - (𝕢 1 (τ : ℂ))⁻¹‖ ≤ 2114567 / 1000 :=
  norm_j_sub_inv_qParam_le_of_norm_qParam_le (norm_qParam_le hτ)

/-- **An explicit bound for the modular invariant.** On `Im τ ≥ √3 / 2`, a region containing the
standard fundamental domain, `|j(τ)| ≤ e^{2π Im τ} + 2114567 / 1000`. -/
theorem norm_j_le {τ : ℍ} (hτ : √3 / 2 ≤ τ.im) :
    ‖j τ‖ ≤ Real.exp (2 * π * τ.im) + 2114567 / 1000 := by
  have h := norm_j_sub_inv_qParam_le hτ
  have hinv : ‖(𝕢 1 (τ : ℂ))⁻¹‖ = Real.exp (2 * π * τ.im) := by
    rw [norm_inv, Function.Periodic.norm_qParam, coe_im, ← Real.exp_neg]
    ring_nf
  calc ‖j τ‖ ≤ ‖(𝕢 1 (τ : ℂ))⁻¹‖ + ‖j τ - (𝕢 1 (τ : ℂ))⁻¹‖ := norm_le_insert' _ _
    _ ≤ Real.exp (2 * π * τ.im) + 2114567 / 1000 := by rw [hinv]; gcongr

end TauCeti.ModularForm
