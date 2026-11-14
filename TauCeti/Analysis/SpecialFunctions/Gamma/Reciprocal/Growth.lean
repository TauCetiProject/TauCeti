/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.NumberTheory.Harmonic.Bounds
public import TauCeti.Analysis.Complex.CanonicalProduct.ElementaryFactor
public import TauCeti.Analysis.SpecialFunctions.Log.GrowthScale
public import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Growth of the reciprocal Gamma functions

The reciprocal `1/Γ` is entire, and this file bounds its growth explicitly:

`‖Γ(s)⁻¹‖ ≤ exp (2 ‖s‖ log (1 + ‖s‖) + 10 ‖s‖)` for every `s : ℂ`,

hence `‖Γ(s)⁻¹‖ ≤ exp (22 (1 + ‖s‖) log (2 + ‖s‖))`, and bounds of the same shape for the
archimedean factors `Gammaℝ` and `Gammaℂ`. Mathlib's inverse is total, so at the poles of `Γ`
the left-hand sides are `0` and the bounds hold trivially there.

The proof uses no asymptotic expansion of `Γ`. Euler's sequence `GammaSeq` has reciprocal

`GammaSeq s n⁻¹ = s ∏_{k ≤ n} E₁(-s/k) exp (s (H_n - log n))`,

where `E₁(z) = (1 - z) e^z` is the genus-one elementary factor and `H_n` is the harmonic number.
Since `0 ≤ H_n - log n ≤ 1`, the exponential contributes at most `e^{‖s‖}`. The factors with
`k ≤ ‖s‖ + 1` are bounded by the global estimate `‖E₁(z)‖ ≤ e^{2‖z‖}`, which sums to
`2 ‖s‖ H_{⌊‖s‖⌋ + 1}`, and the remaining factors by the quadratic estimate
`‖E₁(z)‖ ≤ e^{3‖z‖²}`, which sums to at most `6 ‖s‖`. The bound passes to `Γ` in the limit
`GammaSeq s n → Γ(s)`.

The bound shows that `1/Γ` has order at most one. It cannot be improved to exponential type:
`‖Γ(-n - 1/2)⁻¹‖ = Γ(n + 3/2)/π` grows like `exp (n log n)`.

## Main results

* `Complex.inv_GammaSeq_eq`: Euler's finite product for `GammaSeq s n⁻¹` in Weierstrass form.
* `Complex.norm_inv_GammaSeq_le`, `Complex.norm_inv_Gamma_le`:
  `‖Γ(s)⁻¹‖ ≤ exp (2 ‖s‖ log (1 + ‖s‖) + 10 ‖s‖)`, and the same for every `GammaSeq s n⁻¹`.
* `Complex.norm_inv_Gamma_le_exp_mul_log`: `‖Γ(s)⁻¹‖ ≤ exp (22 (1 + ‖s‖) log (2 + ‖s‖))`.
* `Complex.norm_inv_Gammaℝ_le_exp_mul_log`, `Complex.norm_inv_Gammaℂ_le_exp_mul_log`: the
  corresponding bounds for `Gammaℝ⁻¹` and `Gammaℂ⁻¹`.

## References

* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §12.1.
-/

public section

open Finset Filter Topology
open scoped Real

namespace Complex

/-- One factor of Euler's product: `s + k = k E₁(-s/k) e^{s/k}` for `k = j + 1`. -/
theorem add_natCast_succ_eq_mul_weierstrassFactorOne (s : ℂ) (j : ℕ) :
    s + (j + 1 : ℕ) = (j + 1 : ℕ) * weierstrassFactor 1 (-s / (j + 1)) * exp (s / (j + 1)) := by
  have hj : (j + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  rw [weierstrassFactor_one_left, mul_assoc, mul_assoc, ← exp_add, neg_div, neg_add_cancel,
    exp_zero, mul_one]
  push_cast
  field_simp
  ring

/-- Euler's finite product for the reciprocal of `GammaSeq`, written with the genus-one
elementary factors `E₁(-s/k)`, `1 ≤ k ≤ n`, and the harmonic number `H_n`. -/
theorem inv_GammaSeq_eq (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    (GammaSeq s n)⁻¹ = s * (∏ j ∈ range n, weierstrassFactor 1 (-s / (j + 1))) *
      exp (s * ((harmonic n : ℂ) - Real.log n)) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hprod : ∏ j ∈ range (n + 1), (s + j) =
      s * (n.factorial : ℂ) * (∏ j ∈ range n, weierstrassFactor 1 (-s / (j + 1))) *
        exp (s * harmonic n) := by
    rw [prod_range_succ', Nat.cast_zero, add_zero]
    simp_rw [add_natCast_succ_eq_mul_weierstrassFactorOne, prod_mul_distrib, ← exp_sum,
      ← Nat.cast_prod, prod_range_add_one_eq_factorial, harmonic, Rat.cast_sum, mul_sum,
      div_eq_mul_inv]
    push_cast
    ring
  rw [GammaSeq, inv_div, hprod, cpow_def_of_ne_zero hn', ← natCast_log, mul_sub, exp_sub]
  field_simp

/-- Explicit growth of the reciprocals of Euler's sequence, uniformly in `n ≥ 1`. -/
theorem norm_inv_GammaSeq_le (s : ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖(GammaSeq s n)⁻¹‖ ≤ Real.exp (2 * ‖s‖ * Real.log (1 + ‖s‖) + 10 * ‖s‖) := by
  set r := ‖s‖ with hr_def
  have hr : 0 ≤ r := norm_nonneg s
  -- The factor `exp (s (H_n - log n))`, using `0 ≤ H_n - log n ≤ 1`.
  have hH₀ : Real.log n ≤ harmonic n :=
    (Real.log_le_log (y := ((n + 1 : ℕ) : ℝ)) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
      (by push_cast; linarith)).trans (by exact_mod_cast log_add_one_le_harmonic n)
  have hH₁ : (harmonic n : ℝ) ≤ 1 + Real.log n := harmonic_le_one_add_log n
  have hexp : ‖exp (s * ((harmonic n : ℂ) - Real.log n))‖ ≤ Real.exp r := by
    rw [norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have : (s * ((harmonic n : ℂ) - Real.log n)).re = s.re * ((harmonic n : ℝ) - Real.log n) := by
      rw [← ofReal_ratCast, ← ofReal_sub, re_mul_ofReal]
    rw [this]
    calc
      _ ≤ |s.re| * ((harmonic n : ℝ) - Real.log n) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
      _ ≤ r * 1 := mul_le_mul (abs_re_le_norm s) (by linarith) (by linarith) hr
      _ = r := mul_one r
  -- The elementary factors: `k ≤ N` by the linear bound, `k > N` by the quadratic one.
  set N := ⌊r⌋₊ + 1 with hN_def
  have hNr : r < N := by rw [hN_def]; push_cast; exact Nat.lt_floor_add_one r
  have hN_le : (N : ℝ) ≤ r + 1 := by rw [hN_def]; push_cast; linarith [Nat.floor_le hr]
  let c : ℕ → ℝ := fun j ↦ if j + 1 ≤ N then 2 * (r / (j + 1)) else 3 * (r / (j + 1)) ^ 2
  have hfac (j : ℕ) : ‖weierstrassFactor 1 (-s / (j + 1))‖ ≤ Real.exp (c j) := by
    have hnorm : ‖-s / (j + 1)‖ = r / (j + 1) := by
      rw [norm_div, norm_neg, ← hr_def]
      congr 1
      exact_mod_cast Complex.norm_natCast (j + 1)
    simp only [c]
    split_ifs with hj
    · rw [← hnorm]
      exact norm_weierstrassFactor_one_le_exp _
    · rw [← hnorm]
      refine norm_weierstrassFactor_one_le_exp_sq ?_
      rw [hnorm, div_le_one (by positivity)]
      have : (N : ℝ) ≤ j := by exact_mod_cast (by omega : N ≤ j)
      linarith
  have hsmall : ∑ j ∈ (range n).filter (fun j ↦ j + 1 ≤ N), 2 * (r / (j + 1)) ≤
      2 * r * (1 + Real.log (1 + r)) := by
    calc
      _ ≤ ∑ j ∈ range N, 2 * (r / (j + 1)) := by
        refine sum_le_sum_of_subset_of_nonneg (fun j hj ↦ ?_) (fun _ _ _ ↦ by positivity)
        simp only [mem_filter] at hj
        exact mem_range.mpr (by omega)
      _ = 2 * r * (harmonic N : ℝ) := by
        simp only [harmonic, Rat.cast_sum, mul_sum, div_eq_mul_inv]
        push_cast
        ring_nf
      _ ≤ 2 * r * (1 + Real.log (1 + r)) := by
        refine mul_le_mul_of_nonneg_left ((harmonic_le_one_add_log N).trans ?_) (by positivity)
        have : (0 : ℝ) < N := by positivity
        linarith [Real.log_le_log this (by linarith : (N : ℝ) ≤ 1 + r)]
  have hlarge : ∑ j ∈ (range n).filter (fun j ↦ ¬j + 1 ≤ N), 3 * (r / (j + 1)) ^ 2 ≤ 6 * r := by
    calc
      _ = ∑ i ∈ ((range n).filter (fun j ↦ ¬j + 1 ≤ N)).image (fun j : ℕ ↦ j + 1),
            3 * r ^ 2 * ((i : ℝ) ^ 2)⁻¹ := by
        rw [sum_image (fun _ _ _ _ h ↦ by omega)]
        refine sum_congr rfl fun j _ ↦ ?_
        push_cast
        rw [div_pow, div_eq_mul_inv]
        ring
      _ ≤ ∑ i ∈ Ioo N (n + 1), 3 * r ^ 2 * ((i : ℝ) ^ 2)⁻¹ := by
        refine sum_le_sum_of_subset_of_nonneg (fun i hi ↦ ?_) (fun _ _ _ ↦ by positivity)
        simp only [mem_image, mem_filter, mem_range] at hi
        obtain ⟨j, ⟨hj, hjN⟩, rfl⟩ := hi
        exact mem_Ioo.mpr ⟨by omega, by omega⟩
      _ = 3 * r ^ 2 * ∑ i ∈ Ioo N (n + 1), ((i : ℝ) ^ 2)⁻¹ := (mul_sum _ _ _).symm
      _ ≤ 3 * r ^ 2 * (2 / (N + 1)) :=
        mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le N (n + 1)) (by positivity)
      _ ≤ 6 * r := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        -- `6 r² ≤ 6 r (N + 1)` since `r < N`.
        nlinarith
  have hprod : ‖∏ j ∈ range n, weierstrassFactor 1 (-s / (j + 1))‖ ≤
      Real.exp (2 * r * (1 + Real.log (1 + r)) + 6 * r) := by
    rw [norm_prod]
    calc
      _ ≤ ∏ j ∈ range n, Real.exp (c j) :=
        prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun j _ ↦ hfac j
      _ = Real.exp (∑ j ∈ range n, c j) := (Real.exp_sum _ _).symm
      _ ≤ _ := by
        refine Real.exp_le_exp.mpr ?_
        simp only [c]
        rw [sum_ite]
        exact add_le_add hsmall hlarge
  -- The leading factor `s`.
  have hs : r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  rw [inv_GammaSeq_eq s hn, norm_mul, norm_mul, ← hr_def]
  calc
    _ ≤ Real.exp r * Real.exp (2 * r * (1 + Real.log (1 + r)) + 6 * r) * Real.exp r :=
      mul_le_mul (mul_le_mul hs hprod (norm_nonneg _) (Real.exp_pos _).le) hexp (norm_nonneg _)
        (by positivity)
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf

/-- Explicit growth of `1/Γ`: `‖Γ(s)⁻¹‖ ≤ exp (2 ‖s‖ log (1 + ‖s‖) + 10 ‖s‖)` for every `s`.
At the poles of `Γ` the left-hand side is `0`. -/
theorem norm_inv_Gamma_le (s : ℂ) :
    ‖(Gamma s)⁻¹‖ ≤ Real.exp (2 * ‖s‖ * Real.log (1 + ‖s‖) + 10 * ‖s‖) := by
  by_cases h : Gamma s = 0
  · rw [h, inv_zero, norm_zero]
    positivity
  exact le_of_tendsto ((GammaSeq_tendsto_Gamma s).inv₀ h).norm
    ((eventually_ne_atTop 0).mono fun n hn ↦ norm_inv_GammaSeq_le s hn)

/-- `1/Γ` is bounded by `exp (22 (1 + ‖s‖) log (2 + ‖s‖))` on all of `ℂ`. -/
theorem norm_inv_Gamma_le_exp_mul_log (s : ℂ) :
    ‖(Gamma s)⁻¹‖ ≤ Real.exp (22 * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  refine (norm_inv_Gamma_le s).trans (Real.exp_le_exp.mpr ?_)
  convert Real.mul_mul_log_one_add_add_mul_le (A := 2) (B := 10) (by norm_num) (by norm_num)
    (norm_nonneg s) using 2
  norm_num

/-- `1/Gammaℝ` is bounded by `exp (15 (1 + ‖s‖) log (2 + ‖s‖))` on all of `ℂ`. -/
theorem norm_inv_Gammaℝ_le_exp_mul_log (s : ℂ) :
    ‖(Gammaℝ s)⁻¹‖ ≤ Real.exp (15 * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  set r := ‖s‖ with hr_def
  have hr : 0 ≤ r := norm_nonneg s
  have hpi : |Real.log π| ≤ 4 := by
    rw [abs_of_nonneg (Real.log_nonneg (by linarith [Real.two_le_pi]))]
    linarith [Real.log_le_sub_one_of_pos Real.pi_pos, Real.pi_le_four]
  have hpow : ‖((π : ℂ) ^ (-s / 2))⁻¹‖ ≤ Real.exp (2 * r) := by
    rw [← cpow_neg, neg_div, neg_neg]
    refine (norm_ofReal_cpow_le_exp Real.pi_pos _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_div, Complex.norm_two, ← hr_def]
    -- `|log π| (r / 2) ≤ 4 (r / 2)` by `hpi`.
    nlinarith [abs_nonneg (Real.log π)]
  have hhalf : ‖s / 2‖ = r / 2 := by rw [norm_div, Complex.norm_two]
  have hG := norm_inv_Gamma_le (s / 2)
  rw [hhalf] at hG
  have hlog : Real.log (1 + r / 2) ≤ Real.log (1 + r) :=
    Real.log_le_log (by linarith) (by linarith)
  rw [Gammaℝ_def, mul_inv, norm_mul]
  calc
    _ ≤ Real.exp (2 * r) * Real.exp (2 * (r / 2) * Real.log (1 + r / 2) + 10 * (r / 2)) :=
      mul_le_mul hpow hG (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (1 * r * Real.log (1 + r) + 7 * r) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      -- `r log (1 + r / 2) ≤ r log (1 + r)` by `hlog`; the linear terms add up to `7 r`.
      nlinarith
    _ ≤ _ := by
      refine Real.exp_le_exp.mpr ?_
      convert Real.mul_mul_log_one_add_add_mul_le (A := 1) (B := 7) (by norm_num) (by norm_num) hr
        using 2
      norm_num

/-- `1/Gammaℂ` is bounded by `exp (36 (1 + ‖s‖) log (2 + ‖s‖))` on all of `ℂ`. -/
theorem norm_inv_Gammaℂ_le_exp_mul_log (s : ℂ) :
    ‖(Gammaℂ s)⁻¹‖ ≤ Real.exp (36 * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  set r := ‖s‖ with hr_def
  have hr : 0 ≤ r := norm_nonneg s
  have h2pi : (0 : ℝ) < 2 * π := by positivity
  have hlog2pi : |Real.log (2 * π)| ≤ 7 := by
    rw [abs_of_nonneg (Real.log_nonneg (by linarith [Real.two_le_pi]))]
    linarith [Real.log_le_sub_one_of_pos h2pi, Real.pi_le_four]
  have hpow : ‖((2 * π : ℂ) ^ (-s))⁻¹‖ ≤ Real.exp (7 * r) := by
    rw [← cpow_neg, neg_neg, ← ofReal_ofNat, ← ofReal_mul]
    refine (norm_ofReal_cpow_le_exp h2pi _).trans (Real.exp_le_exp.mpr ?_)
    rw [← hr_def]
    -- `|log (2π)| r ≤ 7 r` by `hlog2pi`.
    nlinarith [abs_nonneg (Real.log (2 * π))]
  have hG := norm_inv_Gamma_le s
  rw [← hr_def] at hG
  rw [Gammaℂ_def, mul_inv, mul_inv, norm_mul, norm_mul]
  have h2 : ‖(2 : ℂ)⁻¹‖ ≤ 1 := by rw [norm_inv, Complex.norm_two]; norm_num
  calc
    _ ≤ 1 * Real.exp (7 * r) * Real.exp (2 * r * Real.log (1 + r) + 10 * r) :=
      mul_le_mul (mul_le_mul h2 hpow (norm_nonneg _) zero_le_one) hG (norm_nonneg _)
        (by positivity)
    _ = Real.exp (2 * r * Real.log (1 + r) + 17 * r) := by
      rw [one_mul, ← Real.exp_add]
      ring_nf
    _ ≤ _ := by
      refine Real.exp_le_exp.mpr ?_
      convert Real.mul_mul_log_one_add_add_mul_le (A := 2) (B := 17) (by norm_num) (by norm_num)
        hr using 2
      norm_num

end Complex
