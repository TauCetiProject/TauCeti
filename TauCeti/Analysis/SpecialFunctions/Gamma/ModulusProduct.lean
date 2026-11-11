/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The modulus of `Γ` on vertical lines

This file proves the infinite product for `Γ(x)² / |Γ(x + iy)|²` (DLMF 5.8.3), the resulting
monotonicity of `|Γ(x + iy)| / Γ(x)` in `x > 0`, and the values of `|Γ|²` on the lines
`Re z = 0` and `Re z = 1` (DLMF 5.4.3).

## Main results

* `Complex.hasProd_Gamma_norm_quotient`: for real `x ∉ {0, −1, −2, …}` and real `y`,
  `∏_{k ≥ 0} (1 + y²/(x + k)²) = Γ(x)² / |Γ(x + iy)|²` (DLMF 5.8.3).
* `Complex.norm_Gamma_add_mul_I_le`: `|Γ(x + iy)| ≤ Γ(x)/Γ(x′) · |Γ(x′ + iy)|` for
  `0 < x ≤ x′`.
* `Complex.norm_Gamma_mul_I_sq`: `|Γ(iy)|² = π / (y sinh(πy))` for `y ≠ 0` (DLMF 5.4.3).
* `Complex.norm_Gamma_one_add_mul_I_sq`: `|Γ(1 + iy)|² = πy / sinh(πy)` for `y ≠ 0`.
* `Complex.hasProd_one_add_sq_div_succ_sq`: `∏_{k ≥ 1} (1 + y²/k²) = sinh(πy)/(πy)` for
  `y ≠ 0`.

## Implementation notes

The partial products of 5.8.3 are exactly `|GammaSeq x n / GammaSeq (x + iy) n|²`, so the
product follows from Euler's limit `Complex.GammaSeq_tendsto_Gamma`. The values on vertical
lines come from the reflection formula `Complex.Gamma_mul_Gamma_one_sub` and `Γ(z̄) = conj Γ(z)`.
-/

@[expose] public section

open Filter Finset

open scoped Topology Real ComplexConjugate

noncomputable section

namespace Complex

/-- `∑ₖ y²/(x + k)²` converges. -/
private theorem summable_sq_div_add_sq (x y : ℝ) :
    Summable fun k : ℕ => y ^ 2 / (x + k) ^ 2 := by
  have hg : Summable fun k : ℕ => 4 * y ^ 2 * (1 / (k : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
  refine Summable.of_norm_bounded_eventually_nat hg ?_
  filter_upwards [eventually_ge_atTop (⌈2 * |x|⌉₊ + 1)] with k hk
  have hk' : 2 * |x| + 1 ≤ k := by
    have := Nat.le_ceil (2 * |x|)
    have : ((⌈2 * |x|⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at this
    linarith
  have hk0 : (0 : ℝ) < k := by linarith [abs_nonneg x]
  have hxk2 : k / 2 ≤ x + k := by linarith [neg_abs_le x]
  have hxk0 : (0 : ℝ) < x + k := by linarith
  rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ (by positivity : (0 : ℝ) < (x + k) ^ 2)]
  have : (k : ℝ) ^ 2 / 4 ≤ (x + k) ^ 2 := by nlinarith
  field_simp
  nlinarith [sq_nonneg y, mul_le_mul_of_nonneg_left this (sq_nonneg y)]

/-- `∏ₖ (1 + y²/(x + k)²)` converges. -/
private theorem multipliable_one_add_sq_div_add_sq (x y : ℝ) :
    Multipliable fun k : ℕ => 1 + y ^ 2 / (x + k) ^ 2 :=
  Real.multipliable_one_add_of_summable (summable_sq_div_add_sq x y)

/-- The `tprod` form of DLMF 5.8.3: both sides are limits of the same Gauss sequences. -/
private theorem norm_Gamma_div_Gamma_add_mul_I_sq {x y : ℝ} (hx : ∀ k : ℕ, (x : ℂ) ≠ -k) :
    ‖(Real.Gamma x : ℂ) / Gamma (x + y * I)‖ ^ 2 =
      ∏' k : ℕ, (1 + y ^ 2 / (x + k) ^ 2) := by
  have hxk : ∀ k : ℕ, (x : ℂ) + k ≠ 0 := fun k h => hx k (eq_neg_of_add_eq_zero_left h)
  have hxk' : ∀ k : ℕ, (x + k : ℝ) ≠ 0 := fun k h => hxk k (by exact_mod_cast h)
  have hz : ∀ k : ℕ, (x : ℂ) + y * I ≠ -k := by
    intro k h
    have hre := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, neg_re, natCast_re] at hre
    exact hx k (by exact_mod_cast hre)
  have hmul := multipliable_one_add_sq_div_add_sq x y
  have hP : Tendsto (fun n : ℕ => ∏ k ∈ range (n + 1), (1 + y ^ 2 / (x + k) ^ 2)) atTop
      (𝓝 (∏' k : ℕ, (1 + y ^ 2 / (x + k) ^ 2))) :=
    hmul.hasProd.tendsto_prod_nat.comp (tendsto_add_atTop_nat 1)
  have hseq : ∀ n : ℕ, 0 < n →
      ‖GammaSeq x n / GammaSeq (x + y * I) n‖ ^ 2 =
        ∏ k ∈ range (n + 1), (1 + y ^ 2 / (x + k) ^ 2) := by
    intro n hn
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hP1 : ∏ j ∈ range (n + 1), ((x : ℂ) + j) ≠ 0 :=
      prod_ne_zero_iff.mpr fun j _ => hxk j
    have hP2 : ∏ j ∈ range (n + 1), ((x : ℂ) + y * I + j) ≠ 0 :=
      prod_ne_zero_iff.mpr fun j _ => fun h => hz j (eq_neg_of_add_eq_zero_left h)
    have hc1 : (n : ℂ) ^ (x : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn')
    have hc2 : (n : ℂ) ^ ((x : ℂ) + y * I) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn')
    have hsplit : GammaSeq x n / GammaSeq (x + y * I) n =
        ((n : ℂ) ^ (x : ℂ) / (n : ℂ) ^ ((x : ℂ) + y * I)) *
          (∏ j ∈ range (n + 1), ((x : ℂ) + y * I + j)) / ∏ j ∈ range (n + 1), ((x : ℂ) + j) := by
      simp only [GammaSeq]
      field_simp
    rw [hsplit, norm_div, norm_mul, norm_div, norm_natCast_cpow_of_pos hn,
      norm_natCast_cpow_of_pos hn]
    have hre : ((x : ℂ) + y * I).re = x := by simp
    rw [hre, ofReal_re, div_self (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) x).ne', one_mul,
      norm_prod, norm_prod, div_pow, ← prod_pow, ← prod_pow, ← prod_div_distrib]
    refine prod_congr rfl fun j _ => ?_
    have h1 : ‖(x : ℂ) + y * I + j‖ ^ 2 = (x + j) ^ 2 + y ^ 2 := by
      rw [← normSq_eq_norm_sq, normSq_apply]; simp; ring
    have h2 : ‖(x : ℂ) + j‖ ^ 2 = (x + j) ^ 2 := by
      rw [show (x : ℂ) + j = ((x + j : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_eq_abs, sq_abs]
    rw [h1, h2]
    have := hxk' j
    field_simp
  have hlim : Tendsto (fun n : ℕ => ‖GammaSeq x n / GammaSeq (x + y * I) n‖ ^ 2)
      atTop (𝓝 (‖Gamma x / Gamma (x + y * I)‖ ^ 2)) :=
    (((GammaSeq_tendsto_Gamma _).div (GammaSeq_tendsto_Gamma _)
      (Gamma_ne_zero hz)).norm).pow 2
  rw [← Gamma_ofReal]
  refine tendsto_nhds_unique hlim (hP.congr' ?_)
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (hseq n hn).symm

/-- **DLMF 5.8.3.** For real `x` that is not a nonpositive integer and real `y`, the product
`∏_{k ≥ 0} (1 + y²/(x + k)²)` converges to `Γ(x)² / |Γ(x + iy)|²`. -/
theorem hasProd_Gamma_norm_quotient {x : ℝ} (hx : ∀ n : ℕ, x ≠ -(n : ℝ)) (y : ℝ) :
    HasProd (fun k : ℕ => 1 + y ^ 2 / (x + k) ^ 2)
      (Real.Gamma x ^ 2 / ‖Gamma ((x : ℂ) + y * I)‖ ^ 2) := by
  have hx' : ∀ k : ℕ, (x : ℂ) ≠ -k := fun k h => hx k (by exact_mod_cast h)
  have h := norm_Gamma_div_Gamma_add_mul_I_sq (y := y) hx'
  rw [norm_div, norm_real, Real.norm_eq_abs, div_pow, sq_abs] at h
  rw [h]
  exact (multipliable_one_add_sq_div_add_sq x y).hasProd

/-- The modulus of `Γ` on a horizontal line, compared at two real parts: for `0 < x ≤ x′`,
`|Γ(x + iy)| ≤ Γ(x)/Γ(x′) · |Γ(x′ + iy)|`. This is the termwise comparison of the products in
DLMF 5.8.3. -/
theorem norm_Gamma_add_mul_I_le {x x' : ℝ} (hx : 0 < x) (hxx' : x ≤ x') (y : ℝ) :
    ‖Gamma ((x : ℂ) + y * I)‖ ≤ Real.Gamma x / Real.Gamma x' * ‖Gamma ((x' : ℂ) + y * I)‖ := by
  have hx' : 0 < x' := hx.trans_le hxx'
  have hnot : ∀ {u : ℝ}, 0 < u → ∀ n : ℕ, u ≠ -(n : ℝ) := fun hu n h => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hne : ∀ {u : ℝ}, 0 < u → Gamma ((u : ℂ) + y * I) ≠ 0 := fun hu => by
    refine Gamma_ne_zero fun n h => ?_
    have hre := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, neg_re, natCast_re] at hre
    exact hnot hu n hre
  have hG := Real.Gamma_pos_of_pos hx
  have hG' := Real.Gamma_pos_of_pos hx'
  have hN := norm_pos_iff.mpr (hne hx)
  have hN' := norm_pos_iff.mpr (hne hx')
  -- the termwise comparison of the two products
  have hle : Real.Gamma x' ^ 2 / ‖Gamma ((x' : ℂ) + y * I)‖ ^ 2 ≤
      Real.Gamma x ^ 2 / ‖Gamma ((x : ℂ) + y * I)‖ ^ 2 := by
    refine le_of_tendsto_of_tendsto' (hasProd_Gamma_norm_quotient (hnot hx') y)
      (hasProd_Gamma_norm_quotient (hnot hx) y) fun s => ?_
    refine prod_le_prod₀ (fun k _ => by positivity) fun k _ => ?_
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : (x + k) ^ 2 ≤ (x' + k) ^ 2 := by nlinarith
    gcongr
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hle
  have hsq : (‖Gamma ((x : ℂ) + y * I)‖ * Real.Gamma x') ^ 2 ≤
      (Real.Gamma x * ‖Gamma ((x' : ℂ) + y * I)‖) ^ 2 := by
    nlinarith
  have := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  rw [div_mul_eq_mul_div, le_div_iff₀ hG']
  exact this

/-- **DLMF 5.4.3.** `|Γ(iy)|² = π / (y sinh(πy))` for real `y ≠ 0`. -/
theorem norm_Gamma_mul_I_sq {y : ℝ} (hy : y ≠ 0) :
    ‖Gamma (y * I)‖ ^ 2 = π / (y * Real.sinh (π * y)) := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hz : (y : ℂ) * I ≠ 0 := mul_ne_zero hy' I_ne_zero
  have hnorm : Gamma (y * I) * Gamma (-(y * I)) = (‖Gamma (y * I)‖ : ℂ) ^ 2 := by
    have hconj : conj ((y : ℂ) * I) = -(y * I) := by simp
    rw [← hconj, Gamma_conj, mul_conj, normSq_eq_norm_sq, ofReal_pow]
  have hrefl := Gamma_mul_Gamma_one_sub (y * I)
  have h1 : Gamma (1 - y * I) = -(y * I) * Gamma (-(y * I)) := by
    rw [← Gamma_add_one (-(y * I)) (neg_ne_zero.mpr hz)]
    ring_nf
  have hsin : sin (π * (y * I)) = I * Real.sinh (π * y) := by
    have hsplit : (π : ℂ) * (y * I) = (0 : ℂ) + ((π * y : ℝ) : ℂ) * I := by push_cast; ring
    rw [hsplit, sin_add_mul_I]
    simp only [sin_zero, cos_zero, ← ofReal_sinh]
    ring
  have hsinh : (Real.sinh (π * y) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hy)
  rw [h1, hsin, eq_div_iff (mul_ne_zero I_ne_zero hsinh)] at hrefl
  have hsq : ((‖Gamma (y * I)‖ ^ 2 : ℝ) : ℂ) = ((π / (y * Real.sinh (π * y)) : ℝ) : ℂ) := by
    rw [ofReal_pow, ← hnorm, ofReal_div, ofReal_mul, eq_div_iff (mul_ne_zero hy' hsinh)]
    linear_combination hrefl +
      Gamma (y * I) * Gamma (-(y * I)) * y * Real.sinh (π * y) * I_sq
  exact_mod_cast hsq

/-- `|Γ(1 + iy)|² = πy / sinh(πy)` for real `y ≠ 0` (DLMF 5.4.3 with the recurrence). The
value at `y = 0` is `Γ(1)² = 1`. -/
theorem norm_Gamma_one_add_mul_I_sq {y : ℝ} (hy : y ≠ 0) :
    ‖Gamma (1 + y * I)‖ ^ 2 = π * y / Real.sinh (π * y) := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hsinh : Real.sinh (π * y) ≠ 0 := Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hy)
  rw [add_comm, Gamma_add_one _ (mul_ne_zero hy' I_ne_zero), norm_mul, mul_pow,
    norm_Gamma_mul_I_sq hy, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, sq_abs]
  field_simp

/-- The case `x = 1` of DLMF 5.8.3: `∏_{k ≥ 1} (1 + y²/k²) = sinh(πy)/(πy)` for real `y ≠ 0`,
indexed from `k = 0` as `∏_{k ≥ 0} (1 + y²/(1 + k)²)`. -/
theorem hasProd_one_add_sq_div_succ_sq {y : ℝ} (hy : y ≠ 0) :
    HasProd (fun k : ℕ => 1 + y ^ 2 / (1 + k) ^ 2) (Real.sinh (π * y) / (π * y)) := by
  have h1 : ∀ n : ℕ, (1 : ℝ) ≠ -(n : ℝ) := fun n h => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h := hasProd_Gamma_norm_quotient h1 y
  rw [ofReal_one, norm_Gamma_one_add_mul_I_sq hy, Real.Gamma_one, one_pow, one_div_div] at h
  exact h

end Complex
