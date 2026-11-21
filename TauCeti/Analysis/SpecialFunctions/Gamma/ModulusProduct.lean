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
import TauCeti.Analysis.Complex.Basic

/-!
# The modulus of `Γ` on vertical lines

This file proves the infinite product for `Γ(x)² / |Γ(x + iy)|²` (DLMF 5.8.3), the resulting
monotonicity of `|Γ(x + iy)| / Γ(x)` in `x > 0`, and the values of `|Γ|²` on the lines
`Re z = 0` and `Re z = 1` (DLMF 5.4.3).

## Main results

* `TauCeti.norm_GammaSeq_div_GammaSeq_add_mul_I_sq`: the partial products of DLMF 5.8.3 as
  `|GammaSeq x n / GammaSeq (x + iy) n|²`.
* `TauCeti.hasProd_Gamma_norm_quotient`: for real `x ∉ {0, −1, −2, …}` and real `y`,
  `∏_{k ≥ 0} (1 + y²/(x + k)²) = Γ(x)² / |Γ(x + iy)|²` (DLMF 5.8.3).
* `TauCeti.norm_Gamma_add_mul_I_le`: `|Γ(x + iy)| ≤ Γ(x)/Γ(x′) · |Γ(x′ + iy)|` for
  `0 < x ≤ x′`.
* `Real.norm_Gamma_mul_I_sq`: `|Γ(iy)|² = π / (y sinh(πy))` (DLMF 5.4.3).
* `TauCeti.norm_Gamma_one_add_mul_I_sq`: `|Γ(1 + iy)|² = πy / sinh(πy)` for `y ≠ 0`.
* `TauCeti.hasProd_one_add_sq_div_succ_sq`: `∏_{k ≥ 1} (1 + y²/k²) = sinh(πy)/(πy)` for
  `y ≠ 0`.

## Implementation notes

The partial products of 5.8.3 are exactly `|GammaSeq x n / GammaSeq (x + iy) n|²`, so the
product follows from Euler's limit `Complex.GammaSeq_tendsto_Gamma`. The values on vertical
lines come from the reflection formula `Complex.Gamma_mul_Gamma_one_sub` and
`Γ(conj z) = conj Γ(z)`.

The proofs of DLMF 5.8.3 and 5.4.3 are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), files `DLMF/Gamma/Products.lean` and
`DLMF/Gamma/SpecialValues.lean`.
-/

public section

open Filter Finset

open scoped Topology Real ComplexConjugate

noncomputable section

namespace TauCeti

open Complex

/-- The partial products of DLMF 5.8.3 are the squared moduli of quotients of Gauss sequences:
`|GammaSeq x n / GammaSeq (x + iy) n|² = ∏_{k ≤ n} (1 + y²/(x + k)²)` for `n > 0`. -/
theorem norm_GammaSeq_div_GammaSeq_add_mul_I_sq {x : ℝ} (hx : ∀ n : ℕ, x ≠ -(n : ℝ)) (y : ℝ)
    {n : ℕ} (hn : 0 < n) :
    ‖GammaSeq x n / GammaSeq (x + y * I) n‖ ^ 2 =
      ∏ k ∈ range (n + 1), (1 + y ^ 2 / (x + k) ^ 2) := by
  have hxk' : ∀ k : ℕ, (x + k : ℝ) ≠ 0 := fun k h => hx k (eq_neg_of_add_eq_zero_left h)
  have hxk : ∀ k : ℕ, (x : ℂ) + k ≠ 0 := fun k h => hxk' k (by exact_mod_cast h)
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hP1 : ∏ j ∈ range (n + 1), ((x : ℂ) + j) ≠ 0 :=
    prod_ne_zero_iff.mpr fun j _ => hxk j
  have hP2 : ∏ j ∈ range (n + 1), ((x : ℂ) + y * I + j) ≠ 0 :=
    prod_ne_zero_iff.mpr fun j _ h =>
      ofReal_add_mul_I_ne_neg_natCast hx y j (eq_neg_of_add_eq_zero_left h)
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
    rw [← ofReal_natCast, ← ofReal_add, norm_real, Real.norm_eq_abs, sq_abs]
  rw [h1, h2]
  have := hxk' j
  field_simp

/-- **DLMF 5.8.3.** For real `x` that is not a nonpositive integer and real `y`, the product
`∏_{k ≥ 0} (1 + y²/(x + k)²)` converges to `Γ(x)² / |Γ(x + iy)|²`. -/
theorem hasProd_Gamma_norm_quotient {x : ℝ} (hx : ∀ n : ℕ, x ≠ -(n : ℝ)) (y : ℝ) :
    HasProd (fun k : ℕ => 1 + y ^ 2 / (x + k) ^ 2)
      (Real.Gamma x ^ 2 / ‖Gamma ((x : ℂ) + y * I)‖ ^ 2) := by
  -- `∑ y²/(x + k)²` converges by the shifted `p`-series test with `p = 2`.
  have hsum : Summable fun k : ℕ => y ^ 2 / (x + k) ^ 2 :=
    (((Real.summable_one_div_nat_add_rpow x 2).2 one_lt_two).mul_left (y ^ 2)).congr fun k => by
      rw [Real.rpow_two, sq_abs, add_comm, mul_one_div]
  have hmul := Real.multipliable_one_add_of_summable hsum
  -- Both sides are limits of the same Gauss sequences.
  have hlim : Tendsto (fun n : ℕ => ‖GammaSeq x n / GammaSeq (x + y * I) n‖ ^ 2)
      atTop (𝓝 (‖Gamma x / Gamma (x + y * I)‖ ^ 2)) :=
    (((GammaSeq_tendsto_Gamma _).div (GammaSeq_tendsto_Gamma _)
      (Gamma_ne_zero (ofReal_add_mul_I_ne_neg_natCast hx y))).norm).pow 2
  have hP := (hmul.hasProd.tendsto_prod_nat.comp (tendsto_add_atTop_nat 1)).congr'
    ((eventually_gt_atTop 0).mono fun n hn =>
      (norm_GammaSeq_div_GammaSeq_add_mul_I_sq hx y hn).symm)
  have h := tendsto_nhds_unique hlim hP
  rw [Gamma_ofReal, norm_div, norm_real, Real.norm_eq_abs, div_pow, sq_abs] at h
  rw [h]
  exact hmul.hasProd

/-- The modulus of `Γ` on a horizontal line, compared at two real parts: for `0 < x ≤ x′`,
`|Γ(x + iy)| ≤ Γ(x)/Γ(x′) · |Γ(x′ + iy)|`. This is the termwise comparison of the products in
DLMF 5.8.3. -/
theorem norm_Gamma_add_mul_I_le {x x' : ℝ} (hx : 0 < x) (hxx' : x ≤ x') (y : ℝ) :
    ‖Gamma ((x : ℂ) + y * I)‖ ≤ Real.Gamma x / Real.Gamma x' * ‖Gamma ((x' : ℂ) + y * I)‖ := by
  have hx' : 0 < x' := hx.trans_le hxx'
  have hnot : ∀ {u : ℝ}, 0 < u → ∀ n : ℕ, u ≠ -(n : ℝ) := fun hu n h => by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hne : ∀ {u : ℝ}, 0 < u → Gamma ((u : ℂ) + y * I) ≠ 0 := fun hu =>
    Gamma_ne_zero (ofReal_add_mul_I_ne_neg_natCast (hnot hu) y)
  have hG' := Real.Gamma_pos_of_pos hx'
  have hN := norm_pos_iff.mpr (hne hx)
  have hN' := norm_pos_iff.mpr (hne hx')
  -- the termwise comparison of the two products
  have hle : Real.Gamma x' ^ 2 / ‖Gamma ((x' : ℂ) + y * I)‖ ^ 2 ≤
      Real.Gamma x ^ 2 / ‖Gamma ((x : ℂ) + y * I)‖ ^ 2 := by
    refine le_of_tendsto_of_tendsto' (hasProd_Gamma_norm_quotient (hnot hx') y)
      (hasProd_Gamma_norm_quotient (hnot hx) y) fun s => ?_
    refine prod_le_prod₀ (fun k _ => by positivity) fun k _ => ?_
    have h1 : (x + k) ^ 2 ≤ (x' + k) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
    gcongr
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at hle
  have hsq : (‖Gamma ((x : ℂ) + y * I)‖ * Real.Gamma x') ^ 2 ≤
      (Real.Gamma x * ‖Gamma ((x' : ℂ) + y * I)‖) ^ 2 := by
    nlinarith
  have := (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  rw [div_mul_eq_mul_div, le_div_iff₀ hG']
  exact this

/-- **DLMF 5.4.3.** `|Γ(iy)|² = π / (y sinh(πy))` for real `y`. At `y = 0` both sides are `0`,
since `Γ(0) = 0` and division by zero is `0`. -/
theorem _root_.Real.norm_Gamma_mul_I_sq (y : ℝ) :
    ‖Complex.Gamma (y * I)‖ ^ 2 = π / (y * Real.sinh (π * y)) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
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
    rw [show (π : ℂ) * (y * I) = ((π * y : ℝ) : ℂ) * I by push_cast; ring, sin_mul_I,
      ← ofReal_sinh, mul_comm]
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
  rw [add_comm, Gamma_add_one _ (mul_ne_zero hy' I_ne_zero), norm_mul, mul_pow,
    Real.norm_Gamma_mul_I_sq y, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, sq_abs]
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

end TauCeti
