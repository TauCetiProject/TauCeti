/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The choice of parameters in the proof of Roth's theorem

The proof of Roth's theorem evaluates an auxiliary polynomial at good rational approximations
`β₀, …, β_{n-1}` of an algebraic number whose logarithmic heights `h k = h(β_k)` grow quickly:
`L ≤ h 0` and `M * h k ≤ h (k + 1)`. For a real number `D` with `5 * h k ≤ D`, the partial
degrees of the auxiliary polynomial are bounded by `r k = ⌊D / h k⌋₊`. Such sequences of
approximations exist by `Northcott.exists_seq_mem_lt`.

This file proves the elementary inequalities between these parameters which put the auxiliary
polynomial in the range of Roth's index estimate. They are stated for an arbitrary real sequence
`h`, which in the application is the sequence of heights of the approximations.

## Main results

* `TauCeti.sum_range_floor_div_le_two_mul_div`: if `M ≥ 2`, then `∑_{k < n} r k ≤ 2 D / L`.
* `TauCeti.floor_div_le_mul_floor_div`: if `σ M ≥ 2`, then `r (k + 1) ≤ σ r k`.
* `TauCeti.inv_mul_add_le_floor_div_mul`: if `L ≥ σ⁻¹ (5 C₁ / 2 + 5 n)` and a height `H` is
  at most `C₁ ∑_{j < n} r j`, then `σ⁻¹ (H + 4 n r 0) ≤ r k h k`.

The degree bounds are positive, `1 ≤ r k`, by `Nat.one_le_floor_iff` and `one_le_div`.

## References

* L. Pottmeyer, [*Diophantine Approximation*](https://esaga.uni-due.de/f/lukas.pottmeyer/DioApp.pdf)
  (2022), §3.5.2.
-/

public section

namespace TauCeti

open Finset

/-- If a sequence starts at `h 0 ≥ L > 0` and grows by a factor `M ≥ 2` at each of its first `n`
terms, then the sum of `⌊D / h k⌋₊` over these terms is at most `2 D / L`. -/
theorem sum_range_floor_div_le_two_mul_div {n : ℕ} {h : ℕ → ℝ} {D L M : ℝ} (hD : 0 ≤ D)
    (hL : 0 < L) (hM : 2 ≤ M) (h₀ : L ≤ h 0) (hh : ∀ k, k + 1 < n → M * h k ≤ h (k + 1)) :
    ∑ k ∈ range n, (⌊D / h k⌋₊ : ℝ) ≤ 2 * D / L := by
  have hk : ∀ k < n, 2 ^ k * L ≤ h k := fun k hk ↦ calc
    2 ^ k * L ≤ M ^ k * h 0 :=
      mul_le_mul (pow_le_pow_left₀ zero_le_two hM k) h₀ hL.le (pow_nonneg (by linarith) k)
    _ ≤ h k := geom_le (by linarith) k fun j hj ↦ hh j (by omega)
  calc ∑ k ∈ range n, (⌊D / h k⌋₊ : ℝ)
      ≤ ∑ k ∈ range n, D / L * (1 / 2) ^ k := by
        refine sum_le_sum fun k hkn ↦ ?_
        have h2k := hk k (mem_range.mp hkn)
        have hpos : 0 < 2 ^ k * L := by positivity
        calc (⌊D / h k⌋₊ : ℝ) ≤ D / h k := Nat.floor_le (div_nonneg hD (hpos.trans_le h2k).le)
          _ ≤ D / (2 ^ k * L) := div_le_div_of_nonneg_left hD hpos h2k
          _ = D / L * (1 / 2) ^ k := by rw [div_pow, one_pow]; field_simp
    _ = D / L * ∑ k ∈ range n, (1 / 2 : ℝ) ^ k := by rw [mul_sum]
    _ ≤ D / L * 2 := by gcongr; exact sum_geometric_two_le n
    _ = 2 * D / L := by ring

/-- If `y ≥ M x > 0`, `D ≥ 2 x` and `σ M ≥ 2`, then `⌊D / y⌋₊ ≤ σ ⌊D / x⌋₊`. Applied to
consecutive terms of a quickly growing sequence, this makes consecutive degree bounds decrease
by the factor `σ`. -/
theorem floor_div_le_mul_floor_div {x y D M σ : ℝ} (hσ : 0 < σ) (hσM : 2 ≤ σ * M) (hx : 0 < x)
    (hxy : M * x ≤ y) (hD : 2 * x ≤ D) : (⌊D / y⌋₊ : ℝ) ≤ σ * ⌊D / x⌋₊ := by
  have hM : 0 < M := pos_of_mul_pos_right (by linarith) hσ.le
  have hMx : 0 < M * x := mul_pos hM hx
  have hD₀ : 0 ≤ D := by linarith
  have hDx : 2 ≤ D / x := by rwa [le_div_iff₀ hx]
  calc (⌊D / y⌋₊ : ℝ) ≤ D / y := Nat.floor_le (div_nonneg hD₀ (hMx.trans_le hxy).le)
    _ ≤ D / (M * x) := div_le_div_of_nonneg_left hD₀ hMx hxy
    _ = (σ * M)⁻¹ * σ * (D / x) := by field_simp
    _ ≤ 2⁻¹ * σ * (D / x) := by gcongr
    _ ≤ σ * (D / x - 1) := by nlinarith
    _ ≤ σ * ⌊D / x⌋₊ := by
        gcongr
        linarith [Nat.lt_floor_add_one (D / x)]

/-- The height condition of Roth's index estimate for the degree bounds `r j = ⌊D / h j⌋₊`.
Let `h` start at `h 0 ≥ L ≥ σ⁻¹ (5 C₁ / 2 + 5 n)` and grow by a factor `M ≥ 2` along its first
`n` terms. If `5 h k ≤ D` and `H ≤ C₁ ∑_{j < n} r j`, then `σ⁻¹ (H + 4 n r 0) ≤ r k h k`. -/
theorem inv_mul_add_le_floor_div_mul {n k : ℕ} {h : ℕ → ℝ} {D L M σ C₁ H : ℝ} (hσ : 0 < σ)
    (hL : 0 < L) (hM : 2 ≤ M) (h₀ : L ≤ h 0) (hh : ∀ j, j + 1 < n → M * h j ≤ h (j + 1))
    (hC₁ : 0 ≤ C₁) (hLC : σ⁻¹ * (5 * C₁ / 2 + 5 * n) ≤ L) (hk : 0 < h k) (hD : 5 * h k ≤ D)
    (hH : H ≤ C₁ * ∑ j ∈ range n, (⌊D / h j⌋₊ : ℝ)) :
    σ⁻¹ * (H + 4 * n * ⌊D / h 0⌋₊) ≤ ⌊D / h k⌋₊ * h k := by
  have hD₀ : 0 ≤ D := by linarith
  have hsum := sum_range_floor_div_le_two_mul_div hD₀ hL hM h₀ hh
  have hr₀ : (⌊D / h 0⌋₊ : ℝ) ≤ D / L :=
    (Nat.floor_le (div_nonneg hD₀ (hL.trans_le h₀).le)).trans
      (div_le_div_of_nonneg_left hD₀ hL h₀)
  have hrk : D - h k ≤ ⌊D / h k⌋₊ * h k := by
    have hlt := Nat.lt_floor_add_one (D / h k)
    have hmul : D / h k * h k = D := div_mul_cancel₀ D hk.ne'
    nlinarith
  have hσL : 5 * C₁ / 2 + 5 * n ≤ σ * L := by rwa [inv_mul_le_iff₀ hσ] at hLC
  have hDL : 0 ≤ D / L := div_nonneg hD₀ hL.le
  rw [inv_mul_le_iff₀ hσ]
  calc H + 4 * n * ⌊D / h 0⌋₊ ≤ C₁ * (2 * D / L) + 4 * n * (D / L) := by
        gcongr
        exact hH.trans (mul_le_mul_of_nonneg_left hsum hC₁)
    _ = 4 / 5 * (5 * C₁ / 2 + 5 * n) * (D / L) := by ring
    _ ≤ 4 / 5 * (σ * L) * (D / L) := by gcongr
    _ = σ * (4 / 5 * D) := by field_simp
    _ ≤ σ * (⌊D / h k⌋₊ * h k) := mul_le_mul_of_nonneg_left (by linarith) hσ.le

end TauCeti
