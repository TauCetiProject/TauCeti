/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Charpoly.FinrankTwo
public import TauCeti.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import TauCeti.NumberTheory.ModularForms.LevelOne.Eigenbasis
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.EichlerSelberg

/-!
# Values of the Eichler–Selberg trace formula at level one

The Eichler–Selberg trace formula
`TauCeti.trace_heckeTCuspLevelOne_eq_neg_hurwitzClassNumber_sub_min` computes the trace of `Tₙ` on
`S_k(SL(2, ℤ))` from finitely many Hurwitz class numbers `H(4n - t²)` and Dickson values
`P_k(t, n)`. This file evaluates it in the first cases, as checks of the formula against
independently known data, and uses it to compute a characteristic polynomial.

* For `n = 1` the formula gives the dimension of `S_k(SL(2, ℤ))`, since `T₁ = 1`
  (`TauCeti.heckeTCuspLevelOne_one`). The class-number side is evaluated here in closed form, from
  `H(0) = -1/12`, `H(3) = 1/3`, `H(4) = 1/2` and the periodicity of `P_k(t, 1)` in `k`, and it
  agrees with the dimension formula `CuspForm.dimension_level_one`, which comes from Mathlib's
  `ModularForm.dimension_level_one` and not from the trace formula.
* On `S₁₂(SL(2, ℤ)) = ℂ Δ` the trace of `T₂` is `-24`, the eigenvalue `τ(2)` of `T₂` on `Δ` found
  from the `q`-expansion of `Δ` in `TauCeti.heckeTCuspNat_discriminant_two`.
* On the two-dimensional space `S₂₄(SL(2, ℤ))` the traces of `T₂` and `T₄ = T₂² - 2²³` are
  `1080` and `25326656`. The trace of `T₂` and that of its square determine its characteristic
  polynomial in dimension two (`LinearMap.charpoly_of_finrank_eq_two`,
  `LinearMap.trace_mul_self_of_finrank_eq_two`), which is `X² - 1080 X - 20468736`.

## Main results

* `TauCeti.neg_sum_hurwitzClassNumber_mul_dickson_one_sub_half`: the class-number side of the trace
  formula at `n = 1` is `⌊k / 12⌋ - 1` if `k ≡ 2 (mod 12)` and `⌊k / 12⌋` otherwise.
* `TauCeti.trace_heckeTCuspLevelOne_twelve_two`: `tr(T₂ | S₁₂) = -24`.
* `TauCeti.trace_heckeTCuspLevelOne_twentyFour_two`: `tr(T₂ | S₂₄) = 1080`.
* `TauCeti.trace_heckeTCuspLevelOne_twentyFour_four`: `tr(T₄ | S₂₄) = 25326656`.
* `TauCeti.charpoly_heckeTCuspLevelOne_twentyFour_two`: the characteristic polynomial of `T₂` on
  `S₂₄(SL(2, ℤ))` is `X² - 1080 X - 20468736`.

## References

* D. Zagier, *The Eichler–Selberg trace formula on SL₂(ℤ)*, appendix to S. Lang,
  *Introduction to Modular Forms*, Springer, 1976.
* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327.
-/

public section

open Module Polynomial
open scoped MatrixGroups

namespace TauCeti

/-! ### The dimension check at `n = 1` -/

/-- **The class-number side of the trace formula at `n = 1`**: for even `w ≥ 2` and `k = w + 2`,

`-½ ∑_{t² ≤ 4} H(4 - t²) P_k(t, 1) - ½ = ⌊k / 12⌋ - [k ≡ 2 (mod 12)]`.

The terms `t = ±2`, `±1` and `0` contribute `H(0) = -1/12` times `P_k(±2, 1) = k - 1`, `H(3) = 1/3`
times `P_k(±1, 1)`, which has period `6` in `w`, and `H(4) = 1/2` times `P_k(0, 1) = (-1)^(w/2)`.
The right side is `dim S_k(SL(2, ℤ))` (`CuspForm.dimension_level_one`), so this is the trace formula
for `T₁ = 1`, verified against the level-one dimension formula. -/
theorem neg_sum_hurwitzClassNumber_mul_dickson_one_sub_half {w : ℕ} (hw : Even w) (hw₀ : w ≠ 0) :
    -(∑ t ∈ (Finset.Icc (-4 : ℤ) 4).filter (fun t ↦ t ^ 2 ≤ 4),
        (hurwitzClassNumber (4 - t ^ 2).toNat : ℂ) * (dickson 2 (1 : ℂ) w).eval (t : ℂ)) / 2 -
      1 / 2 =
      ((if w + 2 ≡ 2 [MOD 12] then (w + 2) / 12 - 1 else (w + 2) / 12 : ℕ) : ℂ) := by
  -- `P_k(±2, 1) = k - 1`
  have h₂ : (dickson 2 (1 : ℂ) w).eval 2 = w + 1 := by
    simpa using dickson_two_sq_eval_two_mul (1 : ℂ) w
  -- write `w = 12 q + 2 m` with `m < 6`; the dimension is `q - 1`, `q` or `q + 1` according to `m`
  obtain ⟨q, m, hm, rfl⟩ : ∃ q m, m < 6 ∧ w = 12 * q + 2 * m :=
    ⟨w / 12, w % 12 / 2, by omega, by obtain ⟨j, rfl⟩ := hw; omega⟩
  generalize hR : (if 12 * q + 2 * m + 2 ≡ 2 [MOD 12] then (12 * q + 2 * m + 2) / 12 - 1
    else (12 * q + 2 * m + 2) / 12) = R
  have hR' : R + (if m = 0 then 1 else 0) = q + (if m = 5 then 1 else 0) := by
    have hc : 12 * q + 2 * m + 2 ≡ 2 [MOD 12] ↔ m = 0 := by simp only [Nat.ModEq]; omega
    rw [← hR, if_congr hc rfl rfl]
    split_ifs <;> omega
  -- the weights at `t = 1` and `t = 0` have periods `6` and `4` in `w`
  have h₁ : (dickson 2 (1 : ℂ) (12 * q + 2 * m)).eval 1 = (dickson 2 (1 : ℂ) (2 * m)).eval 1 := by
    rw [show 12 * q + 2 * m = 6 * (2 * q) + 2 * m by ring, dickson_two_one_eval_one_six_mul_add]
  have h₀ : (dickson 2 (1 : ℂ) (12 * q + 2 * m)).eval 0 = (-1) ^ m := by
    rw [show 12 * q + 2 * m = 2 * (6 * q + m) by ring, dickson_two_eval_zero_two_mul, pow_add,
      pow_mul]
    norm_num
  rw [show (Finset.Icc (-4 : ℤ) 4).filter (fun t ↦ t ^ 2 ≤ 4) = {-2, -1, 0, 1, 2} by decide]
  simp +decide only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton]
  norm_num [dickson_eval_neg_of_even _ _ _ hw, h₂, h₁, h₀]
  -- the remaining weights `P_{2m+2}(1, 1)` for `m < 6`
  interval_cases m <;>
  · have h := congrArg (Nat.cast (R := ℂ)) hR'
    push_cast at h
    norm_num [dickson_add_two]
    linear_combination -h

/-! ### The trace of `T₂` on `S₁₂` -/

/-- **The trace of `T₂` on `S₁₂(SL(2, ℤ))` is `-24`**, by the Eichler–Selberg trace formula:
`-½ (H(8) P₁₂(0, 2) + 2 H(7) P₁₂(1, 2) + 2 H(4) P₁₂(2, 2)) - 1 = -½ (-32 + 46 + 32) - 1`. Since
`S₁₂(SL(2, ℤ)) = ℂ Δ`, this is the eigenvalue `τ(2) = -24` of `T₂` on `Δ`. -/
theorem trace_heckeTCuspLevelOne_twelve_two :
    LinearMap.trace ℂ _ (heckeTCuspLevelOne 12 2) = -24 := by
  rw [trace_heckeTCuspLevelOne_eq_neg_hurwitzClassNumber_sub_min (w := 10) (by norm_num)
      (by decide) (by decide) 2,
    show (Finset.Icc (-4 * ((2 : ℕ) : ℤ)) (4 * (2 : ℕ))).filter
      (fun t ↦ t ^ 2 ≤ 4 * ((2 : ℕ) : ℤ)) = {-2, -1, 0, 1, 2} by decide,
    show Nat.divisorsAntidiagonal 2 = {(1, 2), (2, 1)} by decide]
  simp +decide only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton]
  simp only [dickson_add_two, dickson_one, dickson_zero, eval_sub, eval_mul, eval_X, eval_C]
  norm_num

/-! ### The characteristic polynomial of `T₂` on `S₂₄` -/

/-- **The trace of `T₂` on `S₂₄(SL(2, ℤ))` is `1080`**, by the Eichler–Selberg trace formula. -/
theorem trace_heckeTCuspLevelOne_twentyFour_two :
    LinearMap.trace ℂ _ (heckeTCuspLevelOne 24 2) = 1080 := by
  rw [trace_heckeTCuspLevelOne_eq_neg_hurwitzClassNumber_sub_min (w := 22) (by norm_num)
      (by decide) (by decide) 2,
    show (Finset.Icc (-4 * ((2 : ℕ) : ℤ)) (4 * (2 : ℕ))).filter
      (fun t ↦ t ^ 2 ≤ 4 * ((2 : ℕ) : ℤ)) = {-2, -1, 0, 1, 2} by decide,
    show Nat.divisorsAntidiagonal 2 = {(1, 2), (2, 1)} by decide]
  simp +decide only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton]
  simp only [dickson_add_two, dickson_one, dickson_zero, eval_sub, eval_mul, eval_X, eval_C]
  norm_num

/-- **The trace of `T₄` on `S₂₄(SL(2, ℤ))` is `25326656`**, by the Eichler–Selberg trace formula. -/
theorem trace_heckeTCuspLevelOne_twentyFour_four :
    LinearMap.trace ℂ _ (heckeTCuspLevelOne 24 4) = 25326656 := by
  rw [trace_heckeTCuspLevelOne_eq_neg_hurwitzClassNumber_sub_min (w := 22) (by norm_num)
      (by decide) (by decide) 4,
    show (Finset.Icc (-4 * ((4 : ℕ) : ℤ)) (4 * (4 : ℕ))).filter
      (fun t ↦ t ^ 2 ≤ 4 * ((4 : ℕ) : ℤ)) = {-4, -3, -2, -1, 0, 1, 2, 3, 4} by decide,
    show Nat.divisorsAntidiagonal 4 = {(1, 4), (2, 2), (4, 1)} by decide]
  simp +decide only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton]
  simp only [dickson_add_two, dickson_one, dickson_zero, eval_sub, eval_mul, eval_X, eval_C]
  norm_num

/-- **The characteristic polynomial of `T₂` on `S₂₄(SL(2, ℤ))` is `X² - 1080 X - 20468736`.**

The space is two-dimensional (`CuspForm.dimension_level_one`), so the characteristic polynomial
is `X² - tr(T₂) X + det(T₂)` with `2 det(T₂) = tr(T₂)² - tr(T₂²)`. By the recurrence
`T₄ = T₂² - 2²³ T₁` and `T₁ = 1`, `tr(T₂²) = tr(T₄) + 2²⁴`, and both traces come from the trace
formula. -/
theorem charpoly_heckeTCuspLevelOne_twentyFour_two :
    (heckeTCuspLevelOne 24 2).charpoly = X ^ 2 - C 1080 * X - C 20468736 := by
  have hdim : finrank ℂ (CuspForm 𝒮ℒ 24) = 2 := by
    simpa [Nat.ModEq] using CuspForm.dimension_level_one 24 (by decide)
  -- `T₂² = T₄ + 2²³`
  have hsq : heckeTCuspLevelOne 24 2 * heckeTCuspLevelOne 24 2 =
      heckeTCuspLevelOne 24 4 + (2 : ℂ) ^ (23 : ℕ) • 1 := by
    have := heckeTCuspLevelOne_prime_pow_add_two 24 2 0
    norm_num at this
    rw [this]
    norm_num
  have htr := LinearMap.trace_mul_self_of_finrank_eq_two hdim (heckeTCuspLevelOne 24 2)
  rw [hsq, map_add, map_smul, LinearMap.trace_one, hdim, trace_heckeTCuspLevelOne_twentyFour_four,
    trace_heckeTCuspLevelOne_twentyFour_two] at htr
  have hdet : LinearMap.det (heckeTCuspLevelOne 24 2) = -20468736 := by
    norm_num at htr
    linear_combination htr / 2
  rw [LinearMap.charpoly_of_finrank_eq_two hdim, trace_heckeTCuspLevelOne_twentyFour_two, hdet,
    C_neg, ← sub_eq_add_neg]

end TauCeti
