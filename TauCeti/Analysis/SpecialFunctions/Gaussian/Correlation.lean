/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import TauCeti.Analysis.SpecialFunctions.Gaussian.PowerDecay

/-!
# Uniform majorants for Gaussian-weighted correlations

A correlation bound can be constant on an exceptional set of positive integer pairs and grow
like a square root times a logarithm off that set. The Gaussian weights give a single summable
majorant, uniform when the scale is at least the inverse square root of the averaging length.
The only extra summability required is that of the power weight on the exceptional set.
For quadratic twists of theta sums, the exceptional pairs are those whose product has square
odd part.

This is the Gaussian-weight estimate used in `New.sum_sq_thetaSeries_jacobiSym_le` in the
shorter GRH formalization (lsernau/grh-lean, commit `72fead1`,
`grh/src/Lib/Analytic/QuadraticTwist.lean`).
-/

public section

open Real

namespace TauCeti

/-- Off the exceptional set, the stronger Gaussian power bound absorbs the correlation
weight and leaves two inverse powers of the scale. -/
private theorem gaussianPair_mul_correlation_le {δ E T u : ℝ} {j : ℕ}
    (hδ : 0 < δ)
    (h : ∀ x : ℝ, 0 < x → x ^ j * exp (-π * x ^ 2) ≤ E * x ^ (-(3 / 2 + δ)))
    (hT : 0 < T) (hTu : T⁻¹ ≤ u) (p : ℕ+ × ℕ+) :
    let m : ℝ := p.1
    let n : ℝ := p.2
    u * (((m * u) ^ j * exp (-π * (m * u) ^ 2)) * ((n * u) ^ j * exp (-π * (n * u) ^ 2))) *
        (2 * sqrt (m * n) * (1 + log (m * n))) ≤
      (E ^ 2 * (2 * (1 + (δ / 2)⁻¹))) * (m * n) ^ (-1 - δ / 2) * T ^ 2 * u ^ (-2 * δ) := by
  let m : ℝ := p.1
  let n : ℝ := p.2
  have hm : 0 < m := by dsimp [m]; positivity
  have hn : 0 < n := by dsimp [n]; positivity
  have hx : 1 ≤ m * n := one_le_mul_of_one_le_of_one_le
    (by dsimp [m]; exact_mod_cast (one_le (a := p.1)))
    (by dsimp [n]; exact_mod_cast (one_le (a := p.2)))
  have hu : 0 < u := (inv_pos.mpr hT).trans_le hTu
  have hinv : u⁻¹ ≤ T := (inv_le_comm₀ hu hT).mpr hTu
  have hu₂ : u ^ (-2 : ℝ) ≤ T ^ 2 := by
    rw [rpow_neg_eq_inv_rpow, rpow_two]
    gcongr
  have hx₀ := zero_lt_one.trans_le hx
  have hlog := log_nonneg hx
  -- Spend half the available exponent saving absorbing the logarithm.
  have hcorr : 2 * sqrt (m * n) * (1 + log (m * n)) ≤
      2 * (1 + (δ / 2)⁻¹) * (m * n) ^ (1 / 2 + δ / 2) := by
    have hpow : 1 ≤ (m * n) ^ (δ / 2) := one_le_rpow hx (half_pos hδ).le
    have hlog' := log_le_rpow_div hx₀.le (half_pos hδ)
    rw [sqrt_eq_rpow, rpow_add hx₀]
    calc
      _ ≤ 2 * (m * n) ^ (1 / 2 : ℝ) * ((m * n) ^ (δ / 2) + (m * n) ^ (δ / 2) / (δ / 2)) := by
        gcongr
      _ = _ := by rw [div_eq_mul_inv]; ring
  calc
    _ ≤ (E ^ 2 * (m * n) ^ (-(3 / 2 + δ)) * u ^ (1 - 2 * (3 / 2 + δ))) *
        (2 * (1 + (δ / 2)⁻¹) * (m * n) ^ (1 / 2 + δ / 2)) :=
      mul_le_mul (mul_gaussian_pair_le h hu.le hm hn) hcorr (by positivity) (by positivity)
    _ = (E ^ 2 * (2 * (1 + (δ / 2)⁻¹))) * (m * n) ^ (-1 - δ / 2) *
        u ^ (-2 : ℝ) * u ^ (-2 * δ) := by
      have hprod : (m * n) ^ (-1 - δ / 2) = (m * n) ^ (-(3 / 2 + δ)) *
          (m * n) ^ (1 / 2 + δ / 2) := by
        rw [← rpow_add (mul_pos hm hn)]
        congr 1
        ring
      rw [(by ring : 1 - 2 * (3 / 2 + δ) = -2 + (-2 * δ)), rpow_add hu, hprod]
      ring
    _ ≤ _ := by gcongr

/-- A uniform summable majorant for Gaussian-weighted correlations. On the exceptional set `D`
(typically the square pairs) the correlation bound is `X`. Outside `D` it is
`2√(mn)(1 + log(mn))`. With `X ≤ T²` and scale `u ≥ 1/T`, the weighted bound at every pair
is at most a summable coefficient times `T² u⁻²ᵟ`. -/
theorem exists_summable_gaussian_correlation_majorant {j : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (D : Set (ℕ+ × ℕ+)) [DecidablePred (· ∈ D)]
    (hD : Summable fun p : ℕ+ × ℕ+ ↦ if p ∈ D then
      ((p.1 : ℝ) * (p.2 : ℝ)) ^ (-(1 / 2 + δ)) else 0) :
    ∃ A : ℕ+ × ℕ+ → ℝ, Summable A ∧ (∀ p, 0 ≤ A p) ∧
      ∀ {T u X : ℝ}, 0 < T → T⁻¹ ≤ u → X ≤ T ^ 2 → ∀ p : ℕ+ × ℕ+,
        let m : ℝ := p.1
        let n : ℝ := p.2
        u * (((m * u) ^ j * exp (-π * (m * u) ^ 2)) *
          ((n * u) ^ j * exp (-π * (n * u) ^ 2))) *
          (if p ∈ D then X else 2 * sqrt (m * n) * (1 + log (m * n))) ≤
            A p * T ^ 2 * u ^ (-2 * δ) := by
  let a : ℝ := 1 / 2 + δ
  obtain ⟨C, -, hsmall⟩ := exists_rpow_mul_exp_neg_mul_sq_le_mul_rpow (a := (j : ℝ))
    (b := -a) (by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) j]) pi_pos
  obtain ⟨E, -, hlarge⟩ := exists_rpow_mul_exp_neg_mul_sq_le_mul_rpow (a := (j : ℝ))
    (b := -(3 / 2 + δ)) (by linarith [Nat.cast_nonneg (α := ℝ) j]) pi_pos
  simp only [rpow_natCast] at hsmall hlarge
  let W (p : ℕ+ × ℕ+) : ℝ := ((p.1 : ℝ) * (p.2 : ℝ)) ^ (-1 - δ / 2)
  let B := E ^ 2 * (2 * (1 + (δ / 2)⁻¹))
  have hW : Summable W := by
    have h := summable_pnat_iff_summable_nat.mpr (summable_nat_rpow.mpr
      (by linarith : -1 - δ / 2 < -1))
    exact (h.mul_of_nonneg h (fun _ ↦ by positivity) (fun _ ↦ by positivity)).congr fun p ↦
      (mul_rpow (by positivity) (by positivity)).symm
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hW₀ (p) : 0 ≤ W p := by dsimp [W]; positivity
  refine ⟨fun p ↦ C ^ 2 * (if p ∈ D then ((p.1 : ℝ) * (p.2 : ℝ)) ^ (-a) else 0) + B * W p,
    (hD.mul_left _).add (hW.mul_left _), fun p ↦ ?_, ?_⟩
  · dsimp only
    have := hW₀ p
    split_ifs <;> positivity
  intro T u X hT hTu hX p
  dsimp only
  have hu : 0 < u := (inv_pos.mpr hT).trans_le hTu
  have hm : (0 : ℝ) < p.1 := by positivity
  have hn : (0 : ℝ) < p.2 := by positivity
  rcases em (p ∈ D) with hp | hp
  · simp only [ite_eq_left hp]
    calc
      _ ≤ u * (((p.1 * u) ^ j * exp (-π * (p.1 * u) ^ 2)) *
          ((p.2 * u) ^ j * exp (-π * (p.2 * u) ^ 2))) * T ^ 2 := by gcongr
      _ ≤ (C ^ 2 * ((p.1 : ℝ) * p.2) ^ (-a) * u ^ (1 - 2 * a)) * T ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_gaussian_pair_le hsmall hu.le hm hn) (sq_nonneg T)
      _ ≤ _ := by
        rw [(by dsimp [a]; ring : 1 - 2 * a = -2 * δ), mul_right_comm]
        gcongr
        exact le_add_of_nonneg_right (mul_nonneg hB (hW₀ p))
  · simp only [ite_eq_right hp, mul_zero, zero_add, B, W]
    exact gaussianPair_mul_correlation_le hδ hlarge hT hTu p

end TauCeti
