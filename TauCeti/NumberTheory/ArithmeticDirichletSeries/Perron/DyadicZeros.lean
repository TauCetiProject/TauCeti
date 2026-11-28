/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.GeomSum
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# The zero-side error on dyadic Perron blocks

When the real parts of the nonexceptional zeros are bounded by `σ ≥ 1/2`, their
half-interval Perron terms have a total bound proportional to `X ^ σ`. Summing the
geometric decay in the block endpoints avoids a factor of `log X` in the error of
the character prime number theorem (Iwaniec–Kowalski, *Analytic Number Theory*,
Theorem 5.27). The input is the capped reciprocal weight of the zeros, not a
bound for the sum of `1 / ‖ρ‖`, which could be large near the origin.
-/

public section

open Finset

namespace TauCeti

private theorem sum_norm_half_perron_zero_terms_le (S : Finset ℂ) (m : ℂ → ℕ) {k σ : ℝ}
    (hk : 1 ≤ k) (hstrip : ∀ ρ ∈ S, 0 ≤ ρ.re ∧ ρ.re ≤ σ) :
    (∑ ρ ∈ S, (m ρ : ℝ) * ‖((k : ℂ) ^ ρ - ((k / 2 : ℝ) : ℂ) ^ ρ) / ρ‖) ≤
      (2 : ℝ) * k ^ σ * ∑ ρ ∈ S, (m ρ : ℝ) * min 1 ‖ρ‖⁻¹ := by
  rw [mul_sum]
  refine sum_le_sum fun ρ hρ ↦ ?_
  obtain ⟨hρ₀, hρσ⟩ := hstrip ρ hρ
  have htwo : ‖(2 : ℂ) ^ (-ρ)‖ ≤ 1 := by
    rw [← Complex.ofReal_ofNat, Complex.norm_cpow_eq_rpow_re_of_pos two_pos]
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by simpa using hρ₀ : (-ρ).re ≤ 0)
  have hdiff : ‖1 - (2 : ℂ) ^ (-ρ)‖ ≤ min (2 * ‖ρ‖) 2 := by
    refine le_min ?_ ((norm_sub_le _ _).trans (by rw [norm_one]; linarith))
    have h := Complex.norm_ofReal_cpow_sub_ofReal_cpow_le (b := 2) (M := 0)
      (z := -ρ) (w := 0) (by norm_num) (by simpa using hρ₀) (by simp)
    have hlog : Real.log 2 ≤ 2 := by linarith [Real.log_le_sub_one_of_pos two_pos]
    rw [norm_sub_rev]
    exact (by simpa using h : ‖(2 : ℂ) ^ (-ρ) - 1‖ ≤ Real.log 2 * ‖ρ‖).trans
      (mul_le_mul_of_nonneg_right hlog (norm_nonneg _))
  have hk₀ : 0 < k := zero_lt_one.trans_le hk
  -- Factor out the endpoint power before estimating the normalized dyadic difference.
  have hfactor : ((k : ℂ) ^ ρ - ((k / 2 : ℝ) : ℂ) ^ ρ) / ρ =
      (k : ℂ) ^ ρ * ((1 - (2 : ℂ) ^ (-ρ)) / ρ) := by
    rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hk₀.le zero_le_two,
      Complex.ofReal_ofNat, Complex.cpow_neg, div_eq_mul_inv ((k : ℂ) ^ ρ)]
    ring
  rw [hfactor, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hk₀, norm_div]
  have hcap : ‖1 - (2 : ℂ) ^ (-ρ)‖ / ‖ρ‖ ≤ 2 * min 1 ‖ρ‖⁻¹ := by
    by_cases hρz : ρ = 0
    · simp [hρz]
    have hn : 0 < ‖ρ‖ := norm_pos_iff.mpr hρz
    rw [mul_min_of_nonneg _ _ (zero_le_two : (0 : ℝ) ≤ 2), mul_one]
    refine le_min ((div_le_iff₀ hn).2 (hdiff.trans (min_le_left ..))) ?_
    simpa only [div_eq_mul_inv] using
      div_le_div_of_nonneg_right (hdiff.trans (min_le_right ..)) hn.le
  calc
    _ ≤ (m ρ : ℝ) * (k ^ σ * (2 * min 1 ‖ρ‖⁻¹)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.rpow_le_rpow_of_exponent_le hk hρσ) hcap (by positivity)
          (Real.rpow_nonneg hk₀.le _)) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The sum of the absolute magnitudes of the half-interval Perron terms on dyadic blocks is
at most `8 * X ^ σ` times the capped reciprocal weight of the zeros in `S`, counted with
multiplicity. Here `k j` is the upper endpoint of block `j`; it may be rounded down from
`X / 2 ^ j`. To bound only the nonexceptional terms, leave the exceptional zero out of `S`. -/
theorem sum_dyadic_perron_zero_terms_le (S : Finset ℂ) (m : ℂ → ℕ) {σ X : ℝ}
    {J : ℕ} {k : ℕ → ℝ} (hX : 0 ≤ X) (hσ : 1 / 2 ≤ σ)
    (hk : ∀ j ∈ range J, 1 ≤ k j ∧ k j ≤ X / (2 : ℝ) ^ j)
    (hstrip : ∀ ρ ∈ S, 0 ≤ ρ.re ∧ ρ.re ≤ σ) :
    (∑ j ∈ range J, ∑ ρ ∈ S, (m ρ : ℝ) *
      ‖((k j : ℂ) ^ ρ - ((k j / 2 : ℝ) : ℂ) ^ ρ) / ρ‖) ≤
      (8 : ℝ) * X ^ σ * ∑ ρ ∈ S, (m ρ : ℝ) * min 1 ‖ρ‖⁻¹ := by
  have hσpos : 0 < σ := by linarith
  let W := ∑ ρ ∈ S, (m ρ : ℝ) * min 1 ‖ρ‖⁻¹
  have hW : 0 ≤ W := sum_nonneg fun _ _ ↦ by positivity
  have hblock (j : ℕ) (hj : j ∈ range J) :
      (∑ ρ ∈ S, (m ρ : ℝ) * ‖((k j : ℂ) ^ ρ - ((k j / 2 : ℝ) : ℂ) ^ ρ) / ρ‖) ≤
        (2 * X ^ σ * W) * ((2 : ℝ) ^ (-σ)) ^ j := by
    obtain ⟨hj₁, hj₂⟩ := hk j hj
    have hd : 0 < (2 : ℝ) ^ j := by positivity
    calc
      _ ≤ 2 * k j ^ σ * W := sum_norm_half_perron_zero_terms_le S m hj₁ hstrip
      _ ≤ 2 * (X / (2 : ℝ) ^ j) ^ σ * W :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (zero_le_one.trans hj₁) hj₂ hσpos.le) zero_le_two) hW
      _ = _ := by
        rw [Real.div_rpow hX hd.le, ← Real.rpow_natCast_mul zero_le_two,
          ← Real.rpow_mul_natCast zero_le_two, neg_mul, mul_comm σ,
          Real.rpow_neg zero_le_two, div_eq_mul_inv]
        ring
  have hr₀ : 0 ≤ (2 : ℝ) ^ (-σ) := Real.rpow_nonneg zero_le_two _
  have hr : (2 : ℝ) ^ (-σ) ≤ 3 / 4 := by
    refine (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show -σ ≤ -(1 / 2) by linarith)).trans ?_
    rw [Real.rpow_neg zero_le_two, ← Real.sqrt_eq_rpow,
      inv_le_comm₀ (Real.sqrt_pos.2 two_pos) (by norm_num)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hgeom : (∑ j ∈ range J, ((2 : ℝ) ^ (-σ)) ^ j) ≤ 4 := by
    refine (sum_le_sum (fun j _ ↦ pow_le_pow_left₀ hr₀ hr j)).trans ?_
    have hs := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) (x := (3 / 4 : ℝ)) (by norm_num)
      (by norm_num)
    rwa [← range_eq_Ico, show (3 / 4 : ℝ) ^ 0 / (1 - 3 / 4) = 4 by norm_num] at hs
  calc
    _ ≤ ∑ j ∈ range J, (2 * X ^ σ * W) * ((2 : ℝ) ^ (-σ)) ^ j := sum_le_sum hblock
    _ = (2 * X ^ σ * W) * ∑ j ∈ range J, ((2 : ℝ) ^ (-σ)) ^ j := (mul_sum ..).symm
    _ ≤ (2 * X ^ σ * W) * 4 := mul_le_mul_of_nonneg_left hgeom
      (mul_nonneg (mul_nonneg zero_le_two (Real.rpow_nonneg hX _)) hW)
    _ = (8 : ℝ) * X ^ σ * W := by ring

end TauCeti
