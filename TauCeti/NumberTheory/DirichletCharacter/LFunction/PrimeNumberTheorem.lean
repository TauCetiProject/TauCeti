/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.Entire
import TauCeti.Analysis.Calculus.LogDeriv
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds
import TauCeti.NumberTheory.DirichletCharacter.LFunction.LogDeriv.ZeroFreeRegion
import TauCeti.NumberTheory.LSeries.SmoothedSum.ZeroFreeRegion

/-!
# The prime number theorem for a fixed Dirichlet character

The sum of `χ(n) Λ(n)` up to `x` has main term `x` for the principal character and `0`
otherwise. The pole-cleared logarithmic derivative supplies Ingham's transfer theorem with a
width proportional to `log (|Im s| + 3)⁻²⁵`; this yields an error of size
`x exp (-c (log x)^(1/26))`, and in particular saves every fixed power of `log x`.

The logarithmic-derivative input is the fixed-character region of
`grh/src/Lib/Analytic/PrimeNumberTheorem/ZeroFreeRegion.lean` of lsernau/grh-lean at `72fead1`.
The transfer follows the classical zero-free-region route (Ingham, *The Distribution of Prime
Numbers*, Chapter II), as used for `ζ` in
`Chebyshev.exists_abs_psi_sub_le_mul_exp_neg_mul_sqrt_log`.
-/

public section

open Complex Set
open scoped ArithmeticFunction.vonMangoldt

namespace DirichletCharacter

open Classical in
/-- The prime number theorem for a fixed Dirichlet character, with an error of size
`x exp (-c (log x)^(1/26))`. No uniformity in the modulus or character is asserted. -/
theorem exists_norm_sum_mul_vonMangoldt_sub_le {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ x : ℝ, 3 ≤ x →
      ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n * (Λ n : ℂ)) - (if χ = 1 then (x : ℂ) else 0)‖ ≤
        C * x * Real.exp (-c * Real.log x ^ (1 / 26 : ℝ)) := by
  classical
  obtain ⟨a, ha, B, hreg⟩ := χ.exists_entireLFunction_ne_zero_and_norm_logDeriv_le_log_pow
  let η : ℝ → ℝ := fun t ↦ a / Real.log t ^ 25
  have hlog {t : ℝ} (ht : t ∈ Ici (3 : ℝ)) : 0 < Real.log t :=
    Real.log_pos (by linarith [mem_Ici.1 ht])
  have hηc : ContinuousOn η (Ici 3) := continuousOn_const.div
    ((Real.continuousOn_log.mono fun t ht ↦ mem_compl_singleton_iff.2
      (by linarith [mem_Ici.1 ht] : 0 < t).ne').pow 25) fun _ ht ↦ pow_ne_zero _ (hlog ht).ne'
  have hηa : AntitoneOn η (Ici 3) := fun s hs t _ hst ↦
    div_le_div_of_nonneg_left ha.le (pow_pos (hlog hs) _) (pow_le_pow_left₀ (hlog hs).le
      (Real.log_le_log (by linarith [mem_Ici.1 hs]) hst) _)
  have hηlow (t : ℝ) (ht : 3 ≤ t) : a * Real.log t ^ (-(25 : ℝ)) ≤ η t := by
    simp only [η, Real.rpow_neg (hlog ht).le, Real.rpow_ofNat, div_eq_mul_inv, le_refl]
  have hcoeff (n : ℕ) (hn : 1 ≤ n) : ‖χ n * (Λ n : ℂ)‖ ≤ 1 * Real.log (n + 1) := by
    simp only [norm_mul, norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      one_mul]
    exact (mul_le_of_le_one_left ArithmeticFunction.vonMangoldt_nonneg (χ.norm_le_one _)).trans
      (ArithmeticFunction.vonMangoldt_le_log.trans
        (Real.log_le_log (by exact_mod_cast hn) (by linarith)))
  obtain ⟨c, hc, C, hC⟩ := TauCeti.LSeries.norm_sum_sub_mul_le_of_zeroFreeRegion
    hηc hηa ha hηlow hcoeff (U := {s | χ.entireLFunction s ≠ 0}) (fun s hs ↦ (hreg s hs).1)
    (G := fun s ↦ -logDeriv χ.entireLFunction s)
    (fun s hs ↦ ((χ.analyticAt_entireLFunction s).logDeriv hs).fun_neg.differentiableAt
      |>.differentiableWithinAt)
    (r := if χ = 1 then 1 else 0)
    (fun s hs ↦ by rw [(χ.LSeriesHasSum_twist_vonMangoldt hs).LSeries_eq]; ring)
    (C₀ := B) (B' := 25) (fun s hs ↦ by simpa only [norm_neg, Real.rpow_ofNat] using (hreg s hs).2)
  refine ⟨c * a ^ (1 / 26 : ℝ), by positivity, max C 1, by positivity, fun x hx ↦ ?_⟩
  have hω := TauCeti.le_inghamExponent_of_mul_log_rpow_le ha.le
    (by norm_num : (0 : ℝ) ≤ 25) hηlow (by linarith : 1 ≤ x)
  norm_num at hω
  have he : Real.exp (-c * TauCeti.inghamExponent η x) ≤
      Real.exp (-(c * a ^ (1 / 26 : ℝ)) * Real.log x ^ (1 / 26 : ℝ)) := by
    rw [Real.exp_le_exp, neg_mul, neg_mul, neg_le_neg_iff, mul_assoc]
    exact mul_le_mul_of_nonneg_left hω hc.le
  have hmain : (if χ = 1 then (1 : ℂ) else 0) * x = (if χ = 1 then (x : ℂ) else 0) := by
    split <;> simp
  rw [← hmain]
  exact (hC x hx).trans (mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left C 1) (by positivity))
    he (Real.exp_nonneg _) (by positivity))

open Classical in
/-- For each fixed Dirichlet character the twisted von Mangoldt summatory error saves
any prescribed power of the logarithm. -/
theorem exists_norm_sum_mul_vonMangoldt_sub_le_div_log_pow {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (k : ℕ) :
    ∃ C > (0 : ℝ), ∀ x : ℝ, 3 ≤ x →
      ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n * (Λ n : ℂ)) - (if χ = 1 then (x : ℂ) else 0)‖ ≤
        C * x / Real.log x ^ k := by
  obtain ⟨c, hc, C, hC₀, hC⟩ := χ.exists_norm_sum_mul_vonMangoldt_sub_le
  obtain ⟨D, -, hD⟩ := TauCeti.exists_rpow_mul_exp_neg_mul_le
    (σ := 26 * (k : ℝ)) (by positivity) hc
  have hD₀ : 0 < D := (Real.exp_pos (-c)).trans_le (by simpa using hD 1 zero_le_one)
  refine ⟨C * D, mul_pos hC₀ hD₀, fun x hx ↦ (hC x hx).trans ?_⟩
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hpow : (Real.log x ^ (1 / 26 : ℝ)) ^ (26 * (k : ℝ)) = Real.log x ^ k := by
    rw [← Real.rpow_mul hlog.le, show (1 / 26 : ℝ) * (26 * (k : ℝ)) = k by ring,
      Real.rpow_natCast]
  have hb := hD (Real.log x ^ (1 / 26 : ℝ)) (by positivity)
  rw [hpow, ← neg_mul] at hb
  rw [le_div_iff₀ (pow_pos hlog _)]
  calc
    _ = C * x * (Real.log x ^ k * Real.exp (-c * Real.log x ^ (1 / 26 : ℝ))) := by ac_rfl
    _ ≤ C * x * D := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

end DirichletCharacter
