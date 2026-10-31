/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.Psi
import Mathlib.Algebra.Order.Floor.Semifield
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.PrimeIdealTheorem
import TauCeti.NumberTheory.NumberField.DedekindZeta

/-!
# Mertens' first theorem for a number field

Let `K` be a number field. This file proves Mertens' first theorem for `K`: the sum of
`log N𝔭 / N𝔭` over the nonzero prime ideals `𝔭` of `𝓞 K` of norm at most `x` is `log x + O(1)`.
Over `ℚ` this is Mertens' classical estimate `∑_{p ≤ x} log p / p = log x + O(1)`. It is the first
step towards Mertens' product `∏_{N𝔭 ≤ x} (1 - N𝔭⁻¹)⁻¹ ~ e^γ κ_K log x` (Rosen), where it is
summed by parts once more.

The proof evaluates `∑_{N𝔞 ≤ x} log N𝔞` in two ways.

* Writing `log N𝔞 = ∑_{𝔟 ∣ 𝔞} Λ_K(𝔟)` and exchanging the order of summation gives
  `∑_{N𝔟 ≤ x} Λ_K(𝔟) · #{𝔞 : N𝔞 ≤ x / N𝔟}` (`TauCeti.LFunctions.idealSummatory_log_absNorm_eq`).
  The divisor-sum identity is used in its norm-regrouped form
  `TauCeti.normCoeff_vonMangoldt_mul_normCoeff_one`, and the exchange is Mathlib's
  `ArithmeticFunction.sum_Ioc_mul_eq_sum_sum`.
* Abel summation against the ideal count `#{N𝔞 ≤ y} = κ_K y + O(y ^ (1 - 1 / [K : ℚ]))`
  (`TauCeti.isBigO_card_idealsLE_sub`) gives `log x · #{N𝔞 ≤ x} + O(x)`.

Inserting the ideal count into the first expression produces the main term
`κ_K x ∑_{N𝔟 ≤ x} Λ_K(𝔟) / N𝔟`. The error terms sum to
`O(x ^ (1 - 1 / [K : ℚ]) ∑_{N𝔟 ≤ x} Λ_K(𝔟) N𝔟 ^ (1 / [K : ℚ] - 1))`, which partial summation
from Chebyshev's bound `ψ_K(t) = O(t)` (a consequence of `TauCeti.primeIdealTheorem`) makes
`O(x)`. Dividing by `κ_K x`, with `κ_K = dedekindZeta_residue K > 0`, gives the prime-power form
`∑_{N𝔟 ≤ x} Λ_K(𝔟) / N𝔟 = log x + O(1)`. The higher prime powers `𝔭 ^ k`, `k ≥ 2`, contribute
`O(1)`, because their weighted count is `O(√t log² t)` (`TauCeti.higherPrimePowerTheta_le`).

## Main results

* `TauCeti.LFunctions.idealSummatory_log_absNorm_eq`: Chebyshev's identity
  `∑_{N𝔞 ≤ x} log N𝔞 = ∑_{N(𝔭 ^ k) ≤ x} log N𝔭 · #{𝔞 : N𝔞 ≤ x / N(𝔭 ^ k)}`.
* `TauCeti.LFunctions.isBigO_primePowerSummatory_div_sub_log`:
  `∑_{N(𝔭 ^ k) ≤ x} log N𝔭 / N(𝔭 ^ k) = log x + O(1)`.
* `TauCeti.LFunctions.isBigO_primeSummatory_log_absNorm_div_sub_log`: Mertens' first theorem,
  `∑_{N𝔭 ≤ x} log N𝔭 / N𝔭 = log x + O(1)`.

## References

* M. Rosen, *A generalization of Mertens' theorem*, J. Ramanujan Math. Soc. 14 (1999).
* P. Lebacque, *Generalised Mertens and Brauer–Siegel theorems*, Acta Arith. 130 (2007),
  §4.1.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.1, for
  the rational case.
-/

public section

open Asymptotics Filter MeasureTheory NumberField
open scoped nonZeroDivisors NumberField

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-! ### Chebyshev's identity -/

/-- **Chebyshev's identity for a number field.** Summing `log N𝔞 = ∑_{𝔟 ∣ 𝔞} Λ_K(𝔟)` over the
nonzero integral ideals of norm at most `x` and exchanging the order of summation,
`∑_{N𝔞 ≤ x} log N𝔞 = ∑_{N(𝔭 ^ k) ≤ x} log N𝔭 · #{𝔞 : N𝔞 ≤ x / N(𝔭 ^ k)}`. -/
theorem idealSummatory_log_absNorm_eq (x : ℝ) :
    idealSummatory K (fun I ↦ Real.log (Ideal.absNorm (I : Ideal (𝓞 K)))) x =
      primePowerSummatory K (fun A ↦ primePowerWeight A *
        ((idealsLE K (x / Ideal.absNorm (A : Ideal (𝓞 K)))).card : ℝ)) x := by
  apply Complex.ofReal_injective
  set G : ℕ → ℂ := fun n ↦ idealSummatory K (1 : IdealArithmeticFunction K) (x / n) with hG
  have hcard (y : ℝ) : (((idealsLE K y).card : ℝ) : ℂ) =
      idealSummatory K (1 : IdealArithmeticFunction K) y := by
    simp [idealSummatory_apply]
  have hlhs : ((idealSummatory K (fun I ↦ Real.log (Ideal.absNorm (I : Ideal (𝓞 K)))) x : ℝ) : ℂ)
      = idealSummatory K (1 : IdealArithmeticFunction K).logMul x := by
    rw [idealSummatory_apply, idealSummatory_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun I _ ↦ ?_
    rw [IdealArithmeticFunction.logMul_apply, Pi.one_apply, mul_one,
      Complex.ofReal_log (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have hrhs : ((primePowerSummatory K (fun A ↦ primePowerWeight A *
      ((idealsLE K (x / Ideal.absNorm (A : Ideal (𝓞 K)))).card : ℝ)) x : ℝ) : ℂ) =
      idealSummatory K (fun I ↦ IdealArithmeticFunction.vonMangoldt I *
        G (Ideal.absNorm (I : Ideal (𝓞 K)))) x := by
    rw [idealSummatory_eq_primePowerSummatory K _
      (fun A ↦ (primePowerWeight A : ℂ) * G (Ideal.absNorm (A : Ideal (𝓞 K))))
      (fun A ↦ by rw [vonMangoldt_eq_primePowerWeight])
      (fun I hI ↦ by rw [IdealArithmeticFunction.vonMangoldt_eq_zero_of_not_isPrimePow hI,
        zero_mul]),
      primePowerSummatory_apply, primePowerSummatory_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun A _ ↦ ?_
    rw [Complex.ofReal_mul, hcard]
  have hIcc (n : ℕ) : Finset.Icc 1 n = Finset.Ioc 0 n := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hlhs, hrhs, idealSummatory_eq_sum_Icc_normCoeff, idealSummatory_eq_sum_Icc_normCoeff,
    ← normCoeff_vonMangoldt_mul_normCoeff_one, hIcc, ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [normCoeff_fun_mul_comp_absNorm, hG]
  beta_reduce
  rw [idealSummatory_eq_sum_Icc_normCoeff, Nat.floor_div_natCast, hIcc]

/-! ### Uniform forms of the two counting estimates -/

/-- The exponent `1 - 1 / [K : ℚ]` of the error term of the ideal count lies in `[0, 1)`. -/
private theorem one_sub_inv_finrank_mem_Ico :
    1 - (Module.finrank ℚ K : ℝ)⁻¹ ∈ Set.Ico 0 1 := by
  have hd : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  exact ⟨sub_nonneg.mpr (inv_le_one_of_one_le₀ hd),
    sub_lt_self 1 (inv_pos.mpr (zero_lt_one.trans_le hd))⟩

/-- The ideal count with a power saving, uniformly on `[1, ∞)`. -/
private theorem exists_abs_card_idealsLE_sub_le :
    ∃ C, 0 ≤ C ∧ ∀ y, 1 ≤ y → |((idealsLE K y).card : ℝ) - dedekindZeta_residue K * y| ≤
      C * y ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) := by
  have hκ := (dedekindZeta_residue_pos K).le
  have hpow (y : ℝ) (hy : 1 ≤ y) : 1 ≤ y ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) :=
    Real.one_le_rpow hy (one_sub_inv_finrank_mem_Ico K).1
  have hO := (isBigO_card_idealsLE_sub K).isBigO_principal_Ici zero_lt_one
    (fun y hy ↦ (hpow y hy).trans_eq (Real.norm_of_nonneg (zero_le_one.trans (hpow y hy))).symm)
    fun Y ↦ ⟨(idealsLE K Y).card + dedekindZeta_residue K * Y, fun y hy ↦ by
      have hcard : ((idealsLE K y).card : ℝ) ≤ (idealsLE K Y).card := by
        exact_mod_cast Finset.card_le_card (normLE_mono _ hy.2)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [mul_le_mul_of_nonneg_left hy.2 hκ, hy.1]⟩
  obtain ⟨C, hC0, hC⟩ := hO.exists_nonneg
  refine ⟨C, hC0, fun y hy ↦ ?_⟩
  have h := isBigOWith_principal.mp hC y hy
  rwa [Real.norm_eq_abs, Real.norm_of_nonneg (zero_le_one.trans (hpow y hy))] at h

/-- **Chebyshev's upper bound** `ψ_K(t) ≤ D t` on `[1, ∞)`, from the prime ideal theorem. -/
private theorem exists_primePsi_le :
    ∃ D, 0 ≤ D ∧ ∀ t, 1 ≤ t → primePsi K Set.univ t ≤ D * t := by
  have hO := (primeIdealTheorem K).1.isBigO.isBigO_principal_Ici zero_lt_one
    (fun t ht ↦ ht.trans_eq (Real.norm_of_nonneg (zero_le_one.trans ht)).symm)
    fun Y ↦ ⟨primePsi K Set.univ Y, fun t ht ↦ by
      rw [Real.norm_of_nonneg (primePsi_nonneg _ t)]
      exact primePsi_mono _ ht.2⟩
  obtain ⟨D, hD0, hD⟩ := hO.exists_nonneg
  refine ⟨D, hD0, fun t ht ↦ ?_⟩
  have h := isBigOWith_principal.mp hD t ht
  rw [Real.norm_of_nonneg (primePsi_nonneg _ t), Real.norm_of_nonneg (zero_le_one.trans ht)] at h
  exact h

/-! ### Mertens' first theorem -/

/-- **Abel summation of `log N𝔞`.** If the ideal count differs from `ρ y` by at most
`C y ^ (1 - 1 / [K : ℚ])` on `[1, ∞)`, then `∑_{N𝔞 ≤ x} log N𝔞` is `log x` times the ideal count
up to `(ρ + C) x`. -/
private theorem abs_idealSummatory_log_absNorm_sub_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y, 1 ≤ y → |((idealsLE K y).card : ℝ) - dedekindZeta_residue K * y| ≤
      C * y ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹)) {x : ℝ} (hx : 1 ≤ x) :
    |idealSummatory K (fun I ↦ Real.log (Ideal.absNorm (I : Ideal (𝓞 K)))) x -
        Real.log x * (idealsLE K x).card| ≤ (dedekindZeta_residue K + C) * x := by
  set ρ := dedekindZeta_residue K
  set S : ℝ → ℝ := fun t ↦ idealSummatory K (fun _ ↦ (1 : ℝ)) t with hS
  have hScard (t : ℝ) : S t = (idealsLE K t).card := by simp [hS, idealSummatory_apply]
  have hinv : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.Icc 1 x) :=
    continuousOn_inv₀.mono fun t ht ↦ (zero_lt_one.trans_le ht.1).ne'
  have habel := idealSummatory_mul_eq_sub_integral_mul K (fun _ ↦ (1 : ℝ)) (g := Real.log) x
    (fun t ht ↦ Real.differentiableAt_log (zero_lt_one.trans_le ht.1).ne')
    (by rw [Real.deriv_log']; exact hinv.integrableOn_Icc)
  simp only [one_mul, Real.deriv_log'] at habel
  rw [habel, ← hScard, ← intervalIntegral.integral_of_le hx]
  -- On `[1, x]` the ideal count is at most `(ρ + C) t`.
  have hle (t : ℝ) (ht : t ∈ Set.Icc 1 x) : t⁻¹ * S t ≤ ρ + C := by
    have ht0 : 0 < t := zero_lt_one.trans_le ht.1
    have hpow : t ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹) ≤ t :=
      Real.rpow_le_self_of_one_le ht.1 (one_sub_inv_finrank_mem_Ico K).2.le
    have h := (abs_le.mp (hC t ht.1)).2
    rw [hScard, inv_mul_le_iff₀ ht0]
    nlinarith [mul_le_mul_of_nonneg_left hpow hC0]
  have hint : IntervalIntegrable (fun t ↦ t⁻¹ * S t) volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr
      (integrableOn_mul_summatory _ _ zero_le_one hinv.integrableOn_Icc)
  have hI0 : 0 ≤ ∫ t in (1 : ℝ)..x, t⁻¹ * S t :=
    intervalIntegral.integral_nonneg hx fun t ht ↦
      mul_nonneg (inv_nonneg.mpr (zero_le_one.trans ht.1)) (by rw [hScard]; positivity)
  have hI : ∫ t in (1 : ℝ)..x, t⁻¹ * S t ≤ (x - 1) * (ρ + C) := by
    rw [← smul_eq_mul, ← intervalIntegral.integral_const]
    exact intervalIntegral.integral_mono_on hx hint intervalIntegrable_const hle
  rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg hI0]
  nlinarith [dedekindZeta_residue_pos K]

/-- **The main term of Chebyshev's identity.** Writing the ideal count as `ρ y + E(y)`, the right
side of `TauCeti.LFunctions.idealSummatory_log_absNorm_eq` is
`ρ x ∑_{N(𝔭 ^ k) ≤ x} log N𝔭 / N(𝔭 ^ k)` up to `∑ log N𝔭 · E(x / N(𝔭 ^ k))`. With
`|E(y)| ≤ C y ^ θ`, `θ = 1 - 1 / [K : ℚ]`, that error is at most
`C x ^ θ ∑ log N𝔭 · N(𝔭 ^ k) ^ (-θ)`, which Chebyshev's bound `ψ_K(t) ≤ D t` makes at most
`C D [K : ℚ] x`. -/
private theorem abs_primePowerSummatory_mul_card_sub_le {C D : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y, 1 ≤ y → |((idealsLE K y).card : ℝ) - dedekindZeta_residue K * y| ≤
      C * y ^ (1 - (Module.finrank ℚ K : ℝ)⁻¹)) (hD0 : 0 ≤ D)
    (hD : ∀ t, 1 ≤ t → primePsi K Set.univ t ≤ D * t) {x : ℝ} (hx : 1 ≤ x) :
    |primePowerSummatory K (fun A ↦ primePowerWeight A *
        ((idealsLE K (x / Ideal.absNorm (A : Ideal (𝓞 K)))).card : ℝ)) x -
      dedekindZeta_residue K * x *
        primePowerSummatory K (fun A ↦ primePowerWeight A / Ideal.absNorm (A : Ideal (𝓞 K))) x| ≤
      C * D * Module.finrank ℚ K * x := by
  set ρ := dedekindZeta_residue K
  set d : ℝ := (Module.finrank ℚ K : ℝ)
  obtain ⟨hθ0, hθ1⟩ := one_sub_inv_finrank_mem_Ico K
  set θ := 1 - d⁻¹ with hθ
  have hd : 0 < d := Nat.cast_pos.mpr Module.finrank_pos
  have h1θ : 1 - θ = d⁻¹ := by rw [hθ]; ring
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  -- The prime powers weighted by `N(𝔭 ^ k) ^ (-θ)`: Abel summation against `ψ_K(t) ≤ D t`.
  have hψ : primePowerSummatory K
      (fun A ↦ primePowerWeight A * (Ideal.absNorm (A : Ideal (𝓞 K)) : ℝ) ^ (-θ)) x ≤
        D * d * x ^ (1 - θ) := by
    have h := summatory_mul_rpow_neg_le
      (fun A : IdealPrimePower K ↦ Ideal.absNorm (A : Ideal (𝓞 K)))
      (fun A ↦ one_le_two.trans (two_le_absNorm_idealPrimePower_real A)) primePowerWeight
      (C := D) (β := 1) hθ0 (by linarith) hx fun t ht ↦ by
        have h := hD t ht.1
        rw [primePsi_apply] at h
        rw [Real.rpow_one, summatory_apply]
        simpa using h
    have hfrac : θ * D * ((x ^ (1 - θ) - 1) / (1 - θ)) ≤ θ * D * (x ^ (1 - θ) / (1 - θ)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) (by linarith))
        (mul_nonneg hθ0 hD0)
    calc _ ≤ D * x ^ (1 - θ) + θ * D * ((x ^ (1 - θ) - 1) / (1 - θ)) := h
      _ ≤ D * x ^ (1 - θ) + θ * D * (x ^ (1 - θ) / (1 - θ)) := by linarith
      _ = D * d * x ^ (1 - θ) := by
        rw [h1θ, hθ]
        field_simp
        ring
  rw [primePowerSummatory_apply, primePowerSummatory_apply, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ A ∈ primePowersLE K x, |primePowerWeight A *
          ((idealsLE K (x / Ideal.absNorm (A : Ideal (𝓞 K)))).card : ℝ) -
          ρ * x * (primePowerWeight A / Ideal.absNorm (A : Ideal (𝓞 K)))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ A ∈ primePowersLE K x, C * x ^ θ *
          (primePowerWeight A * (Ideal.absNorm (A : Ideal (𝓞 K)) : ℝ) ^ (-θ)) :=
        Finset.sum_le_sum fun A hA ↦ by
          set n : ℝ := (Ideal.absNorm (A : Ideal (𝓞 K)) : ℝ)
          have hn : 1 ≤ n := one_le_two.trans (two_le_absNorm_idealPrimePower_real A)
          have hn0 : 0 < n := zero_lt_one.trans_le hn
          have hy : 1 ≤ x / n := (one_le_div hn0).mpr
            ((mem_normLE fun B : IdealPrimePower K ↦ Ideal.absNorm (B : Ideal (𝓞 K))).mp hA)
          have hw := primePowerWeight_nonneg A
          have hsplit : primePowerWeight A * ((idealsLE K (x / n)).card : ℝ) -
              ρ * x * (primePowerWeight A / n) =
              primePowerWeight A * (((idealsLE K (x / n)).card : ℝ) - ρ * (x / n)) := by
            ring
          rw [hsplit, abs_mul, abs_of_nonneg hw]
          calc primePowerWeight A * |((idealsLE K (x / n)).card : ℝ) - ρ * (x / n)|
              ≤ primePowerWeight A * (C * (x / n) ^ θ) := mul_le_mul_of_nonneg_left (hC _ hy) hw
            _ = C * x ^ θ * (primePowerWeight A * n ^ (-θ)) := by
              rw [Real.div_rpow hx0.le hn0.le, Real.rpow_neg hn0.le]
              ring
    _ = C * x ^ θ * primePowerSummatory K
          (fun A ↦ primePowerWeight A * (Ideal.absNorm (A : Ideal (𝓞 K)) : ℝ) ^ (-θ)) x := by
        rw [← Finset.mul_sum, primePowerSummatory_apply]
    _ ≤ C * x ^ θ * (D * d * x ^ (1 - θ)) := mul_le_mul_of_nonneg_left hψ (by positivity)
    _ = C * D * d * (x ^ θ * x ^ (1 - θ)) := by ring
    _ = C * D * d * x := by rw [← Real.rpow_add hx0, add_sub_cancel, Real.rpow_one]

/-- **Mertens' first theorem for a number field, prime-power form.** The sum of `Λ_K(𝔞) / N𝔞`
over the nonzero integral ideals of norm at most `x` is `log x + O(1)`: the weight `log N𝔭` of
each prime power `𝔭 ^ k` divided by its norm, summed over `N(𝔭 ^ k) ≤ x`, differs from `log x` by
a bounded amount. -/
theorem isBigO_primePowerSummatory_div_sub_log :
    (fun x ↦ primePowerSummatory K
        (fun A ↦ primePowerWeight A / Ideal.absNorm (A : Ideal (𝓞 K))) x - Real.log x) =O[atTop]
      fun _ ↦ (1 : ℝ) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_card_idealsLE_sub_le K
  obtain ⟨D, hD0, hD⟩ := exists_primePsi_le K
  set ρ := dedekindZeta_residue K
  have hρ : 0 < ρ := dedekindZeta_residue_pos K
  set d : ℝ := (Module.finrank ℚ K : ℝ)
  have hd : 0 < d := Nat.cast_pos.mpr Module.finrank_pos
  refine IsBigO.of_bound ((C * d + (ρ + C) + C * D * d) / ρ) ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  set W := primePowerSummatory K
    (fun A ↦ primePowerWeight A / Ideal.absNorm (A : Ideal (𝓞 K))) x
  set P := primePowerSummatory K (fun A ↦ primePowerWeight A *
    ((idealsLE K (x / Ideal.absNorm (A : Ideal (𝓞 K)))).card : ℝ)) x
  set E := ((idealsLE K x).card : ℝ) - ρ * x
  -- The error of the ideal count at `x`, against `log x ≤ d x ^ (1 / d)`.
  have hlog : |E * Real.log x| ≤ C * d * x := by
    have hlx := Real.log_le_rpow_div hx0.le (inv_pos.mpr hd)
    rw [div_inv_eq_mul] at hlx
    rw [abs_mul, abs_of_nonneg (Real.log_nonneg hx)]
    calc |E| * Real.log x ≤ C * x ^ (1 - d⁻¹) * (x ^ d⁻¹ * d) :=
          mul_le_mul (hC x hx) hlx (Real.log_nonneg hx) (by positivity)
      _ = C * d * (x ^ (1 - d⁻¹) * x ^ d⁻¹) := by ring
      _ = C * d * x := by rw [← Real.rpow_add hx0, sub_add_cancel, Real.rpow_one]
  have h1 := abs_idealSummatory_log_absNorm_sub_le K hC0 hC hx
  rw [idealSummatory_log_absNorm_eq] at h1
  have h2 := abs_primePowerSummatory_mul_card_sub_le K hC0 hC hD0 hD hx
  have key : ρ * x * |W - Real.log x| ≤ (C * d + (ρ + C) + C * D * d) * x := by
    have hdecomp : ρ * x * (W - Real.log x) =
        -(P - ρ * x * W) + (P - Real.log x * (idealsLE K x).card) + E * Real.log x := by
      simp only [E]
      ring
    rw [← abs_of_pos (mul_pos hρ hx0), ← abs_mul, hdecomp]
    refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
    rw [abs_neg]
    nlinarith [h1, h2, hlog]
  rw [norm_one, mul_one, Real.norm_eq_abs, le_div_iff₀ hρ]
  nlinarith [key]

/-- **The higher prime powers contribute `O(1)`.** The sum of `log N𝔭 / N(𝔭 ^ k)` over the prime
powers with `k ≥ 2` and `N(𝔭 ^ k) ≤ x` is bounded uniformly in `x`: their summatory function is
`O(√t log² t) = O(t ^ (3/4))`, and Abel summation against `1 / t` turns this into a bound. -/
private theorem exists_primePowerSummatory_higherPrimePowerWeight_div_le :
    ∃ B, ∀ x, 1 ≤ x → primePowerSummatory K
      (fun A ↦ higherPrimePowerWeight A / Ideal.absNorm (A : Ideal (𝓞 K))) x ≤ B := by
  set c := (Module.finrank ℚ K : ℝ) / (2 * Real.log 2)
  have hc : 0 ≤ c := by have := Real.log_pos one_lt_two; positivity
  refine ⟨5 * (64 * c), fun x hx ↦ ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  -- `√t log² t ≤ 64 t ^ (3/4)` on `[1, ∞)`, from `log t ≤ 8 t ^ (1/8)`.
  have hH (t : ℝ) (ht : t ∈ Set.Icc 1 x) :
      summatory (fun A : IdealPrimePower K ↦ Ideal.absNorm (A : Ideal (𝓞 K)))
        higherPrimePowerWeight t ≤ 64 * c * t ^ (3 / 4 : ℝ) := by
    have ht0 : 0 < t := zero_lt_one.trans_le ht.1
    have h := higherPrimePowerTheta_le K ht.1
    rw [higherPrimePowerTheta_apply] at h
    have hlog := Real.log_le_rpow_div ht0.le (by norm_num : (0 : ℝ) < 1 / 8)
    have hlog2 : Real.log t ^ 2 ≤ 64 * t ^ (1 / 4 : ℝ) := by
      calc Real.log t ^ 2 ≤ (t ^ (1 / 8 : ℝ) / (1 / 8)) ^ 2 :=
            pow_le_pow_left₀ (Real.log_nonneg ht.1) hlog 2
        _ = 64 * (t ^ (1 / 8 : ℝ)) ^ (2 : ℝ) := by rw [Real.rpow_two]; ring
        _ = 64 * t ^ (1 / 4 : ℝ) := by rw [← Real.rpow_mul ht0.le]; norm_num
    refine h.trans ?_
    calc c * (Real.sqrt t * Real.log t ^ 2) ≤ c * (t ^ (1 / 2 : ℝ) * (64 * t ^ (1 / 4 : ℝ))) := by
          rw [Real.sqrt_eq_rpow]
          gcongr
      _ = 64 * c * (t ^ (1 / 2 : ℝ) * t ^ (1 / 4 : ℝ)) := by ring
      _ = 64 * c * t ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add ht0]; norm_num
  have h := summatory_mul_rpow_neg_le
    (fun A : IdealPrimePower K ↦ Ideal.absNorm (A : Ideal (𝓞 K)))
    (fun A ↦ one_le_two.trans (two_le_absNorm_idealPrimePower_real A)) higherPrimePowerWeight
    zero_le_one (by norm_num) hx hH
  have hpow0 : 0 ≤ x ^ (3 / 4 - 1 : ℝ) := Real.rpow_nonneg hx0.le _
  have hpow1 : x ^ (3 / 4 - 1 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  simp only [Real.rpow_neg_one, ← div_eq_mul_inv] at h
  refine h.trans ?_
  have hfrac : (x ^ (3 / 4 - 1 : ℝ) - 1) / (3 / 4 - 1) = 4 * (1 - x ^ (3 / 4 - 1 : ℝ)) := by ring
  rw [hfrac]
  nlinarith [mul_le_mul_of_nonneg_left hpow1 (by positivity : (0 : ℝ) ≤ 64 * c),
    mul_nonneg (by positivity : (0 : ℝ) ≤ 64 * c) hpow0]

/-- **Mertens' first theorem for a number field.** The sum of `log N𝔭 / N𝔭` over the nonzero prime
ideals `𝔭` of `𝓞 K` of norm at most `x` is `log x + O(1)`. -/
theorem isBigO_primeSummatory_log_absNorm_div_sub_log :
    (fun x ↦ primeSummatory K
        (fun v ↦ Real.log (Ideal.absNorm v.asIdeal) / Ideal.absNorm v.asIdeal) x - Real.log x)
      =O[atTop] fun _ ↦ (1 : ℝ) := by
  obtain ⟨B, hB⟩ := exists_primePowerSummatory_higherPrimePowerWeight_div_le K
  set R : ℝ → ℝ := primePowerSummatory K
    (fun A ↦ higherPrimePowerWeight A / Ideal.absNorm (A : Ideal (𝓞 K))) with hR
  -- Splitting off the higher prime powers leaves exactly the primes.
  have hsplit (x : ℝ) : primePowerSummatory K
      (fun A ↦ primePowerWeight A / Ideal.absNorm (A : Ideal (𝓞 K))) x =
      R x + primeSummatory K
        (fun v ↦ Real.log (Ideal.absNorm v.asIdeal) / Ideal.absNorm v.asIdeal) x := by
    have hw : (fun A : IdealPrimePower K ↦ primePowerWeight A / Ideal.absNorm (A : Ideal (𝓞 K))) =
        (fun A ↦ higherPrimePowerWeight A / Ideal.absNorm (A : Ideal (𝓞 K))) +
          fun A ↦ (primePowerWeight A - higherPrimePowerWeight A) /
            Ideal.absNorm (A : Ideal (𝓞 K)) := by
      funext A
      simp only [Pi.add_apply]
      ring
    rw [hw, primePowerSummatory_add, primePowerSummatory_eq_primeSummatory K
      (fun A ↦ (primePowerWeight A - higherPrimePowerWeight A) / Ideal.absNorm (A : Ideal (𝓞 K)))
      (fun A hA ↦ by rw [higherPrimePowerWeight_of_not_prime hA, sub_self, zero_div])]
    congr 1
    refine congrArg (primeSummatory K · x) (funext fun v ↦ ?_)
    rw [higherPrimePowerWeight_of_prime (IdealPrimePower.prime_ofPrime v), sub_zero,
      primePowerWeight_ofPrime, IdealPrimePower.coe_ofPrime]
  have hRO : R =O[atTop] fun _ ↦ (1 : ℝ) := by
    refine IsBigO.of_bound B ?_
    filter_upwards [eventually_ge_atTop 1] with x hx
    rw [norm_one, mul_one, Real.norm_of_nonneg (primePowerSummatory_nonneg K _ (fun A ↦
      div_nonneg (higherPrimePowerWeight_nonneg A) (Nat.cast_nonneg _)) x)]
    exact hB x hx
  refine ((isBigO_primePowerSummatory_div_sub_log K).sub hRO).congr_left fun x ↦ ?_
  rw [hsplit]
  ring

end TauCeti.LFunctions
