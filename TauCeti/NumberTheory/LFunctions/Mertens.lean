/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.NumberField.DirichletDensity
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.Psi
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.SpecialFunctions.Integrability.Log
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub
import TauCeti.Analysis.SpecialFunctions.LogIntegral
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Convergence
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.DedekindZeta.Basic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.DedekindZeta.Tail
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.IdealZetaSum
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.PrimeIdealTheorem
import TauCeti.NumberTheory.NumberField.DedekindZeta

/-!
# Mertens' theorems for a number field

Let `K` be a number field. This file proves Mertens' first theorem for `K`: the sum of
`log N𝔭 / N𝔭` over the nonzero prime ideals `𝔭` of `𝓞 K` of norm at most `x` is `log x + O(1)`.
Over `ℚ` this is Mertens' classical estimate `∑_{p ≤ x} log p / p = log x + O(1)`. Partial
summation then gives Mertens' second theorem,
`∑_{N𝔭 ≤ x} 1 / N𝔭 = log log x + B_K + O(1 / log x)` with a constant `B_K`. Identifying `B_K`
through the Euler product of `ζ_K` gives Mertens' product (Rosen)
`∏_{N𝔭 ≤ x} (1 - N𝔭⁻¹)⁻¹ ~ e^γ κ_K log x`, with `γ` Euler's constant and `κ_K` the residue of
`ζ_K` at `s = 1`. Over `ℚ` this is Mertens' third theorem `∏_{p ≤ x} (1 - 1 / p)⁻¹ ~ e^γ log x`.

The proof of the first theorem evaluates `∑_{N𝔞 ≤ x} log N𝔞` in two ways.

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

For the second theorem, write `S(t) = ∑_{N𝔭 ≤ t} log N𝔭 / N𝔭 = log t + R(t)`, so that `R` is
bounded on `t ≥ 2` by the first theorem. Abel summation against `1 / log t`
(`TauCeti.primeSummatory_div_log_eq_div_log_add_integral`) gives
`∑_{N𝔭 ≤ x} 1 / N𝔭 = S(x) / log x + ∫_2^x S(t) / (t log² t) dt`. The main part `log t` of `S`
integrates to `log log x - log log 2`, and `∫_2^∞ R(t) / (t log² t) dt` converges absolutely with
tail `O(1 / log x)` beyond `x`. The resulting expansion is that of Lebacque, Proposition 2.

For the product, the constant `B_K` is computed from the behaviour of the prime zeta sum
`P(s) = ∑_𝔭 N𝔭 ^ (-s)` as `s → 1⁺` (Lebacque, Proposition 3). Abel summation writes
`P(s) = (s - 1) ∫_1^∞ t ^ (-s) (∑_{N𝔭 ≤ t} 1 / N𝔭) dt`. The second theorem and the Abelian
limit `TauCeti.tendsto_smul_integral_Ioi_rpow_smul_nhdsGT_zero` handle the part
`∑_{N𝔭 ≤ t} 1 / N𝔭 - log log t → B_K`. Mathlib's
`Real.eulerMascheroniConstant_eq_neg_integral_log_log` evaluates the `log log t` part exactly:
`(s - 1) ∫_1^∞ log (log t) t ^ (-s) dt = -γ - log (s - 1)`. Together they give
`P(s) = log (1 / (s - 1)) + B_K - γ + o(1)`. On the other side, the Euler product writes
`log ζ_K(s)` as `P(s)` plus the sum of the remainders `-log (1 - N𝔭 ^ (-s)) - N𝔭 ^ (-s)`. That
sum is continuous at `s = 1` (`TauCeti.tendsto_tsum_neg_log_one_sub_sub_absNorm_rpow`), and the
residue gives `log ζ_K(s) = log (1 / (s - 1)) + log κ_K + o(1)`.
Comparing the two expansions gives `B_K = γ + log κ_K + ∑_𝔭 (log (1 - N𝔭⁻¹) + N𝔭⁻¹)`. Adding the
convergent sum of the remainders at `s = 1` to the second theorem then gives the logarithm of the
product.

## Main results

* `TauCeti.LFunctions.idealSummatory_log_absNorm_eq`: Chebyshev's identity
  `∑_{N𝔞 ≤ x} log N𝔞 = ∑_{N(𝔭 ^ k) ≤ x} log N𝔭 · #{𝔞 : N𝔞 ≤ x / N(𝔭 ^ k)}`.
* `TauCeti.LFunctions.isBigO_primePowerSummatory_div_sub_log`:
  `∑_{N(𝔭 ^ k) ≤ x} log N𝔭 / N(𝔭 ^ k) = log x + O(1)`.
* `TauCeti.LFunctions.isBigO_primeSummatory_log_absNorm_div_sub_log`: Mertens' first theorem,
  `∑_{N𝔭 ≤ x} log N𝔭 / N𝔭 = log x + O(1)`.
* `TauCeti.LFunctions.mertensConstant`: the constant `B_K`, the limit of
  `∑_{N𝔭 ≤ x} 1 / N𝔭 - log log x`.
* `TauCeti.LFunctions.isBigO_primeSummatory_inv_absNorm_sub_log_log_sub_mertensConstant` and
  `TauCeti.LFunctions.tendsto_primeSummatory_inv_absNorm_sub_log_log`: Mertens' second theorem,
  `∑_{N𝔭 ≤ x} 1 / N𝔭 = log log x + B_K + O(1 / log x)`.
* `TauCeti.LFunctions.tendsto_primeIdealZetaSum_univ_sub_log_one_div_sub_one`:
  `∑_𝔭 N𝔭 ^ (-s) = log (1 / (s - 1)) + B_K - γ + o(1)` as `s → 1⁺`.
* `TauCeti.LFunctions.mertensConstant_eq`: `B_K = γ + log κ_K + ∑_𝔭 (log (1 - N𝔭⁻¹) + N𝔭⁻¹)`.
* `TauCeti.LFunctions.tendsto_primeSummatory_neg_log_one_sub_inv_absNorm_sub_log_log`:
  `∑_{N𝔭 ≤ x} -log (1 - N𝔭⁻¹) = log log x + γ + log κ_K + o(1)`.
* `TauCeti.LFunctions.tendsto_prod_one_sub_inv_absNorm_div_log`: Mertens' product,
  `∏_{N𝔭 ≤ x} (1 - N𝔭⁻¹)⁻¹ ~ e^γ κ_K log x`.

## References

* M. Rosen, *A generalization of Mertens' theorem*, J. Ramanujan Math. Soc. 14 (1999).
* P. Lebacque, *Generalised Mertens and Brauer–Siegel theorems*, Acta Arith. 130 (2007),
  §4.1, Propositions 2 and 3, and Theorem 5 (NF).
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.1, for
  the rational case.
-/

public section

open Asymptotics Filter MeasureTheory NumberField
open scoped nonZeroDivisors NumberField Topology

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

/-! ### Mertens' second theorem -/

/-- The weight `log N𝔭 / N𝔭` of Mertens' first theorem is nonnegative. -/
private theorem log_absNorm_div_absNorm_nonneg (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    0 ≤ Real.log (Ideal.absNorm v.asIdeal) / Ideal.absNorm v.asIdeal :=
  div_nonneg (log_absNorm_asIdeal_pos v).le (Nat.cast_nonneg _)

/-- **Mertens' first theorem with a uniform constant.** The error
`∑_{N𝔭 ≤ t} log N𝔭 / N𝔭 - log t` is bounded on the whole half-line `t ≥ 2`, not only
eventually: below the threshold of the asymptotic bound both terms are bounded by monotonicity. -/
private theorem exists_abs_primeSummatory_log_absNorm_div_sub_log_le :
    ∃ C, ∀ t, 2 ≤ t → |primeSummatory K
        (fun v ↦ Real.log (Ideal.absNorm v.asIdeal) / Ideal.absNorm v.asIdeal) t -
          Real.log t| ≤ C := by
  set S := primeSummatory K
    (fun v ↦ Real.log (Ideal.absNorm v.asIdeal) / Ideal.absNorm v.asIdeal)
  have hmono : Monotone S := summatory_mono _ (log_absNorm_div_absNorm_nonneg K)
  have hS0 (t : ℝ) : 0 ≤ S t := summatory_nonneg _ (log_absNorm_div_absNorm_nonneg K) t
  have hO := (isBigO_primeSummatory_log_absNorm_div_sub_log K).isBigO_principal_Ici (a := 2)
    zero_lt_one (fun _ _ ↦ by simp)
    fun Y ↦ ⟨S Y + Real.log Y, fun t ht ↦ by
      have hlog0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith [ht.1])
      have hlog : Real.log t ≤ Real.log Y := Real.log_le_log (by linarith [ht.1]) ht.2
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hmono ht.2, hS0 t, hS0 Y]⟩
  obtain ⟨C, -, hC⟩ := hO.exists_nonneg
  refine ⟨C, fun t ht ↦ ?_⟩
  have h := isBigOWith_principal.mp hC t ht
  rwa [Real.norm_eq_abs, norm_one, mul_one] at h

/-- **Abel summation turns Mertens' first theorem into the second.** For `x ≥ 2`, writing
`S(t) = ∑_{N𝔭 ≤ t} log N𝔭 / N𝔭`,
`∑_{N𝔭 ≤ x} 1 / N𝔭 = S(x) / log x + log log x - log log 2 + ∫_2^x (S(t) - log t) / (t log² t) dt`.
-/
private theorem primeSummatory_inv_absNorm_eq {x : ℝ} (hx : 2 ≤ x) :
    primeSummatory K (fun v ↦ (Ideal.absNorm v.asIdeal : ℝ)⁻¹) x =
      primeSummatory K
          (fun v ↦ Real.log (Ideal.absNorm v.asIdeal) / Ideal.absNorm v.asIdeal) x /
          Real.log x + (Real.log (Real.log x) - Real.log (Real.log 2)) +
        ∫ t in Set.Ioc 2 x, (primeSummatory K
          (fun v ↦ Real.log (Ideal.absNorm v.asIdeal) / Ideal.absNorm v.asIdeal) t -
            Real.log t) * (t⁻¹ / Real.log t ^ 2) := by
  set S := primeSummatory K
    (fun v ↦ Real.log (Ideal.absNorm v.asIdeal) / Ideal.absNorm v.asIdeal)
  have hw : (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) ↦
      Real.log (Ideal.absNorm v.asIdeal) / Ideal.absNorm v.asIdeal /
        Real.log (Ideal.absNorm v.asIdeal)) = fun v ↦ (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
    funext v
    rw [div_right_comm, div_self (log_absNorm_asIdeal_pos v).ne', one_div]
  have key := primeSummatory_div_log_eq_div_log_add_integral K
    (fun v ↦ Real.log (Ideal.absNorm v.asIdeal) / Ideal.absNorm v.asIdeal) x
  rw [hw] at key
  -- Split the integrand as `1 / (t log t)` plus the contribution of the error term.
  have hsplit : ∫ t in Set.Ioc 2 x, S t / (t * Real.log t ^ 2) =
      ∫ t in Set.Ioc 2 x, (t⁻¹ / Real.log t + (S t - Real.log t) * (t⁻¹ / Real.log t ^ 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    have ht0 : t ≠ 0 := (by linarith [ht.1] : (0 : ℝ) < t).ne'
    have hlog : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    field_simp
    ring
  have hIcc : Set.Icc 2 x ⊆ Set.Ioi 1 := fun t ht ↦ one_lt_two.trans_le ht.1
  have hcont : ContinuousOn (fun t : ℝ ↦ t⁻¹ / Real.log t ^ 2) (Set.Icc 2 x) :=
    (Real.continuousOn_inv_div_log_pow 2).mono hIcc
  have hint₁ : IntegrableOn (fun t : ℝ ↦ t⁻¹ / Real.log t) (Set.Ioc 2 x) := by
    simpa only [pow_one] using
      ((Real.continuousOn_inv_div_log_pow 1).mono hIcc).integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self
  have hint₂ : IntegrableOn (fun t ↦ (S t - Real.log t) * (t⁻¹ / Real.log t ^ 2))
      (Set.Ioc 2 x) := by
    have hS' : IntegrableOn (fun t ↦ t⁻¹ / Real.log t ^ 2 * S t) (Set.Icc 2 x) :=
      integrableOn_mul_summatory _ _ zero_le_two (hcont.integrableOn_Icc)
    have hlog' : IntegrableOn (fun t ↦ t⁻¹ / Real.log t ^ 2 * Real.log t) (Set.Icc 2 x) :=
      (hcont.mul (Real.continuousOn_log.mono fun t ht ↦
        (by linarith [ht.1] : (0 : ℝ) < t).ne')).integrableOn_Icc
    refine ((hS'.sub hlog').mono_set Set.Ioc_subset_Icc_self).congr_fun (fun t _ ↦ ?_)
      measurableSet_Ioc
    simp only [Pi.sub_apply]
    ring
  rw [key, hsplit, integral_add hint₁ hint₂, ← intervalIntegral.integral_of_le hx,
    integral_inv_div_log one_lt_two (by linarith)]
  ring

/-- **Mertens' second theorem with an error term.** There is a constant `B` with
`∑_{N𝔭 ≤ x} 1 / N𝔭 = log log x + B + O(1 / log x)`. -/
private theorem exists_isBigO_primeSummatory_inv_absNorm_sub_log_log_sub :
    ∃ B, (fun x ↦ primeSummatory K (fun v ↦ (Ideal.absNorm v.asIdeal : ℝ)⁻¹) x -
      Real.log (Real.log x) - B) =O[atTop] fun x ↦ (Real.log x)⁻¹ := by
  obtain ⟨C, hC⟩ := exists_abs_primeSummatory_log_absNorm_div_sub_log_le K
  set S := primeSummatory K
    (fun v ↦ Real.log (Ideal.absNorm v.asIdeal) / Ideal.absNorm v.asIdeal) with hS
  set R : ℝ → ℝ := fun t ↦ (S t - Real.log t) * (t⁻¹ / Real.log t ^ 2) with hR
  -- `R` is dominated by `C / (t log² t)`, which is integrable at infinity.
  have hRle (t : ℝ) (ht : 2 ≤ t) : ‖R t‖ ≤ C * (t⁻¹ / Real.log t ^ 2) := by
    rw [hR, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg
      (div_nonneg (inv_nonneg.mpr (by linarith)) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hC t ht)
      (div_nonneg (inv_nonneg.mpr (by linarith)) (sq_nonneg _))
  have hRmeas : AEStronglyMeasurable R := by
    have hSmeas : Measurable S :=
      (summatory_mono _ (log_absNorm_div_absNorm_nonneg K)).measurable
    exact ((hSmeas.sub Real.measurable_log).mul
      (measurable_inv.div (Real.measurable_log.pow_const 2))).aestronglyMeasurable
  have hRint {a : ℝ} (ha : 2 ≤ a) : IntegrableOn R (Set.Ioi a) :=
    ((integrableOn_inv_div_log_sq_Ioi (by linarith : (1 : ℝ) < a)).const_mul C).mono'
      hRmeas.restrict ((ae_restrict_mem measurableSet_Ioi).mono fun t ht ↦
        hRle t (ha.trans (le_of_lt ht)))
  refine ⟨1 - Real.log (Real.log 2) + ∫ t in Set.Ioi 2, R t, IsBigO.of_bound (2 * C) ?_⟩
  filter_upwards [eventually_ge_atTop 2] with x hx
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  -- Split the integral over `(2, ∞)` at `x`.
  have hsplit : ∫ t in Set.Ioc 2 x, R t = (∫ t in Set.Ioi 2, R t) - ∫ t in Set.Ioi x, R t := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hx, setIntegral_union Set.Ioc_disjoint_Ioi_same
      measurableSet_Ioi ((hRint le_rfl).mono_set Set.Ioc_subset_Ioi_self) (hRint hx)]
    ring
  -- The tail of the integral is at most `C / log x`.
  have htail : ‖∫ t in Set.Ioi x, R t‖ ≤ C * (Real.log x)⁻¹ := by
    rw [← integral_inv_div_log_sq_Ioi (by linarith : (1 : ℝ) < x), ← integral_const_mul]
    exact norm_integral_le_of_norm_le
      ((integrableOn_inv_div_log_sq_Ioi (by linarith : (1 : ℝ) < x)).const_mul C)
      ((ae_restrict_mem measurableSet_Ioi).mono fun t ht ↦ hRle t (hx.trans (le_of_lt ht)))
  have hSx : |S x / Real.log x - 1| ≤ C * (Real.log x)⁻¹ := by
    rw [← div_self hlogx.ne', ← sub_div, abs_div, abs_of_pos hlogx, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hC x hx) (inv_nonneg.mpr hlogx.le)
  rw [primeSummatory_inv_absNorm_eq K hx, ← hS, hsplit, Real.norm_eq_abs, Real.norm_of_nonneg
    (inv_nonneg.mpr hlogx.le)]
  rw [Real.norm_eq_abs] at htail
  calc _ = |(S x / Real.log x - 1) - ∫ t in Set.Ioi x, R t| := by congr 1; ring
    _ ≤ |S x / Real.log x - 1| + |∫ t in Set.Ioi x, R t| := abs_sub _ _
    _ ≤ 2 * C * (Real.log x)⁻¹ := by linarith

/-- **Mertens' constant of a number field**: the limit `B_K` of
`∑_{N𝔭 ≤ x} 1 / N𝔭 - log log x` as `x → ∞`, the sum over the nonzero prime ideals of `𝓞 K`.
It exists by `tendsto_primeSummatory_inv_absNorm_sub_log_log`; over `ℚ` it is the classical
Meissel–Mertens constant. -/
noncomputable def mertensConstant : ℝ :=
  limUnder atTop fun x ↦
    primeSummatory K (fun v ↦ (Ideal.absNorm v.asIdeal : ℝ)⁻¹) x - Real.log (Real.log x)

/-- **Mertens' second theorem for a number field.** The sum of `1 / N𝔭` over the nonzero prime
ideals `𝔭` of `𝓞 K` of norm at most `x` is `log log x + B_K + O(1 / log x)`, where
`B_K = mertensConstant K`. -/
theorem isBigO_primeSummatory_inv_absNorm_sub_log_log_sub_mertensConstant :
    (fun x ↦ primeSummatory K (fun v ↦ (Ideal.absNorm v.asIdeal : ℝ)⁻¹) x -
      Real.log (Real.log x) - mertensConstant K) =O[atTop] fun x ↦ (Real.log x)⁻¹ := by
  obtain ⟨B, hB⟩ := exists_isBigO_primeSummatory_inv_absNorm_sub_log_log_sub K
  have hlim : Tendsto (fun x ↦ primeSummatory K (fun v ↦ (Ideal.absNorm v.asIdeal : ℝ)⁻¹) x -
      Real.log (Real.log x)) atTop (𝓝 B) := by
    have h := (hB.trans_tendsto (Real.tendsto_log_atTop.inv_tendsto_atTop)).add_const B
    simpa using h
  rwa [mertensConstant, hlim.limUnder_eq]

/-- **Mertens' second theorem for a number field, limit form.** As `x → ∞`,
`∑_{N𝔭 ≤ x} 1 / N𝔭 - log log x` tends to Mertens' constant `B_K = mertensConstant K`. -/
theorem tendsto_primeSummatory_inv_absNorm_sub_log_log :
    Tendsto (fun x ↦ primeSummatory K (fun v ↦ (Ideal.absNorm v.asIdeal : ℝ)⁻¹) x -
      Real.log (Real.log x)) atTop (𝓝 (mertensConstant K)) := by
  have h := ((isBigO_primeSummatory_inv_absNorm_sub_log_log_sub_mertensConstant K).trans_tendsto
    (Real.tendsto_log_atTop.inv_tendsto_atTop)).add_const (mertensConstant K)
  simpa using h

open IsDedekindDomain

/-! ### Mertens' product -/

/-- The summatory function `∑_{N𝔭 ≤ t} 1 / N𝔭` of Mertens' second theorem is monotone. -/
private theorem monotone_primeSummatory_inv_absNorm :
    Monotone (primeSummatory K fun v ↦ (Ideal.absNorm v.asIdeal : ℝ)⁻¹) :=
  summatory_mono _ fun _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)

/-- For `σ > 1` and `t ≥ 0`, `∑_{N𝔭 ≤ t} 1 / N𝔭 ≤ t ^ (σ - 1) ∑_𝔭 N𝔭 ^ (-σ)`, since
`1 / N𝔭 = N𝔭 ^ (σ - 1) N𝔭 ^ (-σ)` and `N𝔭 ≤ t` in the sum. -/
private theorem primeSummatory_inv_absNorm_le {σ t : ℝ} (hσ : 1 < σ) (ht : 0 ≤ t) :
    primeSummatory K (fun v ↦ (Ideal.absNorm v.asIdeal : ℝ)⁻¹) t ≤
      t ^ (σ - 1) * ∑' v : HeightOneSpectrum (𝓞 K), (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
  rw [primeSummatory_apply]
  calc ∑ v ∈ primesLE K t, (Ideal.absNorm v.asIdeal : ℝ)⁻¹
      ≤ ∑ v ∈ primesLE K t, t ^ (σ - 1) * (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
        refine Finset.sum_le_sum fun v hv ↦ ?_
        have hN : (0 : ℝ) < Ideal.absNorm v.asIdeal :=
          zero_lt_two.trans_le (two_le_absNorm_asIdeal_real v)
        rw [← Real.rpow_neg_one, show (-1 : ℝ) = σ - 1 + -σ by ring, Real.rpow_add hN]
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hN.le
            ((mem_normLE fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal).mp hv)
            (by linarith))
          (Real.rpow_nonneg hN.le _)
    _ = t ^ (σ - 1) * ∑ v ∈ primesLE K t, (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
        ((summable_absNorm_rpow_primes_of_one_lt hσ).sum_le_tsum _
          fun v _ ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg ht _)

/-- For `s > 1`, `t ↦ t ^ (-s) ∑_{N𝔭 ≤ t} 1 / N𝔭` is integrable on `(1, ∞)`: by
`primeSummatory_inv_absNorm_le` at `σ = (1 + s) / 2` it is `O(t ^ (-(1 + s) / 2))`. -/
private theorem integrableOn_rpow_neg_mul_primeSummatory_inv_absNorm {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun t ↦ t ^ (-s) *
      primeSummatory K (fun v ↦ (Ideal.absNorm v.asIdeal : ℝ)⁻¹) t) (Set.Ioi 1) := by
  set σ : ℝ := (1 + s) / 2 with hσdef
  have hσ : 1 < σ := by rw [hσdef]; linarith
  set Z := ∑' v : HeightOneSpectrum (𝓞 K), (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)
  refine ((integrableOn_Ioi_rpow_of_lt (show -s + (σ - 1) < -1 by rw [hσdef]; linarith)
    zero_lt_one).const_mul Z).mono' ?_ ?_
  · exact ((measurable_id.pow_const _).mul
      (monotone_primeSummatory_inv_absNorm K).measurable).aestronglyMeasurable
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 1 < t) ↦ ?_
    have ht0 : (0 : ℝ) < t := zero_lt_one.trans ht
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _)
      (summatory_nonneg _ (fun _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)) t)), Real.rpow_add ht0]
    calc t ^ (-s) * primeSummatory K (fun v ↦ (Ideal.absNorm v.asIdeal : ℝ)⁻¹) t
        ≤ t ^ (-s) * (t ^ (σ - 1) * Z) := mul_le_mul_of_nonneg_left
          (primeSummatory_inv_absNorm_le K hσ ht0.le) (Real.rpow_nonneg ht0.le _)
      _ = Z * (t ^ (-s) * t ^ (σ - 1)) := by ring

/-- Abel summation of the weight `1 / N𝔭` against `t ^ (1 - s)`: for every cutoff `x`,
`∑_{N𝔭 ≤ x} N𝔭 ^ (-s) = x ^ (1 - s) P(x) + (s - 1) ∫_2^x t ^ (-s) P(t) dt` with
`P(t) = ∑_{N𝔭 ≤ t} 1 / N𝔭`. -/
private theorem primeSummatory_absNorm_rpow_neg_eq {s : ℝ} (x : ℝ) :
    primeSummatory K (fun v ↦ (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) x =
      x ^ (1 - s) * primeSummatory K (fun v ↦ (Ideal.absNorm v.asIdeal : ℝ)⁻¹) x +
        (s - 1) * ∫ t in Set.Ioc 2 x,
          t ^ (-s) * primeSummatory K (fun v ↦ (Ideal.absNorm v.asIdeal : ℝ)⁻¹) t := by
  have hderiv : deriv (fun u : ℝ ↦ u ^ (1 - s)) = fun t ↦ (1 - s) * t ^ (-s) := by
    funext t
    rw [Real.deriv_rpow_const, show 1 - s - 1 = -s by ring]
  have hdiff : ∀ t ∈ Set.Icc 2 x, DifferentiableAt ℝ (fun u : ℝ ↦ u ^ (1 - s)) t :=
    fun t ht ↦ (Real.hasDerivAt_rpow_const
      (Or.inl (by linarith [ht.1] : (0 : ℝ) < t).ne')).differentiableAt
  have hcont : ContinuousOn (fun t : ℝ ↦ (1 - s) * t ^ (-s)) (Set.Icc 2 x) :=
    continuousOn_const.mul (continuousOn_id.rpow_const fun t ht ↦
      Or.inl (by linarith [ht.1] : (0 : ℝ) < t).ne')
  have key := primeSummatory_mul_eq_sub_integral_mul K
    (fun v ↦ (Ideal.absNorm v.asIdeal : ℝ)⁻¹) x hdiff
    (by rw [hderiv]; exact hcont.integrableOn_Icc)
  have hw : (fun v : HeightOneSpectrum (𝓞 K) ↦
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹ * (Ideal.absNorm v.asIdeal : ℝ) ^ (1 - s)) =
      fun v ↦ (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) := by
    funext v
    have hN : (0 : ℝ) < Ideal.absNorm v.asIdeal :=
      zero_lt_two.trans_le (two_le_absNorm_asIdeal_real v)
    rw [← Real.rpow_neg_one, ← Real.rpow_add hN]
    ring_nf
  rw [hw] at key
  rw [key, hderiv]
  simp_rw [mul_assoc]
  rw [integral_const_mul]
  ring

/-- For `s > 1`, `∑_𝔭 N𝔭 ^ (-s) = (s - 1) ∫_1^∞ t ^ (-s) (∑_{N𝔭 ≤ t} 1 / N𝔭) dt`, by Abel
summation of the weight `1 / N𝔭` against `t ^ (1 - s)`. -/
private theorem primeIdealZetaSum_univ_eq_mul_integral {s : ℝ} (hs : 1 < s) :
    (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s =
      (s - 1) * ∫ t in Set.Ioi 1,
        t ^ (-s) * primeSummatory K (fun v ↦ (Ideal.absNorm v.asIdeal : ℝ)⁻¹) t := by
  set P := primeSummatory K fun v ↦ (Ideal.absNorm v.asIdeal : ℝ)⁻¹
  have hint := integrableOn_rpow_neg_mul_primeSummatory_inv_absNorm K hs
  -- Let the cutoff `x` of the Abel summation `primeSummatory_absNorm_rpow_neg_eq` tend to `∞`.
  set σ : ℝ := (1 + s) / 2 with hσdef
  have hσ : 1 < σ := by rw [hσdef]; linarith
  set Z := ∑' v : HeightOneSpectrum (𝓞 K), (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)
  have hlhs : Tendsto (primeSummatory K (fun v ↦ (Ideal.absNorm v.asIdeal : ℝ) ^ (-s))) atTop
      (𝓝 ((Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s)) := by
    rw [Set.primeIdealZetaSum_univ]
    exact ((summable_absNorm_rpow_primes_of_one_lt hs).hasSum.comp
      (tendsto_normLE_atTop _)).congr fun x ↦ (primeSummatory_apply K _ x).symm
  have hboundary : Tendsto (fun x : ℝ ↦ x ^ (1 - s) * P x) atTop (𝓝 0) := by
    have hdecay : Tendsto (fun x : ℝ ↦ Z * x ^ (-((s - 1) / 2))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith : 0 < (s - 1) / 2)).const_mul Z
    refine squeeze_zero' ?_ ?_ hdecay
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact mul_nonneg (Real.rpow_nonneg hx.le _)
        (summatory_nonneg _ (fun _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)) x)
    · filter_upwards [eventually_ge_atTop 1] with x hx
      have hx0 : (0 : ℝ) < x := zero_lt_one.trans_le hx
      calc x ^ (1 - s) * P x ≤ x ^ (1 - s) * (x ^ (σ - 1) * Z) :=
            mul_le_mul_of_nonneg_left (primeSummatory_inv_absNorm_le K hσ hx0.le)
              (Real.rpow_nonneg hx0.le _)
        _ = Z * (x ^ (1 - s) * x ^ (σ - 1)) := by ring
        _ = Z * x ^ (-((s - 1) / 2)) := by
          rw [← Real.rpow_add hx0, hσdef]
          ring_nf
  have hintegral : Tendsto (fun x : ℝ ↦ ∫ t in Set.Ioc 2 x, t ^ (-s) * P t) atTop
      (𝓝 (∫ t in Set.Ioi 2, t ^ (-s) * P t)) := by
    refine (intervalIntegral_tendsto_integral_Ioi 2
      (hint.mono_set (Set.Ioi_subset_Ioi one_le_two)) tendsto_id).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with x hx
    exact intervalIntegral.integral_of_le hx
  have hrhs := hboundary.add (hintegral.const_mul (s - 1))
  rw [zero_add] at hrhs
  rw [tendsto_nhds_unique hlhs
    (hrhs.congr fun x ↦ (primeSummatory_absNorm_rpow_neg_eq K x).symm)]
  -- The integrand vanishes on `(1, 2)`, where no prime has norm below the cutoff.
  rw [← integral_Ici_eq_integral_Ioi, ← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    measurableSet_Ioi (Set.Ici_subset_Ioi.mpr one_lt_two)]
  intro t ht
  exact mul_eq_zero_of_right _
    (summatory_eq_zero_of_lt _ two_le_absNorm_asIdeal_real (not_le.mp ht.2) _)

/-- **The prime zeta sum near `s = 1`, with its constant.** As `s → 1⁺`,
`∑_𝔭 N𝔭 ^ (-s) = log (1 / (s - 1)) + B_K - γ + o(1)`, where `B_K = mertensConstant K` and `γ` is
Euler's constant. This refines `TauCeti.primeIdealZetaSum_univ_sub_log_one_div_sub_one_isBigO`,
which bounds the difference by a constant. -/
theorem tendsto_primeIdealZetaSum_univ_sub_log_one_div_sub_one :
    Tendsto (fun s : ℝ ↦ (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s -
      Real.log (1 / (s - 1))) (𝓝[>] 1)
      (𝓝 (mertensConstant K - Real.eulerMascheroniConstant)) := by
  set P := primeSummatory K fun v ↦ (Ideal.absNorm v.asIdeal : ℝ)⁻¹
  have hg : LocallyIntegrableOn (fun t ↦ P t - Real.log (Real.log t)) (Set.Ici 1) :=
    ((monotone_primeSummatory_inv_absNorm K).locallyIntegrable.locallyIntegrableOn _).sub
      locallyIntegrableOn_log_log
  have habel := tendsto_smul_integral_Ioi_rpow_smul_nhdsGT_zero hg
    (tendsto_primeSummatory_inv_absNorm_sub_log_log K)
  have hshift : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using ((continuous_sub_right (1 : ℝ)).tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      exact sub_pos.mpr hs
  refine ((habel.comp hshift).sub_const Real.eulerMascheroniConstant).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  have hγ := Real.eulerMascheroniConstant_eq_neg_integral_log_log hs
  have hsplit : ∫ t in Set.Ioi 1, t ^ (-(s - 1) - 1) • (P t - Real.log (Real.log t)) =
      (∫ t in Set.Ioi 1, t ^ (-s) * P t) -
        ∫ t in Set.Ioi 1, Real.log (Real.log t) * t ^ (-s) := by
    rw [← integral_sub (integrableOn_rpow_neg_mul_primeSummatory_inv_absNorm K hs)
      (Real.integrableOn_log_log_mul_rpow hs)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    rw [smul_eq_mul, show -(s - 1) - 1 = -s by ring]
    ring
  rw [Function.comp_apply, smul_eq_mul, hsplit, primeIdealZetaSum_univ_eq_mul_integral K hs,
    one_div, Real.log_inv]
  linear_combination (-1 : ℝ) * hγ

/-- **Mertens' constant of a number field in closed form** (Rosen; Lebacque, Proposition 3):
`B_K = γ + log κ_K + ∑_𝔭 (log (1 - N𝔭⁻¹) + N𝔭⁻¹)`, with `γ` Euler's constant and
`κ_K = dedekindZeta_residue K` the residue of `ζ_K` at `s = 1`. Over `ℚ` this is the classical
expression of the Meissel–Mertens constant. -/
theorem mertensConstant_eq :
    mertensConstant K = Real.eulerMascheroniConstant + Real.log (dedekindZeta_residue K) +
      ∑' v : HeightOneSpectrum (𝓞 K),
        (Real.log (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) + (Ideal.absNorm v.asIdeal : ℝ)⁻¹) := by
  -- Near `s = 1⁺`, `log ζ_K(s)` is the prime zeta sum plus the sum of the quadratic remainders.
  have hlim := (tendsto_primeIdealZetaSum_univ_sub_log_one_div_sub_one K).add
    (tendsto_tsum_neg_log_one_sub_sub_absNorm_rpow (K := K))
  have heq := tendsto_nhds_unique (hlim.congr' ?_)
    (tendsto_log_dedekindZeta_re_sub_log_one_div_sub_one (K := K))
  · have hE : ∑' v : HeightOneSpectrum (𝓞 K),
        (Real.log (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) + (Ideal.absNorm v.asIdeal : ℝ)⁻¹) =
        -∑' v : HeightOneSpectrum (𝓞 K),
          (-Real.log (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) := by
      rw [← tsum_neg]
      exact tsum_congr fun v ↦ by ring
    rw [hE]
    linarith
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  have hsum : ∑' v : HeightOneSpectrum (𝓞 K), -Real.log (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) =
      ∑' v : HeightOneSpectrum (𝓞 K), (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) +
        ∑' v : HeightOneSpectrum (𝓞 K), (-Real.log (1 - (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) -
          (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)) := by
    rw [← (summable_absNorm_rpow_primes_of_one_lt hs).tsum_add
      (summable_neg_log_one_sub_sub_absNorm_rpow (by linarith))]
    exact tsum_congr fun v ↦ by ring
  rw [log_dedekindZeta_re_eq_tsum_neg_log_one_sub hs, Set.primeIdealZetaSum_univ, hsum]
  ring

/-- **Mertens' product for a number field, logarithmic form.** As `x → ∞`,
`∑_{N𝔭 ≤ x} -log (1 - N𝔭⁻¹) = log log x + γ + log κ_K + o(1)`, the sum over the nonzero prime
ideals of `𝓞 K` of norm at most `x`, with `γ` Euler's constant and
`κ_K = dedekindZeta_residue K`. -/
theorem tendsto_primeSummatory_neg_log_one_sub_inv_absNorm_sub_log_log :
    Tendsto (fun x ↦ primeSummatory K
        (fun v ↦ -Real.log (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹)) x - Real.log (Real.log x))
      atTop (𝓝 (Real.eulerMascheroniConstant + Real.log (dedekindZeta_residue K))) := by
  set r : HeightOneSpectrum (𝓞 K) → ℝ :=
    fun v ↦ -Real.log (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹) - (Ideal.absNorm v.asIdeal : ℝ)⁻¹
  have hr : Summable r := by
    simpa only [r, Real.rpow_neg_one] using
      summable_neg_log_one_sub_sub_absNorm_rpow (K := K) (s := 1) (by norm_num)
  have hR : Tendsto (primeSummatory K r) atTop (𝓝 (∑' v, r v)) :=
    (hr.hasSum.comp (tendsto_normLE_atTop _)).congr fun x ↦ (primeSummatory_apply K r x).symm
  have hconst : mertensConstant K + ∑' v, r v =
      Real.eulerMascheroniConstant + Real.log (dedekindZeta_residue K) := by
    rw [mertensConstant_eq, add_assoc, ← Summable.tsum_add ?_ hr]
    · simp [r]
    · exact hr.neg.congr fun v ↦ by simp only [r]; ring
  rw [← hconst]
  refine ((tendsto_primeSummatory_inv_absNorm_sub_log_log K).add hR).congr fun x ↦ ?_
  simp only [primeSummatory_apply]
  rw [sub_add_eq_add_sub, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun v _ ↦ by simp only [r]; ring

/-- **Mertens' product for a number field** (Rosen; Lebacque, *Generalised Mertens and
Brauer–Siegel theorems*, Theorem 5 (NF)): as `x → ∞`,
`∏_{N𝔭 ≤ x} (1 - N𝔭⁻¹)⁻¹ ~ e^γ κ_K log x`, the product over the nonzero prime ideals of `𝓞 K`
of absolute norm at most `x`, with `γ` Euler's constant and `κ_K = dedekindZeta_residue K` the
residue of `ζ_K` at `s = 1`. The factor is `1` at every prime of norm above `x`, so the product is
a `finprod`. Over `ℚ` it is Mertens' third theorem `∏_{p ≤ x} (1 - 1 / p)⁻¹ ~ e^γ log x`. -/
theorem tendsto_prod_one_sub_inv_absNorm_div_log :
    Tendsto (fun x : ℝ ↦
      (∏ᶠ 𝔭 : HeightOneSpectrum (𝓞 K),
        if (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x then (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ)⁻¹)⁻¹
        else 1) /
        (Real.exp Real.eulerMascheroniConstant * dedekindZeta_residue K * Real.log x))
      atTop (𝓝 1) := by
  have h := (tendsto_primeSummatory_neg_log_one_sub_inv_absNorm_sub_log_log K).sub_const
    (Real.eulerMascheroniConstant + Real.log (dedekindZeta_residue K))
  rw [sub_self] at h
  have h' := (Real.continuous_exp.tendsto 0).comp h
  rw [Real.exp_zero] at h'
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hκ := dedekindZeta_residue_pos K
  -- The finite product is the exponential of the sum of the logarithms of its factors.
  have hprod : (∏ᶠ 𝔭 : HeightOneSpectrum (𝓞 K),
      if (Ideal.absNorm 𝔭.asIdeal : ℝ) ≤ x then (1 - (Ideal.absNorm 𝔭.asIdeal : ℝ)⁻¹)⁻¹
      else 1) = Real.exp (primeSummatory K
        (fun v ↦ -Real.log (1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹)) x) := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := primesLE K x), primeSummatory_apply,
      Real.exp_sum]
    · refine Finset.prod_congr rfl fun v hv ↦ ?_
      have h1 : 0 < 1 - (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := sub_pos.mpr
        (inv_lt_one_of_one_lt₀ (one_lt_two.trans_le (two_le_absNorm_asIdeal_real v)))
      rw [ite_eq_left
          ((mem_normLE fun v : HeightOneSpectrum (𝓞 K) ↦ Ideal.absNorm v.asIdeal).mp hv),
        Real.exp_neg, Real.exp_log h1]
    · intro v hv
      rw [Finset.mem_coe, mem_normLE]
      by_contra hvx
      exact hv (ite_eq_right hvx)
  rw [Function.comp_apply, hprod, Real.exp_sub, Real.exp_sub, Real.exp_add, Real.exp_log hlog,
    Real.exp_log hκ, div_div, mul_comm (Real.log x)]

end TauCeti.LFunctions
