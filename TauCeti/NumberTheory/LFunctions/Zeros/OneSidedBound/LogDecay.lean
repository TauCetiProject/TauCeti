/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebyshev.ResidueClass
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Remainder
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.LogDecay
import TauCeti.NumberTheory.Chebyshev.TwistedResidueClass
import TauCeti.NumberTheory.DirichletCharacter.Quadratic

/-!
# Logarithmic decay of the signed prime remainder

A prime number theorem in progressions at the base modulus and at the product modulus
controls the signed summatory error. Once the constant in the normalized Riesz sum is known
(i.e. `primeRemainder` tends to zero), a log-power saving for the summatory error gives a
log-power saving for the remainder. This is a partial-summation route to the rate in
`New.eventually_abs_primeRemainder_le` in `New/Reduction/Zeros/PrimeNumberTheorem` of
lsernau/grh-lean (`72fead1`).
-/

public section

open Asymptotics Filter Finset Real
open scoped Topology

namespace TauCeti.OneSidedBound

/-- Transfer progression estimates at `q` and `q*d` to a logarithmic saving for the signed
prime remainder. The ordinary convergence hypothesis identifies its centering constant;
the rate only uses the progression estimates with exponent `B + 2`. -/
theorem eventually_abs_primeRemainder_le_of_progression_estimates {d q : ℕ}
    [Fact d.Prime] [NeZero q] (hd : d ≠ 2) (hqd : q.Coprime d) (B : ℕ)
    (hq : (fun t ↦ Chebyshev.psiAP q 1 t - t / q.totient) =O[atTop]
      fun t ↦ t / log t ^ (B + 2))
    (hprod : ∀ a : ZMod (q * d), IsUnit a →
      (fun t ↦ Chebyshev.psiAP (q * d) a t - t / (q * d).totient) =O[atTop]
        fun t ↦ t / log t ^ (B + 2))
    (hlim : Tendsto (primeRemainder d q) atTop (𝓝 0)) :
    ∀ᶠ y : ℝ in atTop, |primeRemainder d q y| ≤ (log y ^ B)⁻¹ := by
  let χ : DirichletCharacter ℂ d := (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)
  have hχ : χ ≠ 1 := DirichletCharacter.quadraticChar_ringHomComp_ne_one (by simp) hd
  let a (n : ℕ) : ℂ := primeWeight d q n
  let A : ℂ := (q.totient : ℂ)⁻¹
  let c : ℂ := ((logDerivMean d q 1).re : ℂ)
  have hE : (fun t : ℝ ↦ (∑ n ∈ Icc 1 ⌊t⌋₊, a n) - A * t) =O[atTop]
      fun t ↦ t / log t ^ (B + 2) := by
    refine (Chebyshev.isBigO_sum_residueClass_smul_one_sub_char
      isUnit_one hqd χ hχ hq hprod).congr_left (fun t ↦ ?_)
    rw [← Icc_add_one_left_eq_Ioc, zero_add]
    have hterm (n : ℕ) : ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod q) n •
        (1 - χ (n : ZMod d)) = a n := by
      by_cases hn : (n : ZMod q) = 1 <;>
        simp [hn, a, primeWeight_def, ArithmeticFunction.vonMangoldt.residueClass,
          χ, legendreSym, Complex.real_smul]
    simp only [hterm, Complex.real_smul, mul_one, A, Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  have hnorm (y : ℝ) (hy : 0 < y) :
      rieszSum a y / (y : ℂ) - A * (log y : ℂ) - c = (primeRemainder d q y : ℂ) := by
    rw [rieszSum_def, primeRemainder_def, sum_div]
    push_cast
    congr 2
    · refine sum_congr rfl fun n _ ↦ ?_
      dsimp only [a]
      field_simp [Complex.ofReal_ne_zero.mpr hy.ne']
    · dsimp only [A]
      ring
  have heq := (eventually_gt_atTop (0 : ℝ)).mono fun y hy ↦ hnorm y hy
  have hc : Tendsto (fun y : ℝ ↦ rieszSum a y / (y : ℂ) - A * (log y : ℂ)) atTop (𝓝 c) := by
    have hlim' : Tendsto (fun y ↦ (primeRemainder d q y : ℂ)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto 0).comp hlim
    have hadd := hlim'.add_const c
    rw [zero_add] at hadd
    exact hadd.congr' (heq.mono fun _ hy ↦ by linear_combination -hy)
  have h := tendsto_log_pow_smul_rieszSum_div_sub_log_sub B hE hc
  have hreal := (tendsto_zero_iff_norm_tendsto_zero.mp h).eventually_le_const
    (zero_lt_one : (0 : ℝ) < 1)
  filter_upwards [hreal, eventually_gt_atTop (1 : ℝ)] with y hy hy₁
  simp only [hnorm y (zero_lt_one.trans hy₁), norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (log_pos hy₁).le B)] at hy
  rw [← one_div, le_div_iff₀ (pow_pos (log_pos hy₁) _), mul_comm]
  exact hy

end TauCeti.OneSidedBound
