/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.LogDeriv
public import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv.Riesz
public import TauCeti.NumberTheory.LFunctions.Data.DedekindZeta
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.LeadingCoefficient

/-!
# The negative gamma contribution to the first Dedekind zeta Riesz formula

The negative poles of the archimedean factor are spaced by two at real places and by one at
complex places. Their first Riesz contribution is continuous on `[1, ∞)` and is `O(1/y)`.
`s(s−1)` times its Mellin transform equals the logarithmic derivative of the gamma factor with
the pole at zero removed, minus the affine interpolant of the resulting function at `0` and `1`.
This separates the negative trivial-zero contribution from the term at the origin.

The calculation uses `TauCeti.mul_integral_rieszGammaCorrection` and the digamma recurrence
`Complex.digamma_apply_add_one` to account for the pole at zero.
-/

public section

open Complex Filter MeasureTheory NumberField.InfinitePlace Set
open scoped Topology

namespace TauCeti.LFunctions

variable (K : Type*) [Field K] [NumberField K]

/-- The negative gamma contribution in first Riesz smoothing of Dedekind zeta: one series
starting at `−2` per real place and one starting at `−1` per complex place. -/
noncomputable def dedekindZetaRieszGammaCorrection (y : ℝ) : ℂ :=
  nrRealPlaces K * rieszGammaCorrection 2 2 y + nrComplexPlaces K * rieszGammaCorrection 1 1 y

/-- The real and complex places contribute with their respective multiplicities. -/
theorem dedekindZetaRieszGammaCorrection_def (y : ℝ) :
    dedekindZetaRieszGammaCorrection K y =
      nrRealPlaces K * rieszGammaCorrection 2 2 y +
        nrComplexPlaces K * rieszGammaCorrection 1 1 y :=
  (rfl)

/-- The negative gamma contribution is continuous on `[1, ∞)`, the range of the Mellin integral. -/
theorem continuousOn_dedekindZetaRieszGammaCorrection :
    ContinuousOn (dedekindZetaRieszGammaCorrection K) (Ici 1) :=
  (continuousOn_const.mul (continuousOn_rieszGammaCorrection zero_lt_two zero_lt_two)).add
    (continuousOn_const.mul (continuousOn_rieszGammaCorrection zero_lt_one zero_lt_one))

/-- The negative gamma contribution is bounded in norm by a constant times `1/y` for `y ≥ 1`. -/
theorem exists_norm_dedekindZetaRieszGammaCorrection_le :
    ∃ C : ℝ, ∀ y ≥ 1, ‖dedekindZetaRieszGammaCorrection K y‖ ≤ C * y ^ (-1 : ℝ) := by
  obtain ⟨A, hA⟩ := exists_norm_rieszGammaCorrection_le zero_lt_two zero_lt_two
  obtain ⟨B, hB⟩ := exists_norm_rieszGammaCorrection_le zero_lt_one zero_lt_one
  refine ⟨nrRealPlaces K * |A| + nrComplexPlaces K * B, fun y hy ↦ ?_⟩
  have hR : ‖rieszGammaCorrection 2 2 y‖ ≤ |A| * y ^ (-1 : ℝ) := by
    refine (hA y hy).trans (mul_le_mul (le_abs_self A) ?_ (by positivity) (abs_nonneg A))
    exact Real.rpow_le_rpow_of_exponent_le hy (by norm_num)
  rw [dedekindZetaRieszGammaCorrection_def, add_mul]
  refine (norm_add_le ..).trans (add_le_add ?_ ?_)
  · rw [norm_mul, Complex.norm_natCast, mul_assoc]
    gcongr
  · rw [norm_mul, Complex.norm_natCast, mul_assoc]
    gcongr
    exact hB y hy

/-- The Mellin integral of the negative gamma contribution converges absolutely for `Re s > −1`. -/
theorem integrableOn_dedekindZetaRieszGammaCorrection_mul_cpow {s : ℂ} (hs : -1 < s.re) :
    IntegrableOn (fun y : ℝ ↦ dedekindZetaRieszGammaCorrection K y * (y : ℂ) ^ (-s - 1))
      (Ioi 1) := by
  have hR := integrableOn_rieszGammaCorrection_mul_cpow (s := s) zero_lt_two zero_lt_two
    (by linarith : -2 < s.re)
  have hC := integrableOn_rieszGammaCorrection_mul_cpow zero_lt_one zero_lt_one hs
  simpa only [dedekindZetaRieszGammaCorrection_def, add_mul, mul_assoc, IntegrableOn, Pi.add_def]
    using (hR.const_mul (nrRealPlaces K : ℂ)).add (hC.const_mul (nrComplexPlaces K : ℂ))

/-- The gamma factor's regular logarithmic derivative after removing the pole at zero. -/
private noncomputable def regularGammaLogDeriv (s : ℂ) : ℂ :=
  nrRealPlaces K * logDeriv Gammaℝ (s + 2) + nrComplexPlaces K * logDeriv Gammaℂ (s + 1)

private theorem regularGammaLogDeriv_eq {s : ℂ} (hs : -1 < s.re) (h₀ : s ≠ 0) :
    regularGammaLogDeriv K s = logDeriv (dedekindZetaData K).gammaFactor s +
      (↑(nrRealPlaces K) + ↑(nrComplexPlaces K)) / s := by
  have hC := ne_neg_natCast_of_neg_one_lt_re_of_ne_zero hs h₀
  have hR (n : ℕ) : s ≠ -(2 * n) := by simpa using hC (2 * n)
  have hhalf (n : ℕ) : s / 2 ≠ -(n : ℂ) := by
    intro h
    exact hR n (by linear_combination 2 * h)
  have hsR : Gammaℝ s ≠ 0 := by simpa [Gammaℝ_eq_zero_iff] using hR
  have hsC : Gammaℂ s ≠ 0 := by simpa [Gammaℂ_eq_zero_iff] using hC
  have heq : (dedekindZetaData K).gammaFactor =
      fun z ↦ Gammaℝ z ^ nrRealPlaces K * Gammaℂ z ^ nrComplexPlaces K :=
    funext (dedekindZetaData_gammaFactor K)
  have h2 : (s + 2) / 2 = s / 2 + 1 := by ring
  rw [heq, logDeriv_fun_mul (f := fun z ↦ Gammaℝ z ^ nrRealPlaces K)
    (g := fun z ↦ Gammaℂ z ^ nrComplexPlaces K) s (pow_ne_zero _ hsR) (pow_ne_zero _ hsC)
    ((differentiableAt_Gammaℝ hsR).pow _) ((differentiableAt_Gammaℂ hsC).pow _),
    logDeriv_fun_pow (differentiableAt_Gammaℝ hsR), logDeriv_fun_pow (differentiableAt_Gammaℂ hsC)]
  simp only [regularGammaLogDeriv, logDeriv_Gammaℝ hR, logDeriv_Gammaℂ hC,
    logDeriv_Gammaℝ (s := s + 2) (fun n ↦ by
      simpa using ne_neg_natCast_of_re_pos (by simp; linarith : 0 < (s + 2).re) (2 * n)),
    logDeriv_Gammaℂ (ne_neg_natCast_of_re_pos (by simp; linarith : 0 < (s + 1).re)), h2,
    digamma_apply_add_one _ hC, digamma_apply_add_one _ hhalf]
  ring

private theorem regularGammaLogDeriv_zero :
    regularGammaLogDeriv K 0 = logDerivFinitePart (dedekindZetaData K).gammaFactor 0 := by
  have hord : (meromorphicOrderAt (dedekindZetaData K).gammaFactor 0).untop₀ =
      -(↑(nrRealPlaces K) + ↑(nrComplexPlaces K) : ℤ) := by
    rw [funext (dedekindZetaData_gammaFactor K)]
    simpa using congrArg WithTop.untop₀
      (meromorphicOrderAt_Gammaℝ_pow_mul_Gammaℂ_pow_one_sub_nat (nrRealPlaces K)
        (nrComplexPlaces K) (n := 1) le_rfl)
  have ha : AnalyticAt ℂ (regularGammaLogDeriv K) 0 := by
    have hR₂ := analyticAt_logDeriv_Gammaℝ (Gammaℝ_ne_zero_of_re_pos (s := 2) (by norm_num))
    have hC₁ := analyticAt_logDeriv_Gammaℂ (Gammaℂ_ne_zero_of_re_pos (s := 1) (by norm_num))
    have hR' : AnalyticAt ℂ (fun z : ℂ ↦ logDeriv Gammaℝ (z + 2)) 0 :=
      AnalyticAt.comp (g := logDeriv Gammaℝ) (by simpa only [zero_add] using hR₂)
        (f := fun z : ℂ ↦ z + 2)
        (by fun_prop)
    have hC' : AnalyticAt ℂ (fun z : ℂ ↦ logDeriv Gammaℂ (z + 1)) 0 :=
      AnalyticAt.comp (g := logDeriv Gammaℂ) (by simpa only [zero_add] using hC₁)
        (f := fun z : ℂ ↦ z + 1)
        (by fun_prop)
    exact (analyticAt_const.mul hR').add (analyticAt_const.mul hC')
  refine (ha.logDerivFinitePart_eq ?_).symm
  have hnear : ∀ᶠ z : ℂ in 𝓝 0, -1 < z.re :=
    (isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (0 : ℂ) ∈ {z | -1 < z.re})
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hz₀
  rw [regularGammaLogDeriv_eq K hz hz₀, hord]
  push_cast
  ring

/-- Multiply the Mellin integral of the negative gamma contribution by `s(s−1)` to obtain
`logDeriv` of the gamma factor with its pole at zero and its affine interpolant removed.
The constant in the interpolant is the finite part at zero, not the value of `logDeriv` there. -/
theorem mul_integral_dedekindZetaRieszGammaCorrection {s : ℂ} (hs : -1 < s.re) (h₀ : s ≠ 0) :
    s * (s - 1) * (∫ y : ℝ in Ioi 1,
        dedekindZetaRieszGammaCorrection K y * (y : ℂ) ^ (-s - 1)) =
      logDeriv (dedekindZetaData K).gammaFactor s -
        (1 - s) * logDerivFinitePart (dedekindZetaData K).gammaFactor 0 -
        s * logDeriv (dedekindZetaData K).gammaFactor 1 +
        (↑(nrRealPlaces K) + ↑(nrComplexPlaces K)) * (s⁻¹ - s) := by
  have hsR : -2 < s.re := by linarith
  have hR := integrableOn_rieszGammaCorrection_mul_cpow zero_lt_two zero_lt_two hsR
  have hC := integrableOn_rieszGammaCorrection_mul_cpow zero_lt_one zero_lt_one hs
  have hM : s * (s - 1) * (∫ y : ℝ in Ioi 1,
      dedekindZetaRieszGammaCorrection K y * (y : ℂ) ^ (-s - 1)) =
      regularGammaLogDeriv K s - (1 - s) * regularGammaLogDeriv K 0 -
        s * regularGammaLogDeriv K 1 := by
    simp only [dedekindZetaRieszGammaCorrection_def, add_mul, mul_assoc]
    rw [integral_add (hR.const_mul _) (hC.const_mul _), integral_const_mul, integral_const_mul]
    simp only [regularGammaLogDeriv, zero_add]
    have hReal := mul_integral_rieszGammaCorrection_eq_logDeriv_Gammaℝ zero_lt_two hsR
    have hComplex := mul_integral_rieszGammaCorrection_eq_logDeriv_Gammaℂ zero_lt_one hs
    simp only [ofReal_ofNat, ofReal_one] at hReal hComplex
    linear_combination (nrRealPlaces K : ℂ) * hReal + (nrComplexPlaces K : ℂ) * hComplex
  rw [hM, regularGammaLogDeriv_eq K hs h₀, regularGammaLogDeriv_zero K,
    regularGammaLogDeriv_eq K (s := 1) (by norm_num) one_ne_zero]
  simp only [div_eq_mul_inv]
  ring

end TauCeti.LFunctions
