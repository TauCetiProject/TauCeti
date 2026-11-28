/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.BoundedCoefficients
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.DedekindZeta.Basic
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.DedekindZeta.ExpBound
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.Basic

/-!
# Logarithmic bounds for Euler products

On the half-plane of absolute convergence, the logarithm of the modulus of an Euler product
with local coefficients of modulus at most one is bounded in absolute value by the logarithm
of the Dedekind zeta function on the real axis. This gives exponential decay in the real part,
in particular for the unitary L-factors in consecutive-rank Hermitian mass ratios.

The mass-ratio application is `New.abs_log_mass_ratio_sub_le` in
`grh/src/Lib/SiegelWeil/OneVector/SiegelClassSum.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at `72fead1`.
-/

public section

open Complex IsDedekindDomain NumberField

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- The Dedekind zeta function bounds the absolute logarithm of the modulus of any Euler
product with coefficients of modulus at most one, on the half-plane `Re s > 1`. -/
theorem abs_log_norm_primeEulerProduct_le_log_dedekindZeta
    {a : HeightOneSpectrum (𝓞 K) → ℂ} (ha : ∀ P, ‖a P‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    |Real.log ‖primeEulerProduct a s‖| ≤ Real.log (dedekindZeta K s.re).re := by
  let F := fun P : HeightOneSpectrum (𝓞 K) ↦ -log (1 - a P / (Ideal.absNorm P.asIdeal : ℂ) ^ s)
  let B := fun P : HeightOneSpectrum (𝓞 K) ↦ -Real.log (1 - (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re))
  have hsum := Complex.hasSum_re (summable_neg_log_one_sub_div_absNorm_cpow ha hs).hasSum
  have hB := summable_neg_log_one_sub_absNorm_rpow (K := K) hs
  have hlocal (P : HeightOneSpectrum (𝓞 K)) : |(F P).re| ≤ B P := by
    let z := a P / (Ideal.absNorm P.asIdeal : ℂ) ^ s
    let r := (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re)
    have hzr : ‖z‖ ≤ r := norm_div_absNorm_cpow_le_rpow_neg (ha P)
    have hr : r ≤ 1 / 2 := P.absNorm_rpow_neg_le_half hs.le
    have hlo : 1 - r ≤ ‖1 - z‖ := by
      have hh := norm_sub_norm_le (1 : ℂ) z
      rw [norm_one] at hh
      linarith
    have hhi : ‖1 - z‖ ≤ 1 + r := (norm_sub_le _ _).trans (by simpa using hzr)
    have hp : 0 < 1 - r := by linarith
    have hhi' : ‖1 - z‖ ≤ (1 - r)⁻¹ := hhi.trans (by
      rw [← one_div, le_div_iff₀ hp]
      nlinarith [sq_nonneg r])
    have hleft := Real.log_le_log hp hlo
    have hright := Real.log_le_log (hp.trans_le hlo) hhi'
    rw [Real.log_inv] at hright
    simpa only [F, B, z, r, neg_re, log_re, abs_neg] using
      (abs_le.mpr ⟨by linarith, hright⟩ :
        |Real.log ‖1 - z‖| ≤ -Real.log (1 - r))
  rw [primeEulerProduct_eq_exp ha hs, norm_exp, Real.log_exp,
    log_dedekindZeta_re_eq_tsum_neg_log_one_sub hs, ← hsum.tsum_eq]
  refine abs_le.mpr ⟨?_, ?_⟩
  · rw [← tsum_neg]
    exact hB.neg.tsum_le_tsum (fun P ↦ (abs_le.mp (hlocal P)).1) hsum.summable
  · exact hsum.summable.tsum_le_tsum (fun P ↦ (abs_le.mp (hlocal P)).2) hB

namespace UnitaryIdealWeight

/-- The logarithm of the modulus of a unitary ideal L-series is bounded in absolute value by
`log ζ_K(Re s)` on `Re s > 1`, including when some Euler factors are omitted. -/
theorem abs_log_norm_LSeries_le_log_dedekindZeta (χ : UnitaryIdealWeight K) {s : ℂ}
    (hs : 1 < s.re) :
    |Real.log ‖LSeries (normCoeff K χ.toIdealArithmeticFunction) s‖| ≤
      Real.log (dedekindZeta K s.re).re := by
  have hχ (P : HeightOneSpectrum (𝓞 K)) : ‖χ.val P.asIdeal‖ ≤ 1 := χ.norm_le_one _
  have hsum := summable_idealTerm_of_unitary_of_one_lt_re χ hs
  rw [χ.toIdealArithmeticFunction_eq_val] at hsum ⊢
  rw [← χ.val.exp_tsum_neg_log_one_sub_eq_LSeries hsum, ← primeEulerProduct_eq_exp hχ hs]
  exact abs_log_norm_primeEulerProduct_le_log_dedekindZeta hχ hs

/-- In `Re s ≥ 2` the logarithm of the modulus of a unitary ideal L-series decays
exponentially, uniformly in the character and the imaginary part. -/
theorem abs_log_norm_LSeries_le_two_rpow_mul_finrank (χ : UnitaryIdealWeight K) {s : ℂ}
    (hs : 2 ≤ s.re) :
    |Real.log ‖LSeries (normCoeff K χ.toIdealArithmeticFunction) s‖| ≤
      2 ^ (3 - s.re) * Module.finrank ℚ K :=
  (χ.abs_log_norm_LSeries_le_log_dedekindZeta (one_lt_two.trans_le hs)).trans
    (log_dedekindZeta_re_le_two_rpow_mul_finrank hs)

end UnitaryIdealWeight

end TauCeti
