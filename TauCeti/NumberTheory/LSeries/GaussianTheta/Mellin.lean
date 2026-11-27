/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.LSeries.GaussianTheta

import TauCeti.Analysis.MellinTransform.Basic
import TauCeti.Analysis.MellinTransform.Series

/-!
# Mellin transforms of Gaussian theta series

In the region of absolute convergence of a Dirichlet series, the Mellin transform of its
Gaussian theta kernel is the Dirichlet series times the Mellin transform of one Gaussian.
For a character's Möbius-twisted coefficients the Dirichlet series is the reciprocal of its
L-function. This identity is the starting point for truncating that Mellin integral to
construct a mollifier.

The normalization follows `New.mellin_thetaSeries` and `New.mellin_thetaSeries_moebius`
in `grh/src/Lib/Analytic/DirichletTheta.lean` of [grh-lean], commit `72fead1`.

[grh-lean]: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207
-/

public section

open Complex Set
open scoped ArithmeticFunction.Moebius

namespace TauCeti

/-- The Mellin transform of the unnormalized Gaussian theta kernel converges absolutely
and equals the Gaussian factor times the Dirichlet series. -/
theorem hasMellin_gaussianTheta (j : Fin 2) {c : ℕ → ℂ} {s : ℂ}
    (hs : -(j.val : ℝ) < s.re) (hc : LSeriesSummable c s) :
    HasMellin (gaussianTheta j c) s (gaussianMellin j s * _root_.LSeries c s) := by
  have hGaussian : HasMellin (fun t ↦ (gaussianMonomial j t : ℂ)) s (gaussianMellin j s) :=
    ⟨mellinConvergent_gaussianMonomial hs, by rw [gaussianMellin_def]⟩
  have hweight : Summable fun n : ℕ+ ↦ ‖c n‖ * (n : ℝ) ^ (-s.re) := by
    have hsub : Summable fun n : ℕ+ ↦ ‖LSeries.term c s (n : ℕ)‖ :=
      hc.norm.comp_injective Subtype.val_injective
    refine hsub.congr fun n ↦ ?_
    rw [LSeries.term_of_ne_zero n.ne_zero, norm_div, norm_natCast_cpow_of_pos n.pos,
      Real.rpow_neg (by positivity), div_eq_mul_inv]
  have hdirichlet : (∑' n : ℕ+, c n * ((n : ℕ) : ℂ) ^ (-s)) = _root_.LSeries c s := by
    simp_rw [cpow_neg, ← div_eq_mul_inv, ← LSeries.term_of_ne_zero (PNat.ne_zero _)]
    refine tsum_subtype_eq_of_support_subset (s := {n : ℕ | 0 < n}) fun n hn ↦ ?_
    exact Nat.pos_of_ne_zero fun h ↦ hn (by simp [h])
  have H := hGaussian.tsum_smul_comp_mul_right (a := fun n : ℕ+ ↦ (n : ℝ))
    (fun n ↦ by positivity) hweight
  have htheta : gaussianTheta j c = fun t ↦
      ∑' n : ℕ+, c n • (gaussianMonomial j (t * n) : ℂ) := by
    funext t
    simp only [gaussianTheta_def, smul_eq_mul, mul_comm t]
  rw [← htheta] at H
  simpa only [smul_eq_mul, ofReal_natCast, hdirichlet, mul_comm (gaussianMellin j s)] using H

/-- The square-root normalization shifts the Mellin exponent from `s` to `s - 1/2`,
without changing the Gaussian factor or the Dirichlet series on the right. -/
theorem hasMellin_gaussianThetaSeries (j : Fin 2) {c : ℕ → ℂ} {s : ℂ}
    (hs : -(j.val : ℝ) < s.re) (hc : LSeriesSummable c s) :
    HasMellin (gaussianThetaSeries j c) (s - 1 / 2)
      (gaussianMellin j s * _root_.LSeries c s) := by
  have h := hasMellin_gaussianTheta j hs hc
  have hEq : EqOn (fun t : ℝ ↦ (t : ℂ) ^ (1 / 2 : ℂ) • gaussianTheta j c t)
      (gaussianThetaSeries j c) (Ioi 0) := by
    intro t (ht : 0 < t)
    simp only [gaussianThetaSeries_def, Real.sqrt_eq_rpow, ofReal_cpow ht.le, ofReal_div,
      ofReal_one, ofReal_ofNat, smul_eq_mul]
  refine (hasMellin_congr hEq).mp ⟨?_, ?_⟩
  · rw [MellinConvergent.cpow_smul, sub_add_cancel]
    exact h.1
  · rw [mellin_cpow_smul, sub_add_cancel]
    exact h.2

end TauCeti

namespace DirichletCharacter

open TauCeti

/-- On `Re s > 1`, the Mellin transform of the normalized theta series of the Möbius-twisted
coefficients of `χ`, taken at `s - 1/2`, is the Gaussian factor divided by `L(s, χ)`.
No parity restriction on the Gaussian is needed for this identity. -/
theorem hasMellin_gaussianThetaSeries_moebius {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (j : Fin 2) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (gaussianThetaSeries j (fun n ↦ χ n * μ n)) (s - 1 / 2)
      (gaussianMellin j s / χ.LFunction s) := by
  have hs' : -(j.val : ℝ) < s.re := by linarith [Nat.cast_nonneg (α := ℝ) j.val]
  have hsum : LSeriesSummable (fun n ↦ χ n * μ n) s :=
    χ.LSeriesSummable_mul (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  have hinv : _root_.LSeries (fun n ↦ χ n * μ n) s = (χ.LFunction s)⁻¹ := by
    rw [LFunction_eq_LSeries χ hs]
    exact eq_inv_of_mul_eq_one_right (LSeries.mul_mu_eq_one χ hs)
  simpa only [hinv, div_eq_mul_inv] using hasMellin_gaussianThetaSeries j hs' hsum

end DirichletCharacter
