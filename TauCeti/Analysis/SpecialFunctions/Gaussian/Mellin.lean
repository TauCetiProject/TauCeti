/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Real.Pi.Bounds
import TauCeti.Analysis.MellinTransform

/-!
# Mellin integrals of weighted Gaussians

A monomial times `exp(-π t²)` has an explicit exponential majorant. Its Mellin transform is
half the archimedean gamma factor at the shifted argument. These facts give the elementary
bounds and the normalization of Mellin integrals of Gaussian theta sums.
-/

public section

open Complex

namespace TauCeti

/-- The monomial of degree `j` times the standard Gaussian is bounded in absolute value by
`j! exp(1 - |x|)`. -/
theorem abs_pow_mul_exp_neg_pi_mul_sq_le (j : ℕ) (x : ℝ) :
    |x ^ j * Real.exp (-Real.pi * x ^ 2)| ≤ (j.factorial : ℝ) * Real.exp 1 * Real.exp (-|x|) := by
  rw [abs_mul, abs_pow, Real.abs_exp, ← sq_abs x]
  calc
    _ ≤ (j.factorial : ℝ) * Real.exp |x| * Real.exp (-Real.pi * |x| ^ 2) := by
      gcongr
      simpa [mul_comm] using (div_le_iff₀ (by positivity : 0 < (j.factorial : ℝ))).mp
        (Real.pow_div_factorial_le_exp |x| (abs_nonneg x) j)
    _ = (j.factorial : ℝ) * Real.exp (|x| - Real.pi * |x| ^ 2) := by
      rw [mul_assoc, ← Real.exp_add, neg_mul, sub_eq_add_neg]
    _ ≤ (j.factorial : ℝ) * Real.exp (1 + -|x|) := by
      gcongr
      have hπ : 0 ≤ Real.pi - 1 := by linarith [Real.pi_gt_three]
      nlinarith [sq_nonneg (|x| - 1), mul_nonneg hπ (sq_nonneg |x|)]
    _ = _ := by rw [Real.exp_add, mul_assoc]

/-- The Mellin transform of a Gaussian times `t^j` is `Γℝ(s+j)/2` when `Re(s+j) > 0`. -/
theorem hasMellin_pow_mul_exp_neg_pi_mul_sq (j : ℕ) {s : ℂ} (hs : 0 < s.re + j) :
    HasMellin (fun t : ℝ ↦ ((t ^ j * Real.exp (-Real.pi * t ^ 2) : ℝ) : ℂ)) s
      (Gammaℝ (s + j) / 2) := by
  have hz : 0 < (s + (j : ℂ)).re := by simpa using hs
  let f (t : ℝ) : ℂ := Real.exp (-(Real.pi * t))
  have he (t : ℝ) : ((t ^ j * Real.exp (-Real.pi * t ^ 2) : ℝ) : ℂ) =
      (t : ℂ) ^ (j : ℂ) • f (t ^ (2 : ℝ)) := by
    simp [f, cpow_natCast, smul_eq_mul, neg_mul]
  have hi : MellinConvergent f ((s + j) / 2) :=
    mellinConvergent_exp_neg_mul Real.pi_pos (by rw [div_ofNat_re]; exact half_pos hz)
  have hf : mellin f ((s + j) / 2) = Gammaℝ (s + j) := by
    rw [← integral_multHaar_cpow_smul]
    simpa [f, smul_eq_mul] using integral_multHaar_cpow_div_two_mul_exp_neg_pi_mul_sq 1 hz
  simp_rw [he]
  refine ⟨MellinConvergent.cpow_smul.mpr ((MellinConvergent.comp_rpow (by norm_num)).mpr hi), ?_⟩
  rw [mellin_cpow_smul, mellin_comp_rpow f _ 2, ofReal_ofNat, hf]
  norm_num [Complex.real_smul, smul_eq_mul, div_eq_mul_inv, mul_comm]

end TauCeti
