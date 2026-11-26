/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.LaplaceTransform.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Basic
import TauCeti.Analysis.LaplaceTransform.Elementary
import TauCeti.Analysis.LaplaceTransform.Mellin
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Riesz.Mellin

/-!
# Laplace transforms of first Riesz sums

The logarithmic variable turns the Mellin transform of a first Riesz sum into a one-sided
Laplace transform. Dividing the Riesz sum by its length and subtracting an affine main term in
the logarithmic variable shifts the transform by one and subtracts two rational terms. This
normalization is the one used with one-sided bounds for smoothed prime-power counts.

The normalization follows the transform identity `New.integral_primeRemainder` in
`New/Reduction/Zeros/PrimeError` of the shorter GRH formalization
(<https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh>).
-/

public section

namespace TauCeti

/-- In the logarithmic variable, the first Riesz sum has one-sided Laplace transform
`LSeries a s / (s * (s - 1))` on the intersection of the half-plane `1 < s.re` and its
Dirichlet series' region of absolute convergence. -/
theorem hasLaplace_rieszSum_comp_exp {a : ℕ → ℂ} {s : ℂ} (hs : 1 < s.re)
    (ha : LSeriesSummable a s) :
    HasLaplace (fun u ↦ rieszSum a (Real.exp u)) s (LSeries a s / (s * (s - 1))) := by
  apply (hasLaplace_comp_exp_iff (rieszSum a) s _ 0).mpr
  have he : -(s + 1) = -s - 1 := by ring
  simpa only [Real.exp_zero, smul_eq_mul, he, mul_comm] using
    And.intro (integrableOn_rieszSum_mul_cpow hs ha) (integral_rieszSum_mul_cpow hs ha)

/-- Divide a first Riesz sum by its length and subtract a linear term and a constant in the
logarithmic variable. Its Laplace transform at `s - 1` uses the Dirichlet series at `s` and
subtracts the transforms of the two main terms. -/
theorem hasLaplace_normalized_riesz_remainder {a : ℕ → ℂ} {s : ℂ} (hs : 1 < s.re)
    (ha : LSeriesSummable a s) (α c : ℂ) :
    HasLaplace (fun u ↦ rieszSum a (Real.exp u) / (Real.exp u : ℂ) - α * u - c) (s - 1)
      ((LSeries a s / s - α / (s - 1) - c) / (s - 1)) := by
  have hpos : 0 < (s - 1).re := by simpa using sub_pos.mpr hs
  have hnorm : HasLaplace (fun u ↦ rieszSum a (Real.exp u) / (Real.exp u : ℂ)) (s - 1)
      (LSeries a s / (s * (s - 1))) := by
    have he : s - 1 - (-1) = s := by ring
    have h := HasLaplace.cexp_mul_smul (s := s - 1) (w := -1)
      (he.symm ▸ hasLaplace_rieszSum_comp_exp hs ha)
    simpa only [he, Complex.ofReal_exp, mul_neg_one, Complex.exp_neg, smul_eq_mul,
      div_eq_mul_inv, mul_comm] using h
  have hlin := (hasLaplace_pow 1 hpos).const_smul α
  have hconst := hasLaplace_const c hpos
  convert (hnorm.sub hlin).sub hconst using 1
  · ext u
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pow_one]
  · have hs₀ : s ≠ 0 := fun he ↦ (not_lt_of_ge (zero_le_one : (0 : ℝ) ≤ 1))
      (by simpa only [he, Complex.zero_re] using hs)
    have hs₁ : s - 1 ≠ 0 := fun he ↦ by simp [he] at hpos
    simp only [Nat.factorial_one, Nat.cast_one, smul_eq_mul, mul_one_div, one_add_one_eq_two]
    field_simp

end TauCeti
