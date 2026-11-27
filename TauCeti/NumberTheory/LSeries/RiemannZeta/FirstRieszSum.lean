/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Pow.Windows.Bounds
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz
public import TauCeti.NumberTheory.LSeries.RiemannZeta.ExplicitFormula
import TauCeti.Analysis.MellinTransform.Uniqueness
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Growth
import TauCeti.NumberTheory.LSeries.RiemannZeta.RiemannHypothesis

/-!
# The first Riesz explicit formula for the Riemann zeta function

Identify the smoothed von Mangoldt sum, with its main term subtracted, with the zero side
`riemannZetaRieszZeroSide`. A zero-free right half-plane then gives a pointwise power bound,
and under the Riemann hypothesis this gives one-sided bounds on windows of every ratio.

The remainder uses the normalization of Levent Alpöge's `Formalism.Gz`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open Complex Filter Set

namespace TauCeti.PrimitiveDirichletCharacter

open LFunctions

/-- The first Riesz remainder of the conductor-one character equals the sum over the
nontrivial zeros of zeta, the strictly negative trivial-zero correction, and `log (2π)`.
The formula holds at the endpoint `y = 1` as well. -/
theorem rieszRemainder_one_eq_riemannZetaRieszZeroSide {y : ℝ} (hy : 1 ≤ y) :
    (1 : PrimitiveDirichletCharacter).rieszRemainder y = riemannZetaRieszZeroSide y := by
  have htwo : 1 < (2 : ℂ).re := by norm_num
  refine eqOn_Ici_of_mellin_integral_Ioi_eq_on_verticalLine (c := 2) zero_le_one
    (continuous_rieszRemainder 1).continuousOn continuousOn_riemannZetaRieszZeroSide ?_ ?_ ?_ hy
  · simpa only [ofReal_ofNat, smul_eq_mul, mul_comm] using
      (1 : PrimitiveDirichletCharacter).integrableOn_rieszRemainder_mul_cpow htwo
  · simpa only [ofReal_ofNat, smul_eq_mul, mul_comm] using
      integrableOn_riemannZetaRieszZeroSide_mul_cpow htwo
  · intro s hs
    have hs' : 1 < s.re := hs.symm ▸ (one_lt_two : (1 : ℝ) < 2)
    simp_rw [smul_eq_mul, mul_comm (_ ^ _)]
    rw [integral_rieszRemainder_mul_cpow _ hs', integral_riemannZetaRieszZeroSide_mul_cpow hs',
      LFunction_character_one]

/-- A zero-free half-plane `Re s > σ` for zeta bounds the first Riesz remainder by
`C * y ^ max σ 0` for all `y ≥ 1`. The maximum with zero accounts for the constant term
in the explicit formula. -/
theorem exists_norm_rieszRemainder_one_le_rpow {σ : ℝ}
    (hσ : ZeroFreeRightOf σ riemannZeta) :
    ∃ C : ℝ, ∀ y ≥ 1, ‖(1 : PrimitiveDirichletCharacter).rieszRemainder y‖ ≤ C * y ^ max σ 0 := by
  have hz (ρ : ℂ) (hρ : zetaEntireCompletion ρ = 0) : ρ.re ≤ σ := by
    have hstrip := re_mem_Ioo_of_zetaEntireCompletion_eq_zero hρ
    have h₀ := Complex.ne_zero_of_re_pos hstrip.1
    have h₁ : ρ ≠ 1 := by rintro rfl; simpa using hstrip.2
    have hζ : riemannZeta ρ = 0 := by
      rw [zetaEntireCompletion_eq_mul h₀ h₁, mul_eq_zero] at hρ
      have hΛ := hρ.resolve_left (mul_ne_zero h₀ (sub_ne_zero.mpr h₁))
      rw [riemannZeta_def_of_ne_zero h₀, hΛ, zero_div]
    exact not_lt.mp fun h ↦ (zeroFreeRightOf_riemannZeta_iff.mp hσ ρ h) hζ
  obtain ⟨D, hD⟩ := exists_norm_rieszGammaCorrection_le (a := 2) (d := 2)
    (by norm_num) (by norm_num)
  have hD₀ : 0 ≤ D := (norm_nonneg _).trans (by simpa using hD 1 le_rfl)
  let C := ∑' ρ : (MeromorphicOn.divisor zetaEntireCompletion univ).support,
    ‖((MeromorphicOn.divisor zetaEntireCompletion univ ρ).toNat : ℂ) / (ρ * (1 - ρ))‖
  refine ⟨C + D + ‖(Real.log (2 * Real.pi) : ℂ)‖, fun y hy ↦ ?_⟩
  have hZ := orderLE_zetaEntireCompletion.norm_rieszZeroSeries_le
    differentiable_zetaEntireCompletion (by norm_num)
    (σ := max σ 0) (fun ρ hρ ↦ (hz ρ hρ).trans (le_max_left ..)) hy
  have hG := (hD y hy).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hy ((by norm_num : (-2 : ℝ) ≤ 0).trans
      (le_max_right σ 0))) hD₀)
  have hconst := le_mul_of_one_le_right (norm_nonneg (Real.log (2 * Real.pi) : ℂ))
    (Real.one_le_rpow hy (le_max_right σ 0))
  rw [rieszRemainder_one_eq_riemannZetaRieszZeroSide hy, riemannZetaRieszZeroSide_def]
  rw [add_mul, add_mul]
  exact (norm_add₃_le.trans (add_le_add (add_le_add hZ hG) hconst))

/-- The Riemann hypothesis gives the conductor-one remainder an upper bound of
`y ^ (1 / 2 + ε)` on arbitrarily far-out scale windows of any ratio. -/
theorem hasWindows_rieszRemainder_one_of_riemannHypothesis (hRH : RiemannHypothesis)
    {ε : ℝ} (hε : 0 < ε) (L : ℝ) :
    HasWindows {y | ((1 : PrimitiveDirichletCharacter).rieszRemainder y).re ≤
      y ^ ((1 : ℝ) / 2 + ε)} L := by
  obtain ⟨C, hC⟩ := exists_norm_rieszRemainder_one_le_rpow
    (riemannHypothesis_iff_zeroFreeRightOf.mp hRH)
  have h : ∀ᶠ y : ℝ in atTop, ((1 : PrimitiveDirichletCharacter).rieszRemainder y).re ≤
      C * y ^ ((1 : ℝ) / 2) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    refine (re_le_norm _).trans ?_
    simpa only [max_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hC y hy
  exact hasWindows_rpow_bound_of_eventually_le h (by linarith) L

end TauCeti.PrimitiveDirichletCharacter
