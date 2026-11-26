/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.GaussNorm
public import TauCeti.RingTheory.PowerSeries.Exp.Padic.Basic
import Mathlib.Analysis.Normed.Algebra.Ultra

/-!
# Integrality of the exponential of a multivariate power series

Let `K` be a normed field extending `ℚ_[p]` isometrically and `c : σ → ℝ` nonnegative radii. If a
multivariate power series `B` over `K` has no constant term and its weighted coefficients satisfy
`‖coeff m B‖ * ∏ᵢ cᵢ ^ mᵢ ≤ p ^ (-1 / (p - 1))`, then the weighted coefficients of `exp(B)`, the
substitution `(PowerSeries.exp K).subst B`, are at most `1`. In valuation language, with radii
`cᵢ = p ^ (-rᵢ)`: if `v_p(coeff m B) ≥ 1 / (p - 1) - ∑ᵢ mᵢ rᵢ` for all `m`, then
`v_p(coeff n exp(B)) ≥ -∑ᵢ nᵢ rᵢ` for all `n`.

The bound holds coefficient by coefficient: the coefficient of `exp(B)` at `n` depends only on
those of `B` at the exponents `m ≤ n`, so the bound at `n` assumes the bound for `B` only there.
This gives the form read up to an exponent `κ` (all `n ≤ κ`) as well.

In Gauss-norm form, if `B` has a Gauss norm at `c` of size at most `p ^ (-1 / (p - 1))`, then
`exp(B)` has a Gauss norm at `c` of size at most `1`. A bound on the Gauss norm alone would not
do: Mathlib's Gauss norm of a series without one, such as `exp(X)` at radius `1`, is `0`.

The proof applies the ultrametric substitution bound `PowerSeries.norm_coeff_subst_mul_prod_le`
to the exponential series, whose coefficients `1 / j!` satisfy `‖1 / j!‖ p ^ (-j / (p - 1)) ≤ 1`
by Legendre's bound `v_p(j!) ≤ j / (p - 1)` (`PowerSeries.gaussNorm_rescale_exp`).

## Main results

* `PowerSeries.norm_coeff_subst_exp_mul_prod_le_one`: the coefficientwise bound, at each exponent
  `n` from the bound on `B` at the exponents `m ≤ n`.
* `PowerSeries.hasGaussNorm_subst_exp`, `PowerSeries.gaussNorm_subst_exp_le_one`: the Gauss-norm
  form.

## Provenance

`PowerSeries.norm_coeff_subst_exp_mul_prod_le_one` is adapted from `New.norm_coeff_expSubst_le_one`
(file `src/Lib/General/Algebra/SeriesBounds.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), which treats
`ℂ_[p]` at radius `1`, with the bound read up to a total degree; the generalisation to any normed
field extending `ℚ_[p]`, to arbitrary radii, to the truncation below an exponent and the
Gauss-norm form are new here.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., GTM 58,
  Chapter IV, §1.
-/

public section

namespace PowerSeries

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K] [Algebra ℚ K] [NormedAlgebra ℚ_[p] K]
  {σ : Type*} {c : σ → ℝ}

/-- **Integrality of `exp(B)`, coefficientwise.** If `B` has no constant term and its weighted
coefficients `‖coeff m B‖ * ∏ᵢ cᵢ ^ mᵢ` are at most `p ^ (-1 / (p - 1))` for `m ≤ n`, then the
weighted coefficient of `exp(B)` at `n` is at most `1`. -/
theorem norm_coeff_subst_exp_mul_prod_le_one (hc : 0 ≤ c) {B : MvPowerSeries σ K}
    (hB : MvPowerSeries.constantCoeff B = 0) {n : σ →₀ ℕ}
    (hBn : ∀ m ≤ n, ‖MvPowerSeries.coeff m B‖ * m.prod (c · ^ ·) ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    ‖MvPowerSeries.coeff n ((exp K).subst B)‖ * n.prod (c · ^ ·) ≤ 1 := by
  have : IsUltrametricDist K := .of_normedAlgebra ℚ_[p]
  have hρ : 0 ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) := by positivity
  -- The coefficients `1 / j!` of the exponential satisfy `‖1 / j!‖ p ^ (-j / (p - 1)) ≤ 1`.
  have h := hasGaussNorm_rescale_exp (p := p) (x := (1 : K)) hρ (by simp)
  have h1 := gaussNorm_rescale_exp (p := p) (x := (1 : K)) hρ (by simp)
  rw [rescale_one, RingHom.id_apply] at h h1
  exact norm_coeff_subst_mul_prod_le hc (.of_constantCoeff_zero hB) hBn
    fun j ↦ (le_gaussNorm _ _ _ h j).trans_eq h1

/-- **Integrality of `exp(B)`.** If `B` has no constant term and a Gauss norm at radii `c` of size
at most `p ^ (-1 / (p - 1))`, then `exp(B)` has a Gauss norm at `c`. -/
theorem hasGaussNorm_subst_exp (hc : 0 ≤ c) {B : MvPowerSeries σ K}
    (hB : MvPowerSeries.constantCoeff B = 0) (hB' : MvPowerSeries.HasGaussNorm norm c B)
    (hBρ : MvPowerSeries.gaussNorm norm c B ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    MvPowerSeries.HasGaussNorm norm c ((exp K).subst B) :=
  ⟨1, Set.forall_mem_range.2 fun _ ↦ norm_coeff_subst_exp_mul_prod_le_one hc hB
    fun m _ ↦ (MvPowerSeries.le_gaussNorm _ _ _ hB' m).trans hBρ⟩

/-- **Integrality of `exp(B)`.** If `B` has no constant term and a Gauss norm at radii `c` of size
at most `p ^ (-1 / (p - 1))`, then the Gauss norm of `exp(B)` at `c` is at most `1`. -/
theorem gaussNorm_subst_exp_le_one (hc : 0 ≤ c) {B : MvPowerSeries σ K}
    (hB : MvPowerSeries.constantCoeff B = 0) (hB' : MvPowerSeries.HasGaussNorm norm c B)
    (hBρ : MvPowerSeries.gaussNorm norm c B ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    MvPowerSeries.gaussNorm norm c ((exp K).subst B) ≤ 1 :=
  ciSup_le fun _ ↦ norm_coeff_subst_exp_mul_prod_le_one hc hB
    fun m _ ↦ (MvPowerSeries.le_gaussNorm _ _ _ hB' m).trans hBρ

end PowerSeries
