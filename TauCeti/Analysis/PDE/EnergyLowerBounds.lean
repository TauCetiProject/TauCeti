/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Group.Prod
public import TauCeti.Analysis.PDE.EnergyForm.Basic

/-!
# Pointwise diagonal lower bounds for divergence-form energy integrands

The pointwise energy integrand of a divergence-form operator acts on jets in
`ℝ × EuclideanSpace ℝ n`. With principal lower bound `λ`, drift bound `β`, and mass floor
`μ`, its diagonal satisfies the Young-inequality estimate
`(λ - ε)‖∇u‖² + (μ - β²/(4ε))|u|² ≤ energyIntegrand A b c U U` for every `ε > 0`.
Taking `ε = λ/2` gives the explicit product-norm bound
`min (λ/2) (μ - β²/(2λ)) · ‖U‖² ≤ energyIntegrand A b c U U` when `λ > 0`.
The mass floor may have either sign; when it dominates the drift defect, the bound is
nonnegative.

These estimates feed the integrated inequalities in
`TauCeti.Analysis.PDE.EnergyForm.Integrated.Basic`. Coercivity for Lax--Milgram requires
bounds for the integrated form on a complete inner-product space.

The theorems take a single principal coefficient `A`, drift coefficient `b₀`, and mass
coefficient `c₀`, together with their pointwise bounds. For a coefficient field satisfying
`UniformlyEllipticOn Ω a λ Λ`, use the pointwise specializations in
`TauCeti.Analysis.PDE.Ellipticity.Energy` at a point `x ∈ Ω`. Symmetry of the zero-drift
integrand is recorded separately in `TauCeti.Analysis.PDE.SymmetricEnergy`.

The estimates follow the standard Young-inequality absorption argument in the energy method,
as in Evans, *Partial Differential Equations*, Chapter 6.

## Main declarations

* `TauCeti.PDE.garding_energyIntegrand_self_of_mass_lower_bound_of_bounds_with_parameter`:
  pointwise Gårding lower bound with a mass floor and a free positive Young parameter.
* `TauCeti.PDE.garding_energyIntegrand_self_of_mass_lower_bound_of_bounds`: the choice `ε = λ/2`.
* `TauCeti.PDE.min_diagonal_lower_bound_mul_norm_sq_le_energyIntegrand_self`: explicit
  diagonal product-norm estimate, allowing a signed mass floor.
* `TauCeti.PDE.min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self`: zero-drift
  diagonal lower bound from a nonnegative principal lower bound and an arbitrary mass.
* `TauCeti.PDE.mul_norm_snd_sq_le_energyIntegrand_zero_drift_self`: the zero-drift energy
  dominates the squared gradient component when the mass is nonnegative.
-/

public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {n : Type*} [Fintype n]

/-- Local classical decidable equality for finite coordinate indices in lower-bound proofs. -/
noncomputable local instance energyLowerBoundsDecidableEq : DecidableEq n := Classical.decEq n

variable {lam mu beta : ℝ}

/-- A mass floor and a free positive Young parameter give the diagonal lower bound
`(λ - ε)‖∇u‖² + (μ - β²/(4ε))|u|²`. Both coefficients may have either sign. -/
lemma garding_energyIntegrand_self_of_mass_lower_bound_of_bounds_with_parameter
    {eps : ℝ} (heps : 0 < eps)
    {A : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    (lam - eps) * ‖U.2‖ ^ 2 + (mu - beta ^ 2 / (4 * eps)) * U.1 ^ 2
      ≤ energyIntegrand A b₀ c₀ U U := by
  have hgard := garding_energyIntegrand_self_of_bounds_with_parameter heps hA hb
    (sub_nonneg.mpr hc) U
  rw [energyIntegrand_self] at hgard ⊢
  linarith

/-- Pointwise lower bound for the energy integrand with bounded drift and a mass lower bound.

If the principal part has quadratic lower bound `λ‖ξ‖²`, the drift satisfies `‖b₀‖ ≤ β`, and
the mass coefficient satisfies `μ ≤ c₀`, then the diagonal of the jet form is bounded below by
`(λ/2)‖∇u‖² + (μ − β²/2λ)|u|²`. -/
lemma garding_energyIntegrand_self_of_mass_lower_bound_of_bounds (hlam : 0 < lam)
    {A : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    lam / 2 * ‖U.2‖ ^ 2 + (mu - beta ^ 2 / (2 * lam)) * U.1 ^ 2
      ≤ energyIntegrand A b₀ c₀ U U := by
  convert garding_energyIntegrand_self_of_mass_lower_bound_of_bounds_with_parameter
    (half_pos hlam) hA hb hc U using 1
  ring

/-- The mass-floor Gårding lower bound implies the explicit diagonal estimate with constant
`min (λ / 2) (μ - β² / (2λ))`, allowing the second coefficient to have either sign. -/
lemma min_diagonal_lower_bound_mul_norm_sq_le_energyIntegrand_self (hlam : 0 < lam)
    {A : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀)
    (U : ℝ × EuclideanSpace ℝ n) :
    min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U‖ ^ 2
      ≤ energyIntegrand A b₀ c₀ U U := by
  have hnorm := U.min_mul_norm_sq_le_add
    (a := mu - beta ^ 2 / (2 * lam)) (b := lam / 2)
    ((half_pos hlam).le.trans (le_max_right _ _))
  rw [min_comm, add_comm, Real.norm_eq_abs, sq_abs] at hnorm
  exact hnorm.trans
    (garding_energyIntegrand_self_of_mass_lower_bound_of_bounds hlam hA hb hc U)

/-- Zero-drift diagonal lower bound from a nonnegative principal quadratic lower bound
and an arbitrary mass coefficient. -/
lemma min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self {A : Matrix n n ℝ}
    {c₀ : ℝ} (hlam : 0 ≤ lam) (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (U : ℝ × EuclideanSpace ℝ n) :
    min lam c₀ * ‖U‖ ^ 2 ≤ energyIntegrand A 0 c₀ U U := by
  have hprod := U.min_mul_norm_sq_le_add (a := c₀) (b := lam)
    (hlam.trans (le_max_right _ _))
  have hA' := hA U.2
  rw [energyIntegrand_self]
  simp only [inner_zero_left, zero_mul, add_zero]
  rw [min_comm, add_comm, Real.norm_eq_abs, sq_abs] at hprod
  exact hprod.trans (add_le_add hA' le_rfl)

/-- A zero-drift energy density dominates the squared gradient component when the principal
quadratic form has lower bound `λ` and the mass coefficient is nonnegative. -/
lemma mul_norm_snd_sq_le_energyIntegrand_zero_drift_self {A : Matrix n n ℝ} {c₀ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hc : 0 ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    lam * ‖U.2‖ ^ 2 ≤ energyIntegrand A 0 c₀ U U := by
  rw [energyIntegrand_self]
  simp only [inner_zero_left, zero_mul, add_zero]
  exact (hA U.2).trans (le_add_of_nonneg_right (mul_nonneg hc (sq_nonneg _)))

/-- Explicit diagonal lower bound for the shifted Laplacian jet form with arbitrary mass. -/
lemma min_one_mass_mul_norm_sq_le_energyIntegrand_one_zero_mass_self {c : ℝ}
    (U : ℝ × EuclideanSpace ℝ n) :
    min 1 c * ‖U‖ ^ 2 ≤ energyIntegrand (1 : Matrix n n ℝ) 0 c U U :=
  min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self zero_le_one
    (by intro ξ; simp) U

end PDE

end TauCeti
