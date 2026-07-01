/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.UniformEllipticEnergy

/-!
# Coercivity under small bounded principal perturbations

This file records the raw pointwise energy-integrand estimates obtained after adding a
small bounded principal perturbation.  The perturbation bound is deliberately an inline
hypothesis, matching the PDE roadmap's convention for bounded coefficient assumptions.

If `A` has quadratic lower bound `λ` and `P` has bilinear size at most `μ < λ`, then
`A + P` has quadratic lower bound `λ - μ`; the existing pointwise energy coercivity
estimates can therefore be applied with the reduced lower constant.
-/

public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A P : Matrix n n ℝ}
variable {b₀ : EuclideanSpace ℝ n} {c₀ lam Mu beta rho : ℝ}

/-- The explicit coercive diagonal estimate after adding a small bounded principal
perturbation to a coefficient with a quadratic lower bound.

If the perturbation has bilinear bound `μ < λ`, the perturbed coefficient uses lower
ellipticity constant `λ - μ`; the mass floor must dominate the drift defect computed with
that reduced constant. -/
lemma min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_bounded_principal_self
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hMu_lt : Mu < lam)
    (hP : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (P *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    (hb : ‖b₀‖ ≤ beta) (hc : rho ≤ c₀)
    (hrho : beta ^ 2 / (2 * (lam - Mu)) < rho)
    (U : ℝ × EuclideanSpace ℝ n) :
    min ((lam - Mu) / 2) (rho - beta ^ 2 / (2 * (lam - Mu))) * ‖U‖ ^ 2
      ≤ energyIntegrand (A + P) b₀ c₀ U U :=
  min_coercivityConstant_mul_norm_sq_le_energyIntegrand_self (sub_pos.mpr hMu_lt)
    (lower_bound_toQuadraticForm'_add_of_lower_bound hA
      (fun ξ =>
        (neg_le_neg (abs_toQuadraticForm'_le_of_abs_dotProduct_mulVec_le hP ξ)).trans
          (neg_abs_le (P.toQuadraticForm' ξ))))
    hb hc hrho U

/-- Coercivity after adding a small bounded principal perturbation to a coefficient with a
quadratic lower bound. -/
lemma isCoercive_energyIntegrand_add_bounded_principal
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hMu_lt : Mu < lam)
    (hP : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (P *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    (hb : ‖b₀‖ ≤ beta) (hc : rho ≤ c₀)
    (hrho : beta ^ 2 / (2 * (lam - Mu)) < rho) :
    IsCoercive (energyIntegrand (A + P) b₀ c₀) := by
  refine ⟨min ((lam - Mu) / 2) (rho - beta ^ 2 / (2 * (lam - Mu))),
    min_coercivityConstant_pos (sub_pos.mpr hMu_lt) hrho, fun U => ?_⟩
  simpa [pow_two, mul_assoc] using
    min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_bounded_principal_self
      hA hMu_lt hP hb hc hrho U

/-- Zero-drift coercivity after adding a small bounded principal perturbation to a coefficient
with a quadratic lower bound and keeping a positive mass coefficient. -/
lemma isCoercive_energyIntegrand_add_bounded_principal_zero_drift
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hMu_lt : Mu < lam)
    (hP : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (P *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    (hc : 0 < c₀) :
    IsCoercive (energyIntegrand (A + P) 0 c₀) :=
  isCoercive_energyIntegrand_add_bounded_principal (beta := 0) (rho := c₀)
    hA hMu_lt hP (by simp) le_rfl (by simpa using hc)

end PDE

end TauCeti
