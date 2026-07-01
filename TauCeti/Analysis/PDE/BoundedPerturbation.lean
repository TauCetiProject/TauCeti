/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.UniformEllipticEnergy

/-!
# Coercivity under small bounded principal perturbations

This file records pointwise and coefficient-field energy coercivity after adding a small
bounded principal perturbation.  The perturbation bound is deliberately an inline
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

/-- Coercivity after adding a small bounded principal perturbation to a coefficient with a
quadratic lower bound. -/
lemma isCoercive_energyIntegrand_add_bounded_principal
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hMu_lt : Mu < lam)
    (hP : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (P *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    (hb : ‖b₀‖ ≤ beta) (hc : rho ≤ c₀)
    (hrho : beta ^ 2 / (2 * (lam - Mu)) < rho) :
    IsCoercive (energyIntegrand (A + P) b₀ c₀) :=
  isCoercive_energyIntegrand_of_bounds (sub_pos.mpr hMu_lt)
    (lower_bound_toQuadraticForm'_add_of_lower_bound hA
      (fun ξ =>
        (neg_le_neg (abs_toQuadraticForm'_le_of_abs_dotProduct_mulVec_le hP ξ)).trans
          (neg_abs_le (P.toQuadraticForm' ξ))))
    hb hc hrho

/-- Zero-drift coercivity after adding a small bounded principal perturbation to a coefficient
with a quadratic lower bound and keeping a positive mass coefficient. -/
lemma isCoercive_energyIntegrand_add_bounded_principal_zero_drift
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hMu_lt : Mu < lam)
    (hP : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (P *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    (hc : 0 < c₀) :
    IsCoercive (energyIntegrand (A + P) 0 c₀) :=
  isCoercive_energyIntegrand_zero_drift (sub_pos.mpr hMu_lt) hc
    (lower_bound_toQuadraticForm'_add_of_lower_bound hA
      (fun ξ =>
        (neg_le_neg (abs_toQuadraticForm'_le_of_abs_dotProduct_mulVec_le hP ξ)).trans
          (neg_abs_le (P.toQuadraticForm' ξ))))

namespace UniformlyEllipticOn

variable {X : Type*} {Ω : Set X} {a p : X → Matrix n n ℝ}
variable {b : X → EuclideanSpace ℝ n} {c : X → ℝ} {Lam : ℝ}

/-- The explicit coercive diagonal estimate for a uniformly elliptic coefficient field after
adding a bounded principal perturbation field. -/
lemma min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_bounded_principal_self
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) (hMu_nonneg : 0 ≤ Mu)
    (hMu_lt : Mu < lam)
    (hp : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (p x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : rho ≤ c₀)
    (hrho : beta ^ 2 / (2 * (lam - Mu)) < rho)
    (U : ℝ × EuclideanSpace ℝ n) :
    min ((lam - Mu) / 2) (rho - beta ^ 2 / (2 * (lam - Mu))) * ‖U‖ ^ 2
      ≤ energyIntegrand (a x + p x) b₀ c₀ U U :=
  (h.add_bounded hMu_nonneg hMu_lt hp).min_coercivityConstant_mul_norm_sq_le_energyIntegrand_self
    hx hb hc hrho U

/-- Coefficient-field version of the explicit coercive diagonal estimate after adding a
bounded principal perturbation field. -/
lemma min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_bounded_principal_self_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hMu_nonneg : 0 ≤ Mu) (hMu_lt : Mu < lam)
    (hp : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (p x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → rho ≤ c x)
    (hrho : beta ^ 2 / (2 * (lam - Mu)) < rho) {x : X} (hx : x ∈ Ω)
    (U : ℝ × EuclideanSpace ℝ n) :
    min ((lam - Mu) / 2) (rho - beta ^ 2 / (2 * (lam - Mu))) * ‖U‖ ^ 2
      ≤ energyIntegrand (a x + p x) (b x) (c x) U U :=
  h.min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_bounded_principal_self hx
    hMu_nonneg hMu_lt hp (hb hx) (hc hx) hrho U

/-- Pointwise coercivity for a uniformly elliptic coefficient field after adding a bounded
principal perturbation field. -/
lemma isCoercive_energyIntegrand_add_bounded_principal
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) (hMu_nonneg : 0 ≤ Mu)
    (hMu_lt : Mu < lam)
    (hp : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (p x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : rho ≤ c₀)
    (hrho : beta ^ 2 / (2 * (lam - Mu)) < rho) :
    IsCoercive (energyIntegrand (a x + p x) b₀ c₀) :=
  (h.add_bounded hMu_nonneg hMu_lt hp).isCoercive_energyIntegrand hx hb hc hrho

/-- Coefficient-field version of pointwise coercivity after adding a bounded principal
perturbation field. -/
lemma isCoercive_energyIntegrand_add_bounded_principal_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hMu_nonneg : 0 ≤ Mu) (hMu_lt : Mu < lam)
    (hp : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (p x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → rho ≤ c x)
    (hrho : beta ^ 2 / (2 * (lam - Mu)) < rho) {x : X} (hx : x ∈ Ω) :
    IsCoercive (energyIntegrand (a x + p x) (b x) (c x)) :=
  h.isCoercive_energyIntegrand_add_bounded_principal hx hMu_nonneg hMu_lt hp
    (hb hx) (hc hx) hrho

/-- Pointwise zero-drift coercivity for a uniformly elliptic coefficient field after adding
a bounded principal perturbation field and keeping a positive mass coefficient. -/
lemma isCoercive_energyIntegrand_add_bounded_principal_zero_drift
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) (hMu_nonneg : 0 ≤ Mu)
    (hMu_lt : Mu < lam)
    (hp : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (p x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    {c₀ : ℝ} (hc : 0 < c₀) :
    IsCoercive (energyIntegrand (a x + p x) 0 c₀) :=
  (h.add_bounded hMu_nonneg hMu_lt hp).isCoercive_energyIntegrand_zero_drift hx hc

/-- Coefficient-field zero-drift coercivity after adding a bounded principal perturbation
field and keeping a positive mass field. -/
lemma isCoercive_energyIntegrand_add_bounded_principal_zero_drift_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hMu_nonneg : 0 ≤ Mu) (hMu_lt : Mu < lam)
    (hp : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (p x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    (hc : ∀ ⦃x⦄, x ∈ Ω → 0 < c x) {x : X} (hx : x ∈ Ω) :
    IsCoercive (energyIntegrand (a x + p x) 0 (c x)) :=
  h.isCoercive_energyIntegrand_add_bounded_principal_zero_drift hx hMu_nonneg hMu_lt hp
    (hc hx)

end UniformlyEllipticOn

end PDE

end TauCeti
