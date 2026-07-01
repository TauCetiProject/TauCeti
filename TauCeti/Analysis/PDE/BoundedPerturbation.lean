/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.UniformEllipticEnergy

/-!
# Coercivity under small bounded principal perturbations

`TauCeti.Analysis.PDE.UniformEllipticity` proves that a uniformly elliptic principal
coefficient remains uniformly elliptic after adding a bounded principal perturbation whose
operator bound is smaller than the ellipticity floor.  This file records the corresponding
pointwise energy-integrand consequences: the same perturbed coefficient feeds the existing
Gårding and coercivity estimates with lower ellipticity constant `λ - μ`.

The statements are still finite-dimensional and pointwise.  They are prerequisites for the
PDE roadmap's Lane D weak-form estimates, where an integrated energy form is often split
into a uniformly elliptic model plus a small bounded second-order perturbation before
applying Lax--Milgram.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.min_coercivityConstant_mul_norm_sq_le_-
  energyIntegrand_add_bounded_principal_self`: explicit diagonal lower bound for a
  uniformly elliptic coefficient plus a small bounded principal perturbation.
* `TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyIntegrand_add_bounded_principal` and
  `_on`: coercivity of the perturbed pointwise jet form.
* `TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyIntegrand_add_bounded_principal_zero_drift`
  and `_on`: the zero-drift positive-mass specialization.

The bookkeeping follows the standard small-perturbation stability of uniformly elliptic
energy estimates; see Evans, *Partial Differential Equations*, Chapter 6.
-/

public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {X n : Type*} [Fintype n] [DecidableEq n]

namespace UniformlyEllipticOn

variable {Ω : Set X} {a p : X → Matrix n n ℝ}
variable {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
variable {lam Lam Mu beta rho : ℝ}

/-- The explicit coercive diagonal estimate after adding a small bounded principal
perturbation to a uniformly elliptic coefficient.

If the perturbation has bilinear bound `μ < λ`, the perturbed coefficient uses lower
ellipticity constant `λ - μ`; the mass floor must dominate the drift defect computed with
that reduced constant. -/
lemma min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_bounded_principal_self
    (h : UniformlyEllipticOn Ω a lam Lam) (hMu_nonneg : 0 ≤ Mu) (hMu_lt : Mu < lam)
    (hp : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (p x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    {x : X} (hx : x ∈ Ω) {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : rho ≤ c₀)
    (hrho : beta ^ 2 / (2 * (lam - Mu)) < rho)
    (U : ℝ × EuclideanSpace ℝ n) :
    min ((lam - Mu) / 2) (rho - beta ^ 2 / (2 * (lam - Mu))) * ‖U‖ ^ 2
      ≤ energyIntegrand (a x + p x) b₀ c₀ U U := by
  exact
    (h.add_bounded hMu_nonneg hMu_lt hp).min_coercivityConstant_mul_norm_sq_le_energyIntegrand_self
      hx hb hc hrho U

/-- Coercivity after adding a small bounded principal perturbation to a uniformly elliptic
coefficient. -/
lemma isCoercive_energyIntegrand_add_bounded_principal
    (h : UniformlyEllipticOn Ω a lam Lam) (hMu_nonneg : 0 ≤ Mu) (hMu_lt : Mu < lam)
    (hp : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (p x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    {x : X} (hx : x ∈ Ω) {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : rho ≤ c₀)
    (hrho : beta ^ 2 / (2 * (lam - Mu)) < rho) :
    IsCoercive (energyIntegrand (a x + p x) b₀ c₀) :=
  (h.add_bounded hMu_nonneg hMu_lt hp).isCoercive_energyIntegrand hx hb hc hrho

/-- Coefficient-field version of
`UniformlyEllipticOn.isCoercive_energyIntegrand_add_bounded_principal`. -/
lemma isCoercive_energyIntegrand_add_bounded_principal_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hMu_nonneg : 0 ≤ Mu) (hMu_lt : Mu < lam)
    (hp : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (p x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → rho ≤ c x)
    (hrho : beta ^ 2 / (2 * (lam - Mu)) < rho) {x : X} (hx : x ∈ Ω) :
    IsCoercive (energyIntegrand (a x + p x) (b x) (c x)) :=
  h.isCoercive_energyIntegrand_add_bounded_principal hMu_nonneg hMu_lt hp hx
    (hb hx) (hc hx) hrho

/-- Zero-drift coercivity after adding a small bounded principal perturbation to a uniformly
elliptic coefficient and keeping a positive mass coefficient. -/
lemma isCoercive_energyIntegrand_add_bounded_principal_zero_drift
    (h : UniformlyEllipticOn Ω a lam Lam) (hMu_nonneg : 0 ≤ Mu) (hMu_lt : Mu < lam)
    (hp : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (p x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    {x : X} (hx : x ∈ Ω) {c₀ : ℝ} (hc : 0 < c₀) :
    IsCoercive (energyIntegrand (a x + p x) 0 c₀) :=
  (h.add_bounded hMu_nonneg hMu_lt hp).isCoercive_energyIntegrand_zero_drift hx hc

/-- Coefficient-field version of
`UniformlyEllipticOn.isCoercive_energyIntegrand_add_bounded_principal_zero_drift`. -/
lemma isCoercive_energyIntegrand_add_bounded_principal_zero_drift_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hMu_nonneg : 0 ≤ Mu) (hMu_lt : Mu < lam)
    (hp : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (p x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    (hc : ∀ ⦃x⦄, x ∈ Ω → 0 < c x) {x : X} (hx : x ∈ Ω) :
    IsCoercive (energyIntegrand (a x + p x) 0 (c x)) :=
  h.isCoercive_energyIntegrand_add_bounded_principal_zero_drift hMu_nonneg hMu_lt hp hx
    (hc hx)

end UniformlyEllipticOn

end PDE

end TauCeti
