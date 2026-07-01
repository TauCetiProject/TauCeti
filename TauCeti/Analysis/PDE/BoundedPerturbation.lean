/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.UniformEllipticEnergy

/-!
# Coercivity under small bounded principal perturbations

This file records pointwise and coefficient-field energy coercivity after adding a small
bounded principal perturbation.  The perturbation bound is deliberately an inline hypothesis,
matching the PDE roadmap's convention for bounded coefficient assumptions.

The proofs route through `UniformlyEllipticOn.add_bounded`, then reuse the existing energy
coercivity estimates with the reduced lower constant `λ - μ`.
-/

public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {b₀ : EuclideanSpace ℝ n} {c₀ lam Mu beta rho : ℝ}

namespace UniformlyEllipticOn

variable {X : Type*} {Ω : Set X} {a p : X → Matrix n n ℝ}
variable {P : Matrix n n ℝ}
variable {b : X → EuclideanSpace ℝ n} {c : X → ℝ} {Lam : ℝ}

/-- Pointwise coercivity for a uniformly elliptic coefficient field after adding a bounded
principal perturbation matrix. -/
lemma isCoercive_energyIntegrand_add_bounded_principal
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) (hMu_nonneg : 0 ≤ Mu)
    (hMu_lt : Mu < lam)
    (hP : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (P *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : rho ≤ c₀)
    (hrho : beta ^ 2 / (2 * (lam - Mu)) < rho) :
    IsCoercive (energyIntegrand (a x + P) b₀ c₀) :=
  (h.add_bounded (b := fun _ => P) hMu_nonneg hMu_lt (fun {_} _ => hP)).isCoercive_energyIntegrand
    hx hb hc hrho

grind_pattern isCoercive_energyIntegrand_add_bounded_principal =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, 0 ≤ Mu, Mu < lam, ‖b₀‖ ≤ beta, rho ≤ c₀,
  beta ^ 2 / (2 * (lam - Mu)) < rho, IsCoercive (energyIntegrand (a x + P) b₀ c₀)

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
  h.isCoercive_energyIntegrand_add_bounded_principal (P := p x) hx hMu_nonneg hMu_lt (hp hx)
    (hb hx) (hc hx) hrho

/-- Pointwise zero-drift coercivity for a uniformly elliptic coefficient field after adding
a bounded principal perturbation matrix and keeping a positive mass coefficient. -/
lemma isCoercive_energyIntegrand_add_bounded_principal_zero_drift
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) (hMu_nonneg : 0 ≤ Mu)
    (hMu_lt : Mu < lam)
    (hP : ∀ η ξ : EuclideanSpace ℝ n, |η ⬝ᵥ (P *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    {c₀ : ℝ} (hc : 0 < c₀) :
    IsCoercive (energyIntegrand (a x + P) 0 c₀) :=
  let h' := h.add_bounded (b := fun _ => P) hMu_nonneg hMu_lt (fun {_} _ => hP)
  h'.isCoercive_energyIntegrand_zero_drift hx hc

grind_pattern isCoercive_energyIntegrand_add_bounded_principal_zero_drift =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, 0 ≤ Mu, Mu < lam, 0 < c₀,
  IsCoercive (energyIntegrand (a x + P) 0 c₀)

/-- Coefficient-field zero-drift coercivity after adding a bounded principal perturbation
field and keeping a positive mass field. -/
lemma isCoercive_energyIntegrand_add_bounded_principal_zero_drift_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hMu_nonneg : 0 ≤ Mu) (hMu_lt : Mu < lam)
    (hp : ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
      |η ⬝ᵥ (p x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖)
    (hc : ∀ ⦃x⦄, x ∈ Ω → 0 < c x) {x : X} (hx : x ∈ Ω) :
    IsCoercive (energyIntegrand (a x + p x) 0 (c x)) :=
  h.isCoercive_energyIntegrand_add_bounded_principal_zero_drift (P := p x) hx hMu_nonneg
    hMu_lt (hp hx) (hc hx)

end UniformlyEllipticOn

end PDE

end TauCeti
