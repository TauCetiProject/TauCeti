/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.CoerciveEnergy

/-!
# Energy-integrand estimates from uniform ellipticity

`TauCeti.Analysis.PDE.EnergyForm` and `TauCeti.Analysis.PDE.CoerciveEnergy` prove the
pointwise estimates for divergence-form energy integrands from raw coefficient bounds.
This file packages the same estimates for callers that hold the roadmap's named principal
coefficient hypothesis `UniformlyEllipticOn Ω a λ Λ`.

The statements are still pointwise finite-dimensional estimates on jets
`ℝ × EuclideanSpace ℝ n`, not integrated Sobolev-space theorems. They are the API that
later Lane D work can consume when turning a uniformly elliptic coefficient field, bounded
lower-order coefficients, and a mass lower bound into the bounded/coercive hypotheses of
Lax--Milgram.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.norm_energyIntegrand_apply_le`: pointwise boundedness
  of the full energy integrand from a uniform ellipticity hypothesis and inline lower-order
  bounds.
* `TauCeti.PDE.UniformlyEllipticOn.opNorm_energyIntegrand_le`: operator-norm boundedness
  of the full energy integrand, with explicit constant `Λ + β + γ`.
* `TauCeti.PDE.UniformlyEllipticOn.garding_energyIntegrand_self_le`: the pointwise
  Gårding lower bound obtained from the lower ellipticity projection of
  `UniformlyEllipticOn`.
* `TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyIntegrand`: coercivity when the mass
  lower bound dominates the first-order drift defect.
* `TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyIntegrand_zero_drift`: the zero-drift
  specialization, needing only a positive mass coefficient.
-/

public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {X n : Type*} [Fintype n] [DecidableEq n]

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ} {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
variable {lam Lam beta gamma mu : ℝ}

/-- Pointwise boundedness of the energy integrand from uniform ellipticity of the principal
coefficient and inline bounds on the drift and mass coefficients. -/
lemma norm_energyIntegrand_apply_le (h : UniformlyEllipticOn Ω a lam Lam)
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → ‖c x‖ ≤ gamma) {x : X} (hx : x ∈ Ω)
    (U V : ℝ × EuclideanSpace ℝ n) :
    ‖energyIntegrand (a x) (b x) (c x) U V‖ ≤ (Lam + beta + gamma) * ‖U‖ * ‖V‖ :=
  norm_energyIntegrand_apply_le_of_bounds h.upper_nonneg (h.upper_bound hx) (hb hx)
    (hc hx) U V

/-- Operator-norm boundedness of the energy integrand from uniform ellipticity of the
principal coefficient and inline bounds on the drift and mass coefficients. -/
lemma opNorm_energyIntegrand_le (h : UniformlyEllipticOn Ω a lam Lam)
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → ‖c x‖ ≤ gamma) {x : X} (hx : x ∈ Ω) :
    ‖energyIntegrand (a x) (b x) (c x)‖ ≤ Lam + beta + gamma :=
  opNorm_energyIntegrand_le_of_bounds h.upper_nonneg (h.upper_bound hx) (hb hx) (hc hx)

/-- Pointwise Gårding inequality for a uniformly elliptic principal coefficient.

With nonnegative mass coefficient and drift bound `β`, the diagonal energy density is bounded
below by `(λ/2)‖∇u‖² - (β²/2λ)|u|²`. -/
lemma garding_energyIntegrand_self_le (h : UniformlyEllipticOn Ω a lam Lam)
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → 0 ≤ c x) {x : X} (hx : x ∈ Ω)
    (U : ℝ × EuclideanSpace ℝ n) :
    lam / 2 * ‖U.2‖ ^ 2 - beta ^ 2 / (2 * lam) * U.1 ^ 2
      ≤ energyIntegrand (a x) (b x) (c x) U U :=
  garding_energyIntegrand_self_of_bounds h.pos (h.lower_bound hx) (hb hx) (hc hx) U

/-- Pointwise coercivity of the energy integrand from uniform ellipticity, a drift bound,
and a mass lower bound that dominates the drift defect.

This is the `UniformlyEllipticOn` wrapper around
`isCoercive_energyIntegrand_of_bounds`: at each point of `Ω`, if
`β² / (2λ) < μ ≤ c x`, then the jet bilinear form is coercive. -/
lemma isCoercive_energyIntegrand (h : UniformlyEllipticOn Ω a lam Lam)
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → mu ≤ c x) (hmu : beta ^ 2 / (2 * lam) < mu)
    {x : X} (hx : x ∈ Ω) :
    IsCoercive (energyIntegrand (a x) (b x) (c x)) :=
  isCoercive_energyIntegrand_of_bounds h.pos (h.lower_bound hx) (hb hx) (hc hx) hmu

/-- The zero-drift coercivity specialization for a uniformly elliptic principal coefficient.

At each point of `Ω`, a positive mass coefficient makes
`energyIntegrand (a x) 0 (c x)` coercive. -/
lemma isCoercive_energyIntegrand_zero_drift (h : UniformlyEllipticOn Ω a lam Lam)
    (hc : ∀ ⦃x⦄, x ∈ Ω → 0 < c x) {x : X} (hx : x ∈ Ω) :
    IsCoercive (energyIntegrand (a x) 0 (c x)) :=
  PDE.isCoercive_energyIntegrand_zero_drift h.pos (hc hx) (h.lower_bound hx)

end UniformlyEllipticOn

end PDE

end TauCeti
