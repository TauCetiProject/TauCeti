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
`ℝ × EuclideanSpace ℝ n`, not integrated Sobolev-space theorems, and they are not the
hypothesis of Lax--Milgram: that needs coercivity of the *integrated* form on a complete
inner-product (H¹-type) space, later Lane A/D work.  They are the pointwise boundedness and
diagonal lower bounds that the integrated inequality of
`TauCeti.Analysis.PDE.IntegratedEnergyForm` consumes after integrating over the domain.

This file deliberately leaves symmetry to `TauCeti.Analysis.PDE.SymmetricEnergy`.  For a
zero-drift uniformly elliptic operator with symmetric principal coefficient, use
`UniformlyEllipticOn.min_coercivityConstant_mul_norm_sq_le_energyIntegrand_self` for the
diagonal lower bound and the `energyIntegrand_zero_drift_flip_eq_*` lemmas for symmetry; for
nonsymmetric coefficients, the symmetric-part API in
`TauCeti.Analysis.PDE.UniformEllipticity` preserves the ellipticity constants before applying
the same symmetry lemmas.

## Main declarations

* `TauCeti.PDE.UniformlyEllipticOn.norm_energyIntegrand_apply_le`: pointwise boundedness
  of the full energy integrand from a uniform ellipticity hypothesis and bounds on the
  lower-order coefficients at that point.
* `TauCeti.PDE.UniformlyEllipticOn.opNorm_energyIntegrand_le`: operator-norm boundedness
  of the full energy integrand, with explicit constant `Λ + β + γ`.
* `TauCeti.PDE.UniformlyEllipticOn.garding_energyIntegrand_self`: the pointwise
  Gårding lower bound obtained from the lower ellipticity projection of
  `UniformlyEllipticOn`.
* `TauCeti.PDE.UniformlyEllipticOn.garding_energyIntegrand_self_of_mass_lower_bound`:
  the pointwise Gårding lower bound with a mass floor.
* `TauCeti.PDE.UniformlyEllipticOn.min_coercivityConstant_mul_norm_sq_le_energyIntegrand_self`:
  the explicit positive-constant diagonal estimate when the mass floor dominates the
  drift defect.
* The corresponding `_on` lemmas apply these estimates to coefficient fields
  `b : X → EuclideanSpace ℝ n` and `c : X → ℝ` on `Ω`.
-/

public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {X n : Type*} [Fintype n] [DecidableEq n]

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ}
variable {lam Lam beta gamma mu : ℝ}

/-- Pointwise boundedness of the energy integrand from uniform ellipticity of the principal
coefficient and pointwise bounds on the drift and mass coefficients. -/
lemma norm_energyIntegrand_apply_le (h : UniformlyEllipticOn Ω a lam Lam)
    {x : X} (hx : x ∈ Ω) {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : ‖c₀‖ ≤ gamma)
    (U V : ℝ × EuclideanSpace ℝ n) :
    ‖energyIntegrand (a x) b₀ c₀ U V‖ ≤ (Lam + beta + gamma) * ‖U‖ * ‖V‖ :=
  norm_energyIntegrand_apply_le_of_bounds h.upper_nonneg (h.upper_bound hx) hb hc U V

grind_pattern norm_energyIntegrand_apply_le =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, ‖b₀‖ ≤ beta, ‖c₀‖ ≤ gamma,
  energyIntegrand (a x) b₀ c₀ U V

/-- Pointwise boundedness on a domain for coefficient fields, from uniform ellipticity of the
principal coefficient and pointwise bounds on the drift and mass fields. -/
lemma norm_energyIntegrand_apply_le_on (h : UniformlyEllipticOn Ω a lam Lam)
    {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → ‖c x‖ ≤ gamma) {x : X} (hx : x ∈ Ω)
    (U V : ℝ × EuclideanSpace ℝ n) :
    ‖energyIntegrand (a x) (b x) (c x) U V‖ ≤ (Lam + beta + gamma) * ‖U‖ * ‖V‖ :=
  h.norm_energyIntegrand_apply_le hx (hb hx) (hc hx) U V

/-- Operator-norm boundedness of the energy integrand from uniform ellipticity of the
principal coefficient and pointwise bounds on the drift and mass coefficients. -/
lemma opNorm_energyIntegrand_le (h : UniformlyEllipticOn Ω a lam Lam)
    {x : X} (hx : x ∈ Ω) {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : ‖c₀‖ ≤ gamma) :
    ‖energyIntegrand (a x) b₀ c₀‖ ≤ Lam + beta + gamma :=
  opNorm_energyIntegrand_le_of_bounds h.upper_nonneg (h.upper_bound hx) hb hc

grind_pattern opNorm_energyIntegrand_le =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, ‖b₀‖ ≤ beta, ‖c₀‖ ≤ gamma,
  ‖energyIntegrand (a x) b₀ c₀‖

/-- Operator-norm boundedness on a domain for coefficient fields, from uniform ellipticity of
the principal coefficient and pointwise bounds on the drift and mass fields. -/
lemma opNorm_energyIntegrand_le_on (h : UniformlyEllipticOn Ω a lam Lam)
    {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → ‖c x‖ ≤ gamma) {x : X} (hx : x ∈ Ω) :
    ‖energyIntegrand (a x) (b x) (c x)‖ ≤ Lam + beta + gamma :=
  h.opNorm_energyIntegrand_le hx (hb hx) (hc hx)

/-- Pointwise Gårding inequality for a uniformly elliptic principal coefficient.

With nonnegative mass coefficient and drift bound `β`, the diagonal energy density is bounded
below by `(λ/2)‖∇u‖² - (β²/2λ)|u|²`. -/
lemma garding_energyIntegrand_self (h : UniformlyEllipticOn Ω a lam Lam)
    {x : X} (hx : x ∈ Ω) {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : 0 ≤ c₀)
    (U : ℝ × EuclideanSpace ℝ n) :
    lam / 2 * ‖U.2‖ ^ 2 - beta ^ 2 / (2 * lam) * U.1 ^ 2
      ≤ energyIntegrand (a x) b₀ c₀ U U :=
  garding_energyIntegrand_self_of_bounds h.pos (h.lower_bound hx) hb hc U

grind_pattern garding_energyIntegrand_self =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, ‖b₀‖ ≤ beta, 0 ≤ c₀,
  energyIntegrand (a x) b₀ c₀ U U

/-- Pointwise Gårding inequality on a domain for coefficient fields.

With nonnegative mass field and drift bound `β`, the diagonal energy density at every
`x ∈ Ω` is bounded below by `(λ/2)‖∇u‖² - (β²/2λ)|u|²`. -/
lemma garding_energyIntegrand_self_on (h : UniformlyEllipticOn Ω a lam Lam)
    {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → 0 ≤ c x) {x : X} (hx : x ∈ Ω)
    (U : ℝ × EuclideanSpace ℝ n) :
    lam / 2 * ‖U.2‖ ^ 2 - beta ^ 2 / (2 * lam) * U.1 ^ 2
      ≤ energyIntegrand (a x) (b x) (c x) U U :=
  h.garding_energyIntegrand_self hx (hb hx) (hc hx) U

/-- Pointwise Gårding lower bound with a mass floor for a uniformly elliptic principal
coefficient.

With drift bound `β` and mass lower bound `μ`, the diagonal energy density is bounded below
by `(λ / 2)‖∇u‖² + (μ - β² / (2λ))u²`. -/
lemma garding_energyIntegrand_self_of_mass_lower_bound (h : UniformlyEllipticOn Ω a lam Lam)
    {x : X} (hx : x ∈ Ω) {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    lam / 2 * ‖U.2‖ ^ 2 + (mu - beta ^ 2 / (2 * lam)) * U.1 ^ 2
      ≤ energyIntegrand (a x) b₀ c₀ U U :=
  garding_energyIntegrand_self_of_mass_lower_bound_of_bounds h.pos (h.lower_bound hx) hb hc U

grind_pattern garding_energyIntegrand_self_of_mass_lower_bound =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, ‖b₀‖ ≤ beta, mu ≤ c₀,
  energyIntegrand (a x) b₀ c₀ U U

/-- Pointwise Gårding lower bound with a mass floor on a domain for coefficient fields,
from uniform ellipticity of the principal coefficient. -/
lemma garding_energyIntegrand_self_of_mass_lower_bound_on
    (h : UniformlyEllipticOn Ω a lam Lam)
    {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → mu ≤ c x) {x : X} (hx : x ∈ Ω)
    (U : ℝ × EuclideanSpace ℝ n) :
    lam / 2 * ‖U.2‖ ^ 2 + (mu - beta ^ 2 / (2 * lam)) * U.1 ^ 2
      ≤ energyIntegrand (a x) (b x) (c x) U U :=
  h.garding_energyIntegrand_self_of_mass_lower_bound hx (hb hx) (hc hx) U

/-- The lower-bound estimate implies the explicit coercive diagonal estimate with constant
`min (λ / 2) (μ - β² / (2λ))`. -/
lemma min_coercivityConstant_mul_norm_sq_le_energyIntegrand_self
    (h : UniformlyEllipticOn Ω a lam Lam)
    {x : X} (hx : x ∈ Ω) {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (hmu : beta ^ 2 / (2 * lam) < mu)
    (U : ℝ × EuclideanSpace ℝ n) :
    min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U‖ ^ 2
      ≤ energyIntegrand (a x) b₀ c₀ U U :=
  PDE.min_coercivityConstant_mul_norm_sq_le_energyIntegrand_self h.pos (h.lower_bound hx)
    hb hc hmu U

/-- The coefficient-field version of the explicit coercive diagonal estimate from
uniform ellipticity and a mass floor. -/
lemma min_coercivityConstant_mul_norm_sq_le_energyIntegrand_self_on
    (h : UniformlyEllipticOn Ω a lam Lam)
    {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → mu ≤ c x)
    (hmu : beta ^ 2 / (2 * lam) < mu) {x : X} (hx : x ∈ Ω)
    (U : ℝ × EuclideanSpace ℝ n) :
    min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U‖ ^ 2
      ≤ energyIntegrand (a x) (b x) (c x) U U :=
  h.min_coercivityConstant_mul_norm_sq_le_energyIntegrand_self hx (hb hx) (hc hx) hmu U

end UniformlyEllipticOn

end PDE

end TauCeti
