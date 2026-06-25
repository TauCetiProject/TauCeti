/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.UniformEllipticEnergy

/-!
# Gårding lower bounds with a mass floor

The pointwise energy integrand in `TauCeti.Analysis.PDE.EnergyForm` satisfies a Gårding
inequality with a negative `L²` defect coming from the first-order drift.  For the coercive
case of the PDE roadmap's Lane D, the zeroth-order mass coefficient is often assumed to have
a lower bound `μ`; this lower bound offsets the drift defect.

This file records the public pointwise estimate

`λ / 2 * ‖∇u‖² + (μ - β² / (2λ)) * u² ≤ a_x((u, ∇u), (u, ∇u))`

under the inline coefficient hypotheses used throughout the PDE lane, and packages the same
estimate for callers holding the named `UniformlyEllipticOn Ω a λ Λ` hypothesis.  The result
is still finite-dimensional bookkeeping on jets, not an integrated Sobolev-space theorem; it
is the estimate that later integrates to the coercive Gårding inequality on `H¹_0(Ω)`.

## Main declarations

* `TauCeti.PDE.energyIntegrand_self_lower_bound_of_bounds`: pointwise lower bound for one
  coefficient matrix, drift vector, and mass coefficient.
* `TauCeti.PDE.energyIntegrand_self_lower_bound_of_bounds_on`: the coefficient-field
  version on a domain.
* `TauCeti.PDE.UniformlyEllipticOn.energyIntegrand_self_lower_bound`: the same estimate
  from `UniformlyEllipticOn`.
* `TauCeti.PDE.UniformlyEllipticOn.energyIntegrand_self_lower_bound_on`: the
  coefficient-field wrapper from `UniformlyEllipticOn`.
* `TauCeti.PDE.UniformlyEllipticOn.min_coercivityConstant_mul_norm_sq_le_energyIntegrand_self`:
  the explicit positive-constant diagonal estimate when the mass floor dominates the drift
  defect.
-/

public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {X n : Type*} [Fintype n] [DecidableEq n]

variable {Ω : Set X} {a : X → Matrix n n ℝ} {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
variable {lam Lam beta mu : ℝ}

/-- Pointwise lower bound for the energy integrand with bounded drift and a mass floor.

If the principal coefficient has lower ellipticity floor `λ`, the drift coefficient has
norm at most `β`, and the mass coefficient is bounded below by `μ`, then the diagonal jet
energy dominates
`(λ / 2) ‖∇u‖² + (μ - β² / (2λ)) u²`.  When the displayed coefficient of `u²` is positive,
this is the finite-dimensional form of the coercive Gårding estimate. -/
lemma energyIntegrand_self_lower_bound_of_bounds (hlam : 0 < lam)
    {A : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    lam / 2 * ‖U.2‖ ^ 2 + (mu - beta ^ 2 / (2 * lam)) * U.1 ^ 2
      ≤ energyIntegrand A b₀ c₀ U U := by
  have hdecomp : energyIntegrand A b₀ c₀ U U
      = energyIntegrand A b₀ (c₀ - mu) U U + mu * U.1 ^ 2 := by
    rw [energyIntegrand_self, energyIntegrand_self]
    ring
  have hgard :
      lam / 2 * ‖U.2‖ ^ 2 - beta ^ 2 / (2 * lam) * U.1 ^ 2
        ≤ energyIntegrand A b₀ (c₀ - mu) U U :=
    garding_energyIntegrand_self_of_bounds hlam hA hb (sub_nonneg.mpr hc) U
  rw [hdecomp]
  have hrearrange :
      lam / 2 * ‖U.2‖ ^ 2 + (mu - beta ^ 2 / (2 * lam)) * U.1 ^ 2
        = lam / 2 * ‖U.2‖ ^ 2 - beta ^ 2 / (2 * lam) * U.1 ^ 2
          + mu * U.1 ^ 2 := by
    ring
  rw [hrearrange]
  linarith

/-- Pointwise lower bound on a domain, obtained by applying
`energyIntegrand_self_lower_bound_of_bounds` at `x`. -/
lemma energyIntegrand_self_lower_bound_of_bounds_on (hlam : 0 < lam)
    (hA : ∀ ⦃x⦄, x ∈ Ω → ∀ ξ : EuclideanSpace ℝ n,
      lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → mu ≤ c x) {x : X} (hx : x ∈ Ω)
    (U : ℝ × EuclideanSpace ℝ n) :
    lam / 2 * ‖U.2‖ ^ 2 + (mu - beta ^ 2 / (2 * lam)) * U.1 ^ 2
      ≤ energyIntegrand (a x) (b x) (c x) U U :=
  energyIntegrand_self_lower_bound_of_bounds hlam (hA hx) (hb hx) (hc hx) U

namespace UniformlyEllipticOn

/-- Pointwise lower bound for a uniformly elliptic principal coefficient with bounded drift
and a mass floor. -/
lemma energyIntegrand_self_lower_bound (h : UniformlyEllipticOn Ω a lam Lam)
    {x : X} (hx : x ∈ Ω) {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    lam / 2 * ‖U.2‖ ^ 2 + (mu - beta ^ 2 / (2 * lam)) * U.1 ^ 2
      ≤ energyIntegrand (a x) b₀ c₀ U U :=
  PDE.energyIntegrand_self_lower_bound_of_bounds h.pos (h.lower_bound hx) hb hc U

grind_pattern energyIntegrand_self_lower_bound =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, ‖b₀‖ ≤ beta, mu ≤ c₀,
  energyIntegrand (a x) b₀ c₀ U U

/-- Pointwise lower bound on a domain for coefficient fields, from uniform ellipticity of the
principal coefficient, a drift bound, and a mass floor. -/
lemma energyIntegrand_self_lower_bound_on (h : UniformlyEllipticOn Ω a lam Lam)
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → mu ≤ c x) {x : X} (hx : x ∈ Ω)
    (U : ℝ × EuclideanSpace ℝ n) :
    lam / 2 * ‖U.2‖ ^ 2 + (mu - beta ^ 2 / (2 * lam)) * U.1 ^ 2
      ≤ energyIntegrand (a x) (b x) (c x) U U :=
  h.energyIntegrand_self_lower_bound hx (hb hx) (hc hx) U

/-- A uniformly elliptic coefficient with drift bound and mass floor satisfying
`β² / (2λ) < μ` has a positive pointwise coercivity constant in the lower-bound estimate. -/
lemma min_coercivityConstant_pos (h : UniformlyEllipticOn Ω a lam Lam)
    (hmu : beta ^ 2 / (2 * lam) < mu) :
    0 < min (lam / 2) (mu - beta ^ 2 / (2 * lam)) :=
  lt_min (half_pos h.pos) (sub_pos.mpr hmu)

/-- The lower-bound estimate implies the explicit coercive diagonal estimate with constant
`min (λ / 2) (μ - β² / (2λ))`. -/
lemma min_coercivityConstant_mul_norm_sq_le_energyIntegrand_self
    (h : UniformlyEllipticOn Ω a lam Lam)
    {x : X} (hx : x ∈ Ω) {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (hmu : beta ^ 2 / (2 * lam) < mu)
    (U : ℝ × EuclideanSpace ℝ n) :
    min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U‖ ^ 2
      ≤ energyIntegrand (a x) b₀ c₀ U U := by
  have hhalf : 0 < lam / 2 := half_pos h.pos
  have hdef : 0 < mu - beta ^ 2 / (2 * lam) := sub_pos.mpr hmu
  have hnorm := min_mul_prod_norm_sq_le_add hhalf.le hdef.le U
  rw [Real.norm_eq_abs, sq_abs] at hnorm
  exact hnorm.trans (h.energyIntegrand_self_lower_bound hx hb hc U)

/-- The coefficient-field version of the explicit coercive diagonal estimate. -/
lemma min_coercivityConstant_mul_norm_sq_le_energyIntegrand_self_on
    (h : UniformlyEllipticOn Ω a lam Lam)
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
