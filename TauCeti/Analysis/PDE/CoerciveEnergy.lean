/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Analysis.PDE.EnergyForm

/-!
# Pointwise coercivity for massive divergence-form energy integrands

The PDE roadmap's Lax--Milgram lane needs coercive bilinear forms.  The file
`TauCeti.Analysis.PDE.EnergyForm` gives the pointwise energy integrand for a
divergence-form operator.  This file records the elementary coercive case where the
principal coefficient is uniformly elliptic and the zeroth-order mass coefficient has a
strict positive lower bound.

This is still a pointwise finite-dimensional statement: the weak Sobolev space and the
integrated energy form are later Lane A/D work.  The lower-mass hypothesis is kept as a
separate predicate, in the roadmap's style of spelling out coefficient assumptions rather
than hiding them in a monolithic PDE class.

## Main declarations

* `TauCeti.PDE.MassLowerBoundOn`: a positive lower bound for a mass coefficient.
* `TauCeti.PDE.massiveEnergyIntegrand_self_lower_bound`: pointwise lower bound for the
  zero-drift energy density.
* `TauCeti.PDE.isCoercive_energyIntegrand_zero_drift_of_lower_bounds`: coercivity of the
  bundled jet bilinear form from ellipticity and a positive mass lower bound.
* `TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyIntegrand_zero_drift`: the same result
  using the bundled uniform-ellipticity predicate.
-/

namespace TauCeti

namespace PDE

open Matrix

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- A strictly positive lower bound for a zeroth-order mass coefficient on a domain. -/
def MassLowerBoundOn (Ω : Set X) (c : X → ℝ) (mu : ℝ) : Prop :=
  0 < mu ∧ ∀ ⦃x⦄, x ∈ Ω → mu ≤ c x

/-- Characteristic restatement of a positive mass lower bound. -/
lemma massLowerBoundOn_iff {Ω : Set X} {c : X → ℝ} {mu : ℝ} :
    MassLowerBoundOn Ω c mu ↔ 0 < mu ∧ ∀ ⦃x⦄, x ∈ Ω → mu ≤ c x :=
  Iff.rfl

namespace MassLowerBoundOn

variable {Ω Ω' : Set X} {c : X → ℝ} {mu mu' : ℝ}

/-- The mass lower-bound constant is positive. -/
@[grind →]
lemma pos (h : MassLowerBoundOn Ω c mu) : 0 < mu :=
  h.1

/-- The mass lower-bound constant is nonnegative. -/
lemma nonneg (h : MassLowerBoundOn Ω c mu) : 0 ≤ mu :=
  h.pos.le

/-- The pointwise lower bound supplied by a mass lower-bound hypothesis. -/
@[grind =>]
lemma lower_bound (h : MassLowerBoundOn Ω c mu) {x : X} (hx : x ∈ Ω) : mu ≤ c x :=
  h.2 hx

/-- A positive mass lower bound gives pointwise nonnegativity of the mass coefficient. -/
lemma nonnegMassPointwiseOn (h : MassLowerBoundOn Ω c mu) :
    NonnegMassPointwiseOn Ω c :=
  fun {_} hx => h.nonneg.trans (h.lower_bound hx)

/-- Restricting the domain preserves a mass lower bound. -/
lemma mono_set (h : MassLowerBoundOn Ω c mu) (hΩ : Ω' ⊆ Ω) :
    MassLowerBoundOn Ω' c mu :=
  ⟨h.pos, fun {_} hx => h.lower_bound (hΩ hx)⟩

/-- Decreasing the positive lower-bound constant preserves a mass lower bound. -/
lemma mono_constant (h : MassLowerBoundOn Ω c mu) (hmu' : 0 < mu') (hmu'_le : mu' ≤ mu) :
    MassLowerBoundOn Ω c mu' :=
  ⟨hmu', fun {_} hx => hmu'_le.trans (h.lower_bound hx)⟩

end MassLowerBoundOn

variable {Ω : Set X} {a : X → Matrix n n ℝ} {c : X → ℝ} {lam mu : ℝ}

omit [DecidableEq n] in
/-- The square of the product sup norm is controlled by the two squared coordinate norms
with the smaller coefficient. -/
private lemma min_mul_prod_norm_sq_le_add (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    (U : ℝ × EuclideanSpace ℝ n) :
    min lam mu * ‖U‖ ^ 2 ≤ lam * ‖U.2‖ ^ 2 + mu * ‖U.1‖ ^ 2 := by
  have hmin_lam : min lam mu ≤ lam := min_le_left _ _
  have hmin_mu : min lam mu ≤ mu := min_le_right _ _
  rw [Prod.norm_def]
  rcases le_total ‖U.1‖ ‖U.2‖ with hle | hle
  · rw [max_eq_right hle]
    calc
      min lam mu * ‖U.2‖ ^ 2 ≤ lam * ‖U.2‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right hmin_lam (sq_nonneg ‖U.2‖)
      _ ≤ lam * ‖U.2‖ ^ 2 + mu * ‖U.1‖ ^ 2 := by
        exact le_add_of_nonneg_right (mul_nonneg hmu (sq_nonneg ‖U.1‖))
  · rw [max_eq_left hle]
    calc
      min lam mu * ‖U.1‖ ^ 2 ≤ mu * ‖U.1‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_right hmin_mu (sq_nonneg ‖U.1‖)
      _ ≤ lam * ‖U.2‖ ^ 2 + mu * ‖U.1‖ ^ 2 := by
        exact le_add_of_nonneg_left (mul_nonneg hlam (sq_nonneg ‖U.2‖))

/-- Pointwise lower bound for the zero-drift energy integrand with a positive mass floor.

If the principal part has quadratic lower bound `λ‖ξ‖²` and the mass coefficient satisfies
`μ ≤ c`, then the jet energy controls the full product norm with constant `min λ μ`. -/
lemma massiveEnergyIntegrand_self_lower_bound (hlam : 0 ≤ lam) (hmu : 0 ≤ mu)
    {A : Matrix n n ℝ} {c₀ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hc : mu ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    min lam mu * ‖U‖ ^ 2 ≤ energyIntegrand A 0 c₀ U U := by
  have hmass : mu * ‖U.1‖ ^ 2 ≤ c₀ * U.1 ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs]
    exact mul_le_mul_of_nonneg_right hc (sq_nonneg U.1)
  have hprincipal : lam * ‖U.2‖ ^ 2 ≤ A.toQuadraticForm' U.2 := hA U.2
  calc
    min lam mu * ‖U‖ ^ 2 ≤ lam * ‖U.2‖ ^ 2 + mu * ‖U.1‖ ^ 2 :=
      min_mul_prod_norm_sq_le_add hlam hmu U
    _ ≤ energyIntegrand A 0 c₀ U U := by
      have henergy : A.toQuadraticForm' U.2 + c₀ * U.1 ^ 2 = energyIntegrand A 0 c₀ U U := by
        rw [energyIntegrand_self]
        simp
      exact (add_le_add hprincipal hmass).trans_eq henergy

/-- Coercivity of the zero-drift jet bilinear form from separate pointwise lower bounds.

The coercivity constant is `min λ μ`, where `λ` is the ellipticity floor and `μ` is the
positive mass floor. -/
lemma isCoercive_energyIntegrand_zero_drift_of_lower_bounds (hlam : 0 < lam) (hmu : 0 < mu)
    {A : Matrix n n ℝ} {c₀ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hc : mu ≤ c₀) :
    IsCoercive (energyIntegrand A 0 c₀) := by
  refine ⟨min lam mu, lt_min hlam hmu, fun U => ?_⟩
  simpa [pow_two, mul_assoc] using massiveEnergyIntegrand_self_lower_bound hlam.le hmu.le hA hc U

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ} {c : X → ℝ} {lam Lam mu : ℝ}

/-- A uniformly elliptic principal coefficient and a positive mass lower bound make the
zero-drift pointwise jet integrand coercive at every point of the domain. -/
@[grind =>]
lemma isCoercive_energyIntegrand_zero_drift (he : UniformlyEllipticOn Ω a lam Lam)
    (hc : MassLowerBoundOn Ω c mu) {x : X} (hx : x ∈ Ω) :
    IsCoercive (energyIntegrand (a x) 0 (c x)) :=
  isCoercive_energyIntegrand_zero_drift_of_lower_bounds he.pos hc.pos
    (he.lower_bound hx) (hc.lower_bound hx)

end UniformlyEllipticOn

end PDE

end TauCeti
