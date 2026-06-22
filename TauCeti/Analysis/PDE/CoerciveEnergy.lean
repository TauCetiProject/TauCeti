/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Analysis.PDE.EnergyForm

/-!
# Pointwise coercivity for divergence-form energy integrands

The PDE roadmap's Lax--Milgram lane needs coercive bilinear forms.  The file
`TauCeti.Analysis.PDE.EnergyForm` gives the pointwise energy integrand for a divergence-form
operator together with its pointwise Gårding lower bound.  This file turns that Gårding
estimate into pointwise coercivity once the zeroth-order mass coefficient has a lower bound
that dominates the drift defect `β²/2λ`.

This is still a pointwise finite-dimensional statement: the weak Sobolev space and the
integrated energy form are later Lane A/D work.  The coefficient assumptions (uniform
ellipticity, a drift bound, and a mass lower bound) are kept as separate named predicates,
in the roadmap's style of spelling out coefficient assumptions rather than hiding them in a
monolithic PDE class.

## Main declarations

* `TauCeti.PDE.energyIntegrand_self_lower_bound_of_bounds`: pointwise lower bound for the
  energy density with bounded drift and a mass lower bound.
* `TauCeti.PDE.isCoercive_energyIntegrand_of_bounds`: coercivity of the jet bilinear form when
  the mass lower bound dominates the drift defect.
* `TauCeti.PDE.isCoercive_energyIntegrand_zero_drift_of_lower_bounds`: the zero-drift
  specialization, needing only a positive mass lower bound.
* `TauCeti.PDE.isCoercive_energyIntegrand_of_bounds_on`: the domain version from raw lower
  bounds, with no upper ellipticity bound or bundled coefficient predicate.
* `TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyIntegrand` and
  `TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyIntegrand_zero_drift`: the same results
  using the bundled uniform-ellipticity and coefficient predicates.
-/

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {X n : Type*} [Fintype n] [DecidableEq n]

variable {lam mu beta : ℝ}

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

/-- Pointwise lower bound for the energy integrand with bounded drift and a mass lower bound.

If the principal part has quadratic lower bound `λ‖ξ‖²`, the drift satisfies `‖b₀‖ ≤ β`, and
the mass coefficient satisfies `μ ≤ c₀`, then the diagonal of the jet form is bounded below by
`(λ/2)‖∇u‖² + (μ − β²/2λ)|u|²`. -/
lemma energyIntegrand_self_lower_bound_of_bounds (hlam : 0 < lam)
    {A : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    lam / 2 * ‖U.2‖ ^ 2 + (mu - beta ^ 2 / (2 * lam)) * U.1 ^ 2
      ≤ energyIntegrand A b₀ c₀ U U := by
  have hdecomp : energyIntegrand A b₀ c₀ U U
      = energyIntegrand A b₀ (c₀ - mu) U U + mu * U.1 ^ 2 := by
    rw [energyIntegrand_self, energyIntegrand_self]; ring
  have hgard := garding_energyIntegrand_self_of_bounds (Ω := (Set.univ : Set Unit))
    (a := fun _ => A) (b := fun _ => b₀) (c := fun _ => c₀ - mu) hlam
    (fun {_} _ ξ => hA ξ) (fun {_} _ => hb) (fun {_} _ => sub_nonneg.mpr hc)
    (Set.mem_univ ()) U
  rw [hdecomp]
  have hrw : lam / 2 * ‖U.2‖ ^ 2 + (mu - beta ^ 2 / (2 * lam)) * U.1 ^ 2
      = lam / 2 * ‖U.2‖ ^ 2 - beta ^ 2 / (2 * lam) * U.1 ^ 2 + mu * U.1 ^ 2 := by ring
  rw [hrw]
  linarith [hgard]

/-- Coercivity of the jet bilinear form when the mass lower bound dominates the drift defect.

With ellipticity floor `λ`, drift bound `β`, and mass lower bound `μ` satisfying `β²/2λ < μ`,
the jet form is coercive with constant `min (λ/2) (μ − β²/2λ)`. -/
lemma isCoercive_energyIntegrand_of_bounds (hlam : 0 < lam)
    {A : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (hmu : beta ^ 2 / (2 * lam) < mu) :
    IsCoercive (energyIntegrand A b₀ c₀) := by
  have hhalf : (0 : ℝ) < lam / 2 := by positivity
  have hdef : 0 < mu - beta ^ 2 / (2 * lam) := sub_pos.mpr hmu
  refine ⟨min (lam / 2) (mu - beta ^ 2 / (2 * lam)), lt_min hhalf hdef, fun U => ?_⟩
  have hlb := energyIntegrand_self_lower_bound_of_bounds hlam hA hb hc U
  have hmin := min_mul_prod_norm_sq_le_add hhalf.le hdef.le U
  rw [Real.norm_eq_abs, sq_abs] at hmin
  simpa [pow_two, mul_assoc] using hmin.trans hlb

/-- Coercivity of the zero-drift jet bilinear form from a positive mass lower bound.

This is the `β = 0` specialization of `isCoercive_energyIntegrand_of_bounds`, where the
coercivity constant is `min (λ/2) μ`. -/
lemma isCoercive_energyIntegrand_zero_drift_of_lower_bounds (hlam : 0 < lam) (hmu : 0 < mu)
    {A : Matrix n n ℝ} {c₀ : ℝ}
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hc : mu ≤ c₀) :
    IsCoercive (energyIntegrand A 0 c₀) :=
  isCoercive_energyIntegrand_of_bounds (beta := 0) hlam hA (by simp) hc (by simpa using hmu)

/-- Coercivity of the pointwise jet bilinear form on a domain from raw lower bounds.

At each point of `Ω`, an ellipticity floor `λ`, a drift bound `β`, and a mass lower bound `μ`
with `β²/2λ < μ` make the jet form coercive.  Only the lower assumptions are needed: there is
no upper ellipticity bound and no bundled coefficient predicate. -/
lemma isCoercive_energyIntegrand_of_bounds_on {Ω : Set X}
    {a : X → Matrix n n ℝ} {b : X → EuclideanSpace ℝ n} {c : X → ℝ} (hlam : 0 < lam)
    (hA : ∀ ⦃x⦄, x ∈ Ω → ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ (a x).toQuadraticForm' ξ)
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta) (hc : ∀ ⦃x⦄, x ∈ Ω → mu ≤ c x)
    (hmu : beta ^ 2 / (2 * lam) < mu) {x : X} (hx : x ∈ Ω) :
    IsCoercive (energyIntegrand (a x) (b x) (c x)) :=
  isCoercive_energyIntegrand_of_bounds hlam (hA hx) (hb hx) (hc hx) hmu

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ} {b : X → EuclideanSpace ℝ n} {c : X → ℝ}
variable {lam Lam beta mu : ℝ}

/-- A uniformly elliptic principal coefficient, a bounded drift, and a mass lower bound that
dominates the drift defect make the pointwise jet integrand coercive at every point of the
domain. -/
@[grind =>]
lemma isCoercive_energyIntegrand (he : UniformlyEllipticOn Ω a lam Lam)
    (hb : DriftBoundedOn Ω b beta) (hc : MassLowerBoundOn Ω c mu)
    (hmu : beta ^ 2 / (2 * lam) < mu) {x : X} (hx : x ∈ Ω) :
    IsCoercive (energyIntegrand (a x) (b x) (c x)) :=
  isCoercive_energyIntegrand_of_bounds_on he.pos (fun {_} hy => he.lower_bound hy)
    (fun {_} hy => hb.bound hy) (fun {_} hy => hc.lower_bound hy) hmu hx

/-- A uniformly elliptic principal coefficient and a positive mass lower bound make the
zero-drift pointwise jet integrand coercive at every point of the domain. -/
@[grind =>]
lemma isCoercive_energyIntegrand_zero_drift (he : UniformlyEllipticOn Ω a lam Lam)
    (hc : MassLowerBoundOn Ω c mu) {x : X} (hx : x ∈ Ω) :
    IsCoercive (energyIntegrand (a x) 0 (c x)) :=
  isCoercive_energyIntegrand_zero_drift_of_lower_bounds he.pos hc.mu_pos
    (he.lower_bound hx) (hc.lower_bound hx)

end UniformlyEllipticOn

end PDE

end TauCeti
