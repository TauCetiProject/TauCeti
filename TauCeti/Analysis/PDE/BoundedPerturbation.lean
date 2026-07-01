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
coercivity and diagonal lower-bound estimates with lower ellipticity constant `λ - μ`.

The statements are still finite-dimensional and pointwise.  They are prerequisites for the
PDE roadmap's Lane D weak-form estimates, where an integrated energy form is often split
into a uniformly elliptic model plus a small bounded second-order perturbation before
applying Lax--Milgram.

## Main declarations

* `TauCeti.PDE.min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_bounded_principal_self`:
  explicit diagonal lower bound from a quadratic lower bound plus a small bounded principal
  perturbation.
* `TauCeti.PDE.MatrixBilinearBoundedOn`: pointwise bilinear bound for a principal
  perturbation field on a domain.
* The corresponding `TauCeti.PDE.UniformlyEllipticOn` specialization of the diagonal lower
  bound.
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
variable {A P : Matrix n n ℝ}
variable {b₀ : EuclideanSpace ℝ n} {c₀ lam Mu beta rho : ℝ}

/-- A principal coefficient field has bilinear operator bound `μ` on a domain. -/
def MatrixBilinearBoundedOn (Ω : Set X) (p : X → Matrix n n ℝ) (Mu : ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ Ω → ∀ η ξ : EuclideanSpace ℝ n,
    |η ⬝ᵥ (p x *ᵥ ξ)| ≤ Mu * ‖η‖ * ‖ξ‖

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
    (h : UniformlyEllipticOn Ω a lam Lam) (hMu_lt : Mu < lam)
    (hp : MatrixBilinearBoundedOn Ω p Mu)
    {x : X} (hx : x ∈ Ω) {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : rho ≤ c₀)
    (hrho : beta ^ 2 / (2 * (lam - Mu)) < rho)
    (U : ℝ × EuclideanSpace ℝ n) :
    min ((lam - Mu) / 2) (rho - beta ^ 2 / (2 * (lam - Mu))) * ‖U‖ ^ 2
      ≤ energyIntegrand (a x + p x) b₀ c₀ U U := by
  exact PDE.min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_bounded_principal_self
    (h.lower_bound hx) hMu_lt (hp hx) hb hc hrho U

/-- Coefficient-field version of the explicit coercive diagonal estimate after adding a small
bounded principal perturbation to a uniformly elliptic coefficient. -/
lemma min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_bounded_principal_self_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hMu_lt : Mu < lam)
    (hp : MatrixBilinearBoundedOn Ω p Mu)
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → rho ≤ c x)
    (hrho : beta ^ 2 / (2 * (lam - Mu)) < rho) {x : X} (hx : x ∈ Ω)
    (U : ℝ × EuclideanSpace ℝ n) :
    min ((lam - Mu) / 2) (rho - beta ^ 2 / (2 * (lam - Mu))) * ‖U‖ ^ 2
      ≤ energyIntegrand (a x + p x) (b x) (c x) U U :=
  h.min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_bounded_principal_self
    hMu_lt hp hx (hb hx) (hc hx) hrho U

/-- Coercivity after adding a small bounded principal perturbation to a uniformly elliptic
coefficient. -/
lemma isCoercive_energyIntegrand_add_bounded_principal
    (h : UniformlyEllipticOn Ω a lam Lam) (hMu_lt : Mu < lam)
    (hp : MatrixBilinearBoundedOn Ω p Mu)
    {x : X} (hx : x ∈ Ω) {b₀ : EuclideanSpace ℝ n} {c₀ : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : rho ≤ c₀)
    (hrho : beta ^ 2 / (2 * (lam - Mu)) < rho) :
    IsCoercive (energyIntegrand (a x + p x) b₀ c₀) :=
  PDE.isCoercive_energyIntegrand_add_bounded_principal (h.lower_bound hx) hMu_lt
    (hp hx) hb hc hrho

grind_pattern isCoercive_energyIntegrand_add_bounded_principal =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, ‖b₀‖ ≤ beta, rho ≤ c₀,
  Mu < lam, MatrixBilinearBoundedOn Ω p Mu,
  beta ^ 2 / (2 * (lam - Mu)) < rho,
  IsCoercive (energyIntegrand (a x + p x) b₀ c₀)

/-- Coefficient-field version of
`UniformlyEllipticOn.isCoercive_energyIntegrand_add_bounded_principal`. -/
lemma isCoercive_energyIntegrand_add_bounded_principal_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hMu_lt : Mu < lam)
    (hp : MatrixBilinearBoundedOn Ω p Mu)
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → rho ≤ c x)
    (hrho : beta ^ 2 / (2 * (lam - Mu)) < rho) {x : X} (hx : x ∈ Ω) :
    IsCoercive (energyIntegrand (a x + p x) (b x) (c x)) :=
  h.isCoercive_energyIntegrand_add_bounded_principal hMu_lt hp hx (hb hx) (hc hx) hrho

/-- Zero-drift coercivity after adding a small bounded principal perturbation to a uniformly
elliptic coefficient and keeping a positive mass coefficient. -/
lemma isCoercive_energyIntegrand_add_bounded_principal_zero_drift
    (h : UniformlyEllipticOn Ω a lam Lam) (hMu_lt : Mu < lam)
    (hp : MatrixBilinearBoundedOn Ω p Mu)
    {x : X} (hx : x ∈ Ω) {c₀ : ℝ} (hc : 0 < c₀) :
    IsCoercive (energyIntegrand (a x + p x) 0 c₀) :=
  PDE.isCoercive_energyIntegrand_add_bounded_principal_zero_drift (h.lower_bound hx)
    hMu_lt (hp hx) hc

grind_pattern isCoercive_energyIntegrand_add_bounded_principal_zero_drift =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, Mu < lam,
  MatrixBilinearBoundedOn Ω p Mu, 0 < c₀,
  IsCoercive (energyIntegrand (a x + p x) 0 c₀)

/-- Coefficient-field version of
`UniformlyEllipticOn.isCoercive_energyIntegrand_add_bounded_principal_zero_drift`. -/
lemma isCoercive_energyIntegrand_add_bounded_principal_zero_drift_on
    (h : UniformlyEllipticOn Ω a lam Lam) (hMu_lt : Mu < lam)
    (hp : MatrixBilinearBoundedOn Ω p Mu)
    (hc : ∀ ⦃x⦄, x ∈ Ω → 0 < c x) {x : X} (hx : x ∈ Ω) :
    IsCoercive (energyIntegrand (a x + p x) 0 (c x)) :=
  h.isCoercive_energyIntegrand_add_bounded_principal_zero_drift hMu_lt hp hx (hc hx)

end UniformlyEllipticOn

end PDE

end TauCeti
