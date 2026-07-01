/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.SymmetricCoerciveEnergy
public import TauCeti.Analysis.PDE.UniformEllipticEnergy

/-!
# Coercive symmetric-part energy integrands

The finite-dimensional PDE energy API allows nonsymmetric principal coefficient matrices, but
the Dirichlet spectrum and self-adjoint weak formulations need symmetric bilinear forms.  The
symmetric part `coefficientSymmetricPart A = (A + Aᵀ) / 2` keeps the same diagonal quadratic
energy and preserves uniform ellipticity.  This file packages the corresponding zero-drift
consumer lemmas: replacing the principal coefficient by its symmetric part gives a symmetric
and coercive jet integrand whenever the original coefficient has the same ellipticity floor and
the mass coefficient is positive.

These are still pointwise statements on jets `ℝ × EuclideanSpace ℝ n`; no Sobolev space or
integrated weak form is introduced here.

## Main declarations

* the `min_lam_mass_mul_norm_sq_le_...` lemmas: the explicit diagonal lower bound for
  the symmetric-part zero-drift integrand.
* `TauCeti.PDE.energyIntegrand_coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive`:
  symmetry and coercivity of the symmetric-part zero-drift integrand.
* the `UniformlyEllipticOn` wrappers: the coefficient-field versions of these estimates.
* `TauCeti.PDE.energyIntegrand_coefficientSymmetricPart_zero_drift_self_eq` and its
  `_on` wrapper: replacing the coefficient by its symmetric part does not change the
  zero-drift diagonal energy density.
-/

public section

namespace TauCeti

namespace PDE

open Matrix

variable {X n : Type*} [Fintype n] [DecidableEq n]
variable {lam Lam c₀ : ℝ}

/-- Replacing the principal coefficient by its symmetric part does not change the diagonal
zero-drift energy density. -/
@[simp]
lemma energyIntegrand_coefficientSymmetricPart_zero_drift_self_eq
    (A : Matrix n n ℝ) (c₀ : ℝ) (U : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand (coefficientSymmetricPart A) 0 c₀ U U =
      energyIntegrand A 0 c₀ U U :=
  energyIntegrand_coefficientSymmetricPart_self A 0 c₀ U

/-- Explicit diagonal lower bound for the symmetric-part zero-drift integrand, from a
quadratic lower bound for the original coefficient and a nonnegative mass coefficient. -/
lemma min_lam_mass_mul_norm_sq_le_energyIntegrand_coefficientSymmetricPart_zero_drift_self
    {A : Matrix n n ℝ} (hlam : 0 ≤ lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hc : 0 ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    min lam c₀ * ‖U‖ ^ 2 ≤ energyIntegrand (coefficientSymmetricPart A) 0 c₀ U U :=
  min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self hlam
    (fun ξ => by simpa using hA ξ) hc U

/-- The symmetric-part zero-drift jet integrand is both symmetric and coercive when the
original principal coefficient has a positive quadratic lower bound and the mass is positive.

This is the raw pointwise package used before the integrated weak form is sent to
Lax--Milgram and the symmetric-operator API. -/
lemma energyIntegrand_coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive
    {A : Matrix n n ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hc : 0 < c₀) :
    (energyIntegrand (coefficientSymmetricPart A) 0 c₀).flip =
        energyIntegrand (coefficientSymmetricPart A) 0 c₀ ∧
      IsCoercive (energyIntegrand (coefficientSymmetricPart A) 0 c₀) :=
  zero_drift_flip_eq_and_isCoercive_energyIntegrand hlam
    (fun ξ => by simpa using hA ξ) (coefficientSymmetricPart_isSymm A) hc

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ}

/-- Replacing a coefficient field by its symmetric part does not change the zero-drift
diagonal energy density at points of the domain. -/
@[simp]
lemma energyIntegrand_coefficientSymmetricPart_zero_drift_self_eq_on
    (a : X → Matrix n n ℝ) (c : X → ℝ) {x : X} (U : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 (c x) U U =
      energyIntegrand (a x) 0 (c x) U U :=
  energyIntegrand_coefficientSymmetricPart_zero_drift_self_eq (a x) (c x) U

/-- The explicit diagonal lower bound for the symmetric-part zero-drift integrand of a
uniformly elliptic principal coefficient field. -/
lemma min_lam_mass_mul_norm_sq_le_energyIntegrand_coefficientSymmetricPart_zero_drift_self
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) {c₀ : ℝ}
    (hc : 0 ≤ c₀) (U : ℝ × EuclideanSpace ℝ n) :
    min lam c₀ * ‖U‖ ^ 2 ≤
      energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 c₀ U U :=
  PDE.min_lam_mass_mul_norm_sq_le_energyIntegrand_coefficientSymmetricPart_zero_drift_self
    h.pos.le (h.lower_bound hx) hc U

/-- Coefficient-field version of the explicit diagonal lower bound for symmetric-part
zero-drift integrands. -/
lemma min_lam_mass_mul_norm_sq_le_energyIntegrand_coefficientSymmetricPart_zero_drift_self_on
    (h : UniformlyEllipticOn Ω a lam Lam) {c : X → ℝ}
    (hc : ∀ ⦃x⦄, x ∈ Ω → 0 ≤ c x) {x : X} (hx : x ∈ Ω)
    (U : ℝ × EuclideanSpace ℝ n) :
    min lam (c x) * ‖U‖ ^ 2 ≤
      energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 (c x) U U :=
  h.min_lam_mass_mul_norm_sq_le_energyIntegrand_coefficientSymmetricPart_zero_drift_self
    hx (hc hx) U

/-- For a uniformly elliptic principal coefficient field, the symmetric-part zero-drift jet
form is both symmetric and coercive at every point where the mass is positive. -/
lemma energyIntegrand_coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) {c₀ : ℝ}
    (hc : 0 < c₀) :
    (energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 c₀).flip =
        energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 c₀ ∧
      IsCoercive (energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 c₀) :=
  PDE.energyIntegrand_coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive
    h.pos (h.lower_bound hx) hc

/-- Coefficient-field version of symmetry and coercivity for the symmetric-part zero-drift
jet integrand. -/
lemma energyIntegrand_coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive_on
    (h : UniformlyEllipticOn Ω a lam Lam) {c : X → ℝ}
    (hc : ∀ ⦃x⦄, x ∈ Ω → 0 < c x) {x : X} (hx : x ∈ Ω) :
    (energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 (c x)).flip =
        energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 (c x) ∧
      IsCoercive (energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 (c x)) :=
  h.energyIntegrand_coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive hx (hc hx)

end UniformlyEllipticOn

end PDE

end TauCeti
