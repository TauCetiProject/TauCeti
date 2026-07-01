/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.SymmetricEnergy
public import TauCeti.Analysis.PDE.CoerciveEnergy

/-!
# Symmetric coercive pointwise energy integrands

Lane D of the PDE roadmap eventually feeds an integrated weak energy form into
Lax--Milgram and, for the Dirichlet spectrum, into the symmetric-operator API.  The existing
pointwise files prove symmetry of zero-drift jet forms and coercivity of uniformly elliptic
jet forms separately.  This file packages the common zero-drift case where both estimates hold
for the same pointwise integrand.

The statements remain finite-dimensional and pointwise: a jet is an element of
`ℝ × EuclideanSpace ℝ n`, representing `(u, ∇u)` at one point.  The main consumer form is a
uniformly elliptic symmetric principal coefficient with a positive mass term; the file also
records the corresponding symmetric-part replacement for nonsymmetric uniformly elliptic
coefficients.  The shifted Laplacian model `energyIntegrand 1 0 c`, corresponding to `-Δ + c`,
is included as the constant coefficient test case.

## Main declarations

* `TauCeti.PDE.zero_drift_flip_eq_and_isCoercive_energyIntegrand`: a symmetric principal
  coefficient, a quadratic lower bound, and positive mass give symmetry and coercivity.
* `TauCeti.PDE.UniformlyEllipticOn.zero_drift_flip_eq_and_isCoercive_energyIntegrand`:
  bundled uniform ellipticity wrapper for the same pointwise package.
* `TauCeti.PDE.energyIntegrand_coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive`:
  symmetric-part replacement form for a coefficient with the same quadratic lower bound.
* `TauCeti.PDE.UniformlyEllipticOn`:
  `energyIntegrand_coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive` is the
  bundled uniformly elliptic symmetric-part replacement wrapper.
* `TauCeti.PDE.energyIntegrand_one_zero_mass_flip_eq_and_isCoercive`: symmetry and
  coercivity of the shifted Laplacian model with positive mass.
-/

public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {X n : Type*} [Fintype n] [DecidableEq n]

variable {lam : ℝ}

/-- A symmetric principal coefficient with a positive quadratic lower bound and a positive
mass coefficient gives a zero-drift pointwise jet form that is both symmetric and coercive.

This is the raw pointwise package later integrated energy forms need before applying the
Lax--Milgram and symmetric spectral APIs. -/
lemma zero_drift_flip_eq_and_isCoercive_energyIntegrand {A : Matrix n n ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (ha : A.IsSymm) {c₀ : ℝ} (hc : 0 < c₀) :
    (energyIntegrand A 0 c₀).flip = energyIntegrand A 0 c₀ ∧
      IsCoercive (energyIntegrand A 0 c₀) :=
  ⟨energyIntegrand_zero_drift_flip_eq_of_isSymm ha c₀,
    isCoercive_energyIntegrand_zero_drift hlam hc hA⟩

/-- Replacing the principal coefficient by its symmetric part gives a zero-drift pointwise
jet form that is both symmetric and coercive, provided the original coefficient has the
same positive quadratic lower bound. -/
lemma energyIntegrand_coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive
    {A : Matrix n n ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    {c₀ : ℝ} (hc : 0 < c₀) :
    (energyIntegrand (coefficientSymmetricPart A) 0 c₀).flip =
        energyIntegrand (coefficientSymmetricPart A) 0 c₀ ∧
      IsCoercive (energyIntegrand (coefficientSymmetricPart A) 0 c₀) :=
  zero_drift_flip_eq_and_isCoercive_energyIntegrand hlam
    (fun ξ => by simpa [toQuadraticForm'_coefficientSymmetricPart] using hA ξ)
    (coefficientSymmetricPart_isSymm A) hc

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ} {Lam : ℝ}

/-- For a symmetric uniformly elliptic principal coefficient and a positive mass coefficient,
the zero-drift pointwise jet form is both symmetric and coercive.

This is the bundled uniform ellipticity wrapper around
`PDE.zero_drift_flip_eq_and_isCoercive_energyIntegrand`. -/
lemma zero_drift_flip_eq_and_isCoercive_energyIntegrand
    (h : UniformlyEllipticOn Ω a lam Lam) (ha : ∀ ⦃x⦄, x ∈ Ω → (a x).IsSymm)
    {x : X} (hx : x ∈ Ω) {c₀ : ℝ} (hc : 0 < c₀) :
    (energyIntegrand (a x) 0 c₀).flip = energyIntegrand (a x) 0 c₀ ∧
      IsCoercive (energyIntegrand (a x) 0 c₀) :=
  PDE.zero_drift_flip_eq_and_isCoercive_energyIntegrand h.pos (h.lower_bound hx) (ha hx) hc

/-- Coefficient-field form of
`UniformlyEllipticOn.zero_drift_flip_eq_and_isCoercive_energyIntegrand`. -/
lemma zero_drift_flip_eq_and_isCoercive_energyIntegrand_on
    (h : UniformlyEllipticOn Ω a lam Lam) (ha : ∀ ⦃x⦄, x ∈ Ω → (a x).IsSymm)
    {c : X → ℝ} (hc : ∀ ⦃x⦄, x ∈ Ω → 0 < c x) {x : X} (hx : x ∈ Ω) :
    (energyIntegrand (a x) 0 (c x)).flip = energyIntegrand (a x) 0 (c x) ∧
      IsCoercive (energyIntegrand (a x) 0 (c x)) :=
  h.zero_drift_flip_eq_and_isCoercive_energyIntegrand ha hx (hc hx)

/-- For a uniformly elliptic coefficient, replacing the principal coefficient by its
symmetric part gives a zero-drift pointwise jet form that is both symmetric and coercive. -/
lemma energyIntegrand_coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) {c₀ : ℝ}
    (hc : 0 < c₀) :
    (energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 c₀).flip =
        energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 c₀ ∧
      IsCoercive (energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 c₀) :=
  (h.coefficientSymmetricPart).zero_drift_flip_eq_and_isCoercive_energyIntegrand
    (fun _ _ => PDE.coefficientSymmetricPart_isSymm _) hx hc

/-- Coefficient-field form of
`UniformlyEllipticOn.energyIntegrand_coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive`.
-/
lemma energyIntegrand_coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive_on
    (h : UniformlyEllipticOn Ω a lam Lam) {c : X → ℝ}
    (hc : ∀ ⦃x⦄, x ∈ Ω → 0 < c x) {x : X} (hx : x ∈ Ω) :
    (energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 (c x)).flip =
        energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 (c x) ∧
      IsCoercive (energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 (c x)) :=
  h.energyIntegrand_coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive hx (hc hx)

end UniformlyEllipticOn

/-- The shifted Laplacian jet form is both symmetric and coercive when the mass is positive. -/
lemma energyIntegrand_one_zero_mass_flip_eq_and_isCoercive {c : ℝ} (hc : 0 < c) :
    (energyIntegrand (1 : Matrix n n ℝ) 0 c).flip =
        energyIntegrand (1 : Matrix n n ℝ) 0 c ∧
      IsCoercive (energyIntegrand (1 : Matrix n n ℝ) 0 c) :=
  ⟨energyIntegrand_one_zero_mass_flip_eq c, isCoercive_energyIntegrand_one_zero_mass hc⟩

end PDE

end TauCeti
