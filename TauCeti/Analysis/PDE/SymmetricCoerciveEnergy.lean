/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.SymmetricEnergy
public import TauCeti.Analysis.PDE.UniformEllipticEnergy

/-!
# Symmetric coercive pointwise energy integrands

Lane D of the PDE roadmap eventually feeds an integrated weak energy form into
Lax--Milgram and, for the Dirichlet spectrum, into the symmetric-operator API. The existing
pointwise files prove symmetry of zero-drift jet forms and coercivity of uniformly elliptic
jet forms separately. This file packages the common zero-drift cases where both estimates
hold for the same pointwise integrand.

The statements remain finite-dimensional and pointwise: a jet is an element of
`ℝ × EuclideanSpace ℝ n`, representing `(u, ∇u)` at one point. The main consumer forms are
a symmetric uniformly elliptic principal coefficient with positive mass, and the symmetric
part of a uniformly elliptic principal coefficient. The shifted Laplacian model
`energyIntegrand 1 0 c`, corresponding to `-Δ + c`, is included as the constant-coefficient
test case.

## Main declarations

* `TauCeti.PDE.zero_drift_flip_eq_and_isCoercive_energyIntegrand`: a symmetric principal
  coefficient, a quadratic lower bound, and positive mass give symmetry and coercivity.
* `TauCeti.PDE.coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive_energyIntegrand`:
  the same package for the symmetric part of a principal coefficient.
* `TauCeti.PDE.UniformlyEllipticOn.zero_drift_flip_eq_and_isCoercive_energyIntegrand`:
  the uniformly elliptic wrapper for a symmetric coefficient field.
* the `UniformlyEllipticOn.coefficientSymmetricPart_...` wrapper after replacing the
  principal coefficient by its symmetric part.
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

/-- The symmetric part of a principal coefficient gives a zero-drift pointwise jet form that
is both symmetric and coercive, provided the original coefficient has the same positive
quadratic lower bound.

The diagonal quadratic form is unchanged by `coefficientSymmetricPart`, so the coercivity
constant is the same as for the original principal coefficient. -/
lemma coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive_energyIntegrand
    {A : Matrix n n ℝ} (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    {c₀ : ℝ} (hc : 0 < c₀) :
    (energyIntegrand (coefficientSymmetricPart A) 0 c₀).flip =
        energyIntegrand (coefficientSymmetricPart A) 0 c₀ ∧
      IsCoercive (energyIntegrand (coefficientSymmetricPart A) 0 c₀) :=
  zero_drift_flip_eq_and_isCoercive_energyIntegrand hlam
    (fun ξ => by simpa using hA ξ) (coefficientSymmetricPart_isSymm A) hc

/-- The shifted Laplacian jet form is both symmetric and coercive when the mass is positive. -/
lemma energyIntegrand_one_zero_mass_flip_eq_and_isCoercive {c : ℝ} (hc : 0 < c) :
    (energyIntegrand (1 : Matrix n n ℝ) 0 c).flip =
        energyIntegrand (1 : Matrix n n ℝ) 0 c ∧
      IsCoercive (energyIntegrand (1 : Matrix n n ℝ) 0 c) :=
  ⟨energyIntegrand_one_zero_mass_flip_eq c, isCoercive_energyIntegrand_one_zero_mass hc⟩

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ} {Lam : ℝ}

/-- For a symmetric uniformly elliptic principal coefficient and a positive mass coefficient,
the zero-drift pointwise jet form is both symmetric and coercive.

This is the bundled uniform-ellipticity wrapper around
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

/-- For a uniformly elliptic principal coefficient and a positive mass coefficient, replacing
the principal coefficient by its symmetric part gives a pointwise jet form that is both
symmetric and coercive.

This is the pointwise package used to pass from a possibly nonsymmetric divergence-form
principal coefficient to a self-adjoint model with the same diagonal energy density. -/
lemma coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive_energyIntegrand
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω) {c₀ : ℝ} (hc : 0 < c₀) :
    (energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 c₀).flip =
        energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 c₀ ∧
      IsCoercive (energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 c₀) :=
  PDE.coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive_energyIntegrand h.pos
    (h.lower_bound hx) hc

/-- Coefficient-field form of
`UniformlyEllipticOn.coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive_energyIntegrand`. -/
lemma coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive_energyIntegrand_on
    (h : UniformlyEllipticOn Ω a lam Lam) {c : X → ℝ}
    (hc : ∀ ⦃x⦄, x ∈ Ω → 0 < c x) {x : X} (hx : x ∈ Ω) :
    (energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 (c x)).flip =
        energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 (c x) ∧
      IsCoercive (energyIntegrand (PDE.coefficientSymmetricPart (a x)) 0 (c x)) :=
  h.coefficientSymmetricPart_zero_drift_flip_eq_and_isCoercive_energyIntegrand hx (hc hx)

end UniformlyEllipticOn

end PDE

end TauCeti
