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
uniformly elliptic symmetric principal coefficient with a positive mass term.  The shifted
Laplacian model `energyIntegrand 1 0 c`, corresponding to `-Δ + c`, is included as the constant
coefficient test case.

For a nonsymmetric principal coefficient, first pass to `coefficientSymmetricPart` using the
uniform ellipticity API in `TauCeti.Analysis.PDE.UniformEllipticity`, then use the lemmas in
this file with the symmetric coefficient field.  This keeps the symmetric-part replacement
available to downstream energy-form consumers without duplicating every packaged coercivity
statement.

## Main declarations

* `TauCeti.PDE.zero_drift_flip_eq_and_isCoercive_energyIntegrand`: a symmetric principal
  coefficient, a quadratic lower bound, and positive mass give symmetry and coercivity.
* `TauCeti.PDE.UniformlyEllipticOn.zero_drift_flip_eq_and_isCoercive_energyIntegrand`:
  bundled uniform ellipticity wrapper for the same pointwise package.
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

end UniformlyEllipticOn

/-- The shifted Laplacian jet form is both symmetric and coercive when the mass is positive. -/
lemma energyIntegrand_one_zero_mass_flip_eq_and_isCoercive {c : ℝ} (hc : 0 < c) :
    (energyIntegrand (1 : Matrix n n ℝ) 0 c).flip =
        energyIntegrand (1 : Matrix n n ℝ) 0 c ∧
      IsCoercive (energyIntegrand (1 : Matrix n n ℝ) 0 c) :=
  ⟨energyIntegrand_one_zero_mass_flip_eq c, isCoercive_energyIntegrand_one_zero_mass hc⟩

end PDE

end TauCeti
