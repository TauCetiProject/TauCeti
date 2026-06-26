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
Lax--Milgram and, for the Dirichlet spectrum, into the symmetric-operator API.  The existing
pointwise files prove symmetry of zero-drift jet forms and coercivity of uniformly elliptic
jet forms separately.  This file packages the common zero-drift case where both estimates hold
for the same pointwise integrand.

The statements remain finite-dimensional and pointwise: a jet is an element of
`ℝ × EuclideanSpace ℝ n`, representing `(u, ∇u)` at one point.  The main consumer form is a
uniformly elliptic symmetric principal coefficient with a positive mass term.  The shifted
Laplacian model `energyIntegrand 1 0 c`, corresponding to `-Δ + c`, is included as the constant
coefficient test case.

## Main declarations

* `TauCeti.PDE.energyIntegrand_zero_drift_flip_eq_on`: a symmetric coefficient field gives a
  bundled symmetric zero-drift jet form at each point.
* `TauCeti.PDE.UniformlyEllipticOn.zero_drift_flip_eq_and_isCoercive_energyIntegrand`:
  uniform ellipticity, coefficient symmetry, and positive mass give symmetry and coercivity.
* `TauCeti.PDE.energyIntegrand_one_zero_mass_apply` and
  `TauCeti.PDE.energyIntegrand_one_zero_mass_self`: normal forms for the shifted Laplacian
  jet integrand.
* `TauCeti.PDE.norm_energyIntegrand_one_zero_mass_apply_le` and
  `TauCeti.PDE.opNorm_energyIntegrand_one_zero_mass_le`: boundedness of the shifted
  Laplacian jet integrand.
* `TauCeti.PDE.energyIntegrand_one_zero_mass_flip_eq` and
  `TauCeti.PDE.isCoercive_energyIntegrand_one_zero_mass`: symmetry and coercivity of the
  shifted Laplacian model with positive mass.
-/

public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {X n : Type*} [Fintype n] [DecidableEq n]

private lemma abs_dotProduct_one_mulVec_le (η ξ : EuclideanSpace ℝ n) :
    |η ⬝ᵥ ((1 : Matrix n n ℝ) *ᵥ ξ)| ≤ 1 * ‖η‖ * ‖ξ‖ := by
  rw [one_mulVec, one_mul]
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using
    abs_real_inner_le_norm η ξ

/-- A pointwise symmetric coefficient field gives a bundled symmetric zero-drift jet form at
each point of the domain. -/
@[simp]
lemma energyIntegrand_zero_drift_flip_eq_on {Ω : Set X} {a : X → Matrix n n ℝ}
    (ha : ∀ ⦃x⦄, x ∈ Ω → (a x).IsSymm) {x : X} (hx : x ∈ Ω) (c : X → ℝ) :
    (energyIntegrand (a x) 0 (c x)).flip = energyIntegrand (a x) 0 (c x) :=
  energyIntegrand_zero_drift_flip_eq_of_isSymm (ha hx) (c x)

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ} {lam Lam : ℝ}

/-- For a symmetric uniformly elliptic principal coefficient and a positive mass coefficient,
the zero-drift pointwise jet form is both symmetric and coercive.

This is the pointwise package later integrated energy forms need before applying the
Lax--Milgram and symmetric spectral APIs. -/
lemma zero_drift_flip_eq_and_isCoercive_energyIntegrand
    (h : UniformlyEllipticOn Ω a lam Lam) (ha : ∀ ⦃x⦄, x ∈ Ω → (a x).IsSymm)
    {x : X} (hx : x ∈ Ω) {c₀ : ℝ} (hc : 0 < c₀) :
    (energyIntegrand (a x) 0 c₀).flip = energyIntegrand (a x) 0 c₀ ∧
      IsCoercive (energyIntegrand (a x) 0 c₀) :=
  ⟨energyIntegrand_zero_drift_flip_eq_of_isSymm (ha hx) c₀,
    h.isCoercive_energyIntegrand_zero_drift hx hc⟩

/-- Coefficient-field form of
`UniformlyEllipticOn.zero_drift_flip_eq_and_isCoercive_energyIntegrand`. -/
lemma zero_drift_flip_eq_and_isCoercive_energyIntegrand_on
    (h : UniformlyEllipticOn Ω a lam Lam) (ha : ∀ ⦃x⦄, x ∈ Ω → (a x).IsSymm)
    {c : X → ℝ} (hc : ∀ ⦃x⦄, x ∈ Ω → 0 < c x) {x : X} (hx : x ∈ Ω) :
    (energyIntegrand (a x) 0 (c x)).flip = energyIntegrand (a x) 0 (c x) ∧
      IsCoercive (energyIntegrand (a x) 0 (c x)) :=
  h.zero_drift_flip_eq_and_isCoercive_energyIntegrand ha hx (hc hx)

end UniformlyEllipticOn

/-- The shifted Laplacian model `-Δ + c` has jet form
`(U, V) ↦ ∇u · ∇v + c u v`. -/
@[simp]
lemma energyIntegrand_one_zero_mass_apply (c : ℝ) (U V : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand (1 : Matrix n n ℝ) 0 c U V = V.2 ⬝ᵥ U.2 + c * U.1 * V.1 := by
  simp [energyIntegrand_apply, massForm_apply]

/-- The shifted Laplacian model `-Δ + c` has diagonal jet density
`‖∇u‖² + c u²`. -/
@[simp]
lemma energyIntegrand_one_zero_mass_self (c : ℝ) (U : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand (1 : Matrix n n ℝ) 0 c U U = ‖U.2‖ ^ 2 + c * U.1 ^ 2 := by
  rw [energyIntegrand_self, toQuadraticForm'_one]
  simp

/-- Pointwise boundedness of the shifted Laplacian jet form with constant `1 + ‖c‖`. -/
lemma norm_energyIntegrand_one_zero_mass_apply_le (c : ℝ)
    (U V : ℝ × EuclideanSpace ℝ n) :
    ‖energyIntegrand (1 : Matrix n n ℝ) 0 c U V‖ ≤
      (1 + ‖c‖) * ‖U‖ * ‖V‖ := by
  simpa using
    norm_energyIntegrand_apply_le_of_bounds (n := n) (Lam := 1) (beta := 0) (b₀ := 0)
      (gamma := ‖c‖) zero_le_one
      (fun η ξ => abs_dotProduct_one_mulVec_le η ξ) (by simp) le_rfl U V

/-- Operator-norm boundedness of the shifted Laplacian jet form with constant `1 + ‖c‖`. -/
lemma opNorm_energyIntegrand_one_zero_mass_le (c : ℝ) :
    ‖energyIntegrand (1 : Matrix n n ℝ) 0 c‖ ≤ 1 + ‖c‖ := by
  simpa using
    opNorm_energyIntegrand_le_of_bounds (n := n) (Lam := 1) (beta := 0) (b₀ := 0)
      (gamma := ‖c‖) zero_le_one
      (fun η ξ => abs_dotProduct_one_mulVec_le η ξ) (by simp) le_rfl

/-- Bundled symmetry of the shifted Laplacian jet form. -/
@[simp]
lemma energyIntegrand_one_zero_mass_flip_eq (c : ℝ) :
    (energyIntegrand (1 : Matrix n n ℝ) 0 c).flip =
      energyIntegrand (1 : Matrix n n ℝ) 0 c :=
  energyIntegrand_zero_drift_flip_eq_of_isSymm isSymm_one c

/-- The shifted Laplacian jet form is coercive when the mass is positive. -/
lemma isCoercive_energyIntegrand_one_zero_mass {c : ℝ} (hc : 0 < c) :
    IsCoercive (energyIntegrand (1 : Matrix n n ℝ) 0 c) :=
  isCoercive_energyIntegrand_zero_drift zero_lt_one hc (by intro ξ; simp)

/-- The shifted Laplacian jet form is both symmetric and coercive when the mass is positive. -/
lemma energyIntegrand_one_zero_mass_flip_eq_and_isCoercive {c : ℝ} (hc : 0 < c) :
    (energyIntegrand (1 : Matrix n n ℝ) 0 c).flip =
        energyIntegrand (1 : Matrix n n ℝ) 0 c ∧
      IsCoercive (energyIntegrand (1 : Matrix n n ℝ) 0 c) :=
  ⟨energyIntegrand_one_zero_mass_flip_eq c, isCoercive_energyIntegrand_one_zero_mass hc⟩

/-- Explicit diagonal lower bound for the shifted Laplacian jet form with nonnegative mass. -/
lemma min_one_mass_mul_norm_sq_le_energyIntegrand_one_zero_mass_self {c : ℝ} (hc : 0 ≤ c)
    (U : ℝ × EuclideanSpace ℝ n) :
    min 1 c * ‖U‖ ^ 2 ≤ energyIntegrand (1 : Matrix n n ℝ) 0 c U U := by
  have hprod := min_mul_prod_norm_sq_le_add zero_le_one hc U
  rw [energyIntegrand_one_zero_mass_self]
  rw [Real.norm_eq_abs, sq_abs] at hprod
  simpa [one_mul] using hprod

end PDE

end TauCeti
