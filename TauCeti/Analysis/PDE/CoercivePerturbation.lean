/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.CoerciveEnergy
public import TauCeti.Analysis.PDE.EnergyFormLinearity
public import TauCeti.Analysis.InnerProductSpace.LaxMilgram

/-!
# Coercive energy integrands under nonnegative perturbations

The pointwise Lax--Milgram layer in `TauCeti.Analysis.PDE.CoerciveEnergy` proves coercivity
of the finite-dimensional jet integrand `energyIntegrand A b c` from a principal lower
bound, a drift bound, and a sufficiently positive mass floor.  This file records the
corresponding monotonicity: adding a principal coefficient with nonnegative quadratic form,
and adding a nonnegative mass coefficient, preserves coercivity.

This is the finite-dimensional bookkeeping used when the later weak energy form is split
into a coercive model plus a nonnegative potential or principal perturbation.  It is still
pointwise: no Sobolev space, weak derivative, or integrated energy form is introduced here.

## Main declarations

* `TauCeti.PDE.isCoercive_energyIntegrand_add_principal_mass_of_isCoercive`: coercivity is
  preserved by such nonnegative perturbations.
* `TauCeti.PDE.min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_principal_mass_self`:
  the explicit diagonal lower bound after such perturbations.
* `TauCeti.PDE.min_lam_mass_mul_norm_sq_le_energyIntegrand_add_principal_mass_zero_drift_self`:
  the zero-drift explicit diagonal lower bound after such perturbations.
* `TauCeti.PDE.UniformlyEllipticOn.
    min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_principal_mass_self`: the
  same explicit estimate from a bundled uniform ellipticity hypothesis.

The perturbation argument is the standard monotonicity of the quadratic energy density in
the energy method, as in Evans, *Partial Differential Equations*, Chapter 6.
-/

public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {A B : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ d lam mu beta : ℝ}

/-- A diagonal energy integrand is bounded above by its nonnegative principal and mass
perturbation. -/
lemma energyIntegrand_le_add_principal_mass_self
    (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ) (hd : 0 ≤ d)
    (U : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand A b₀ c₀ U U ≤ energyIntegrand (A + B) b₀ (c₀ + d) U U := by
  have hpert : 0 ≤ energyIntegrand B 0 d U U := by
    rw [energyIntegrand_self]
    simpa using add_nonneg (hB U.2) (mul_nonneg hd (sq_nonneg U.1))
  calc
    energyIntegrand A b₀ c₀ U U
        ≤ energyIntegrand A b₀ c₀ U U + energyIntegrand B 0 d U U :=
      le_add_of_nonneg_right hpert
    _ = energyIntegrand (A + B) b₀ (c₀ + d) U U := by
      simpa using
        (energyIntegrand_add_apply (A := A) (B := B) (b := b₀) (d := 0) (c := c₀)
          (e := d) (U := U) (V := U)).symm

/-- A coercive pointwise energy integrand remains coercive after adding a nonnegative
principal quadratic form and a nonnegative mass coefficient. -/
lemma isCoercive_energyIntegrand_add_principal_mass_of_isCoercive
    (h : IsCoercive (energyIntegrand A b₀ c₀))
    (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ) (hd : 0 ≤ d) :
    IsCoercive (energyIntegrand (A + B) b₀ (c₀ + d)) := by
  rcases h with ⟨K, hKpos, hK⟩
  refine ⟨K, hKpos, fun U => (hK U).trans ?_⟩
  exact energyIntegrand_le_add_principal_mass_self hB hd U

grind_pattern isCoercive_energyIntegrand_add_principal_mass_of_isCoercive =>
  IsCoercive (energyIntegrand A b₀ c₀), 0 ≤ d,
  IsCoercive (energyIntegrand (A + B) b₀ (c₀ + d))

/-- The explicit coercive diagonal lower bound remains valid after adding a nonnegative
principal quadratic form and a nonnegative mass coefficient. -/
lemma min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_principal_mass_self
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (hmu : beta ^ 2 / (2 * lam) < mu)
    (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ) (hd : 0 ≤ d)
    (U : ℝ × EuclideanSpace ℝ n) :
    min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U‖ ^ 2
      ≤ energyIntegrand (A + B) b₀ (c₀ + d) U U :=
  (min_coercivityConstant_mul_norm_sq_le_energyIntegrand_self hlam hA hb hc hmu U).trans
    (energyIntegrand_le_add_principal_mass_self hB hd U)

/-- The zero-drift diagonal lower bound remains valid after adding a nonnegative principal
quadratic form and a nonnegative mass coefficient. -/
lemma min_lam_mass_mul_norm_sq_le_energyIntegrand_add_principal_mass_zero_drift_self
    {lam c d : ℝ} (hlam : 0 ≤ lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hc : 0 ≤ c) (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ)
    (hd : 0 ≤ d) (U : ℝ × EuclideanSpace ℝ n) :
    min lam c * ‖U‖ ^ 2 ≤ energyIntegrand (A + B) 0 (c + d) U U :=
  calc
    min lam c * ‖U‖ ^ 2 ≤ min lam (c + d) * ‖U‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_min_left lam (le_add_of_nonneg_right hd))
        (sq_nonneg ‖U‖)
    _ ≤ energyIntegrand (A + B) 0 (c + d) U U :=
      min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self hlam
        (lower_bound_toQuadraticForm'_add hA hB)
        (add_nonneg hc hd) U

namespace UniformlyEllipticOn

variable {X : Type*} {Ω : Set X} {a p : X → Matrix n n ℝ}
variable {lam Lam beta mu : ℝ}

/-- The explicit coercive diagonal lower bound from uniform ellipticity remains valid after
adding a nonnegative principal quadratic form and a nonnegative mass coefficient. -/
lemma min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_principal_mass_self
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    {B : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ q : ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (hmu : beta ^ 2 / (2 * lam) < mu)
    (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ) (hq : 0 ≤ q)
    (U : ℝ × EuclideanSpace ℝ n) :
    min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U‖ ^ 2
      ≤ energyIntegrand (a x + B) b₀ (c₀ + q) U U :=
  PDE.min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_principal_mass_self h.pos
    (h.lower_bound hx) hb hc hmu hB hq U

grind_pattern min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_principal_mass_self =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, ‖b₀‖ ≤ beta, mu ≤ c₀,
  beta ^ 2 / (2 * lam) < mu, 0 ≤ q,
  energyIntegrand (a x + B) b₀ (c₀ + q) U U

/-- The coefficient-field version of the explicit perturbed coercive diagonal estimate from
uniform ellipticity and a mass floor. -/
lemma min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_principal_mass_self_on
    (h : UniformlyEllipticOn Ω a lam Lam)
    {b : X → EuclideanSpace ℝ n} {c q : X → ℝ}
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → mu ≤ c x)
    (hmu : beta ^ 2 / (2 * lam) < mu)
    (hp : ∀ ⦃x⦄, x ∈ Ω → ∀ ξ : EuclideanSpace ℝ n, 0 ≤ (p x).toQuadraticForm' ξ)
    (hq : ∀ ⦃x⦄, x ∈ Ω → 0 ≤ q x) {x : X} (hx : x ∈ Ω)
    (U : ℝ × EuclideanSpace ℝ n) :
    min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U‖ ^ 2
      ≤ energyIntegrand (a x + p x) (b x) (c x + q x) U U :=
  h.min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_principal_mass_self hx
    (hb hx) (hc hx) hmu (hp hx) (hq hx) U

end UniformlyEllipticOn

end PDE

end TauCeti
