/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PDE.EnergyFormLinearity
public import TauCeti.Analysis.PDE.CoerciveEnergy

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

* `TauCeti.PDE.energyIntegrand_le_add_principal_mass_self`: a diagonal energy integrand is
  bounded above by adding a nonnegative principal and mass perturbation.
* `TauCeti.PDE.isCoercive_energyIntegrand_add_principal_mass_of_isCoercive`: coercivity is
  preserved by such nonnegative perturbations.
* `TauCeti.PDE.min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_principal_mass_self`:
  the explicit coercive lower bound after such a perturbation.
* `TauCeti.PDE.UniformlyEllipticOn` wrappers for the explicit perturbed diagonal estimate.
* `TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyIntegrand_add_principal_mass` and
  `TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyIntegrand_add_principal_mass_on`:
  `UniformlyEllipticOn` wrappers for constant and coefficient-field perturbations.

The perturbation argument is the standard monotonicity of the quadratic energy density in
the energy method, as in Evans, *Partial Differential Equations*, Chapter 6.
-/

public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {X n : Type*} [Fintype n] [DecidableEq n]

variable {A B : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ d lam mu beta : ℝ}

private theorem isCoercive_mono {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {L M : E →L[ℝ] E →L[ℝ] ℝ} (hL : IsCoercive L) (hLM : ∀ u, L u u ≤ M u u) :
    IsCoercive M := by
  rcases hL with ⟨K, hKpos, hK⟩
  exact ⟨K, hKpos, fun u => (hK u).trans (hLM u)⟩

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
    IsCoercive (energyIntegrand (A + B) b₀ (c₀ + d)) :=
  isCoercive_mono h (energyIntegrand_le_add_principal_mass_self hB hd)

grind_pattern isCoercive_energyIntegrand_add_principal_mass_of_isCoercive =>
  IsCoercive (energyIntegrand A b₀ c₀), 0 ≤ d,
  IsCoercive (energyIntegrand (A + B) b₀ (c₀ + d))

/-- The explicit coercive diagonal estimate remains true after adding a nonnegative principal
quadratic form and a nonnegative mass coefficient. -/
lemma min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_principal_mass_self
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (hmu : beta ^ 2 / (2 * lam) < mu)
    (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ) (hd : 0 ≤ d)
    (U : ℝ × EuclideanSpace ℝ n) :
    min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U‖ ^ 2
      ≤ energyIntegrand (A + B) b₀ (c₀ + d) U U :=
  min_coercivityConstant_mul_norm_sq_le_energyIntegrand_self hlam
    (lower_bound_toQuadraticForm'_add hA hB) hb (hc.trans (le_add_of_nonneg_right hd)) hmu U

namespace UniformlyEllipticOn

variable {Ω : Set X} {a p : X → Matrix n n ℝ} {b : X → EuclideanSpace ℝ n}
variable {c e : X → ℝ} {Lam : ℝ}

/-- The explicit coercive diagonal estimate for a uniformly elliptic principal coefficient
after adding a nonnegative principal matrix and nonnegative mass perturbation. -/
lemma min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_principal_mass_self
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    {b₀ : EuclideanSpace ℝ n} {c₀ d : ℝ} {B : Matrix n n ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (hmu : beta ^ 2 / (2 * lam) < mu)
    (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ) (hd : 0 ≤ d)
    (U : ℝ × EuclideanSpace ℝ n) :
    min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U‖ ^ 2
      ≤ energyIntegrand (a x + B) b₀ (c₀ + d) U U :=
  PDE.min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_principal_mass_self h.pos
    (h.lower_bound hx) hb hc hmu hB hd U

/-- The coefficient-field version of the explicit coercive diagonal estimate after adding
nonnegative principal and mass perturbation fields. -/
lemma min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_principal_mass_self_on
    (h : UniformlyEllipticOn Ω a lam Lam)
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → mu ≤ c x) (hmu : beta ^ 2 / (2 * lam) < mu)
    (hp : ∀ ⦃x⦄, x ∈ Ω → ∀ ξ : EuclideanSpace ℝ n, 0 ≤ (p x).toQuadraticForm' ξ)
    (he : ∀ ⦃x⦄, x ∈ Ω → 0 ≤ e x) {x : X} (hx : x ∈ Ω)
    (U : ℝ × EuclideanSpace ℝ n) :
    min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U‖ ^ 2
      ≤ energyIntegrand (a x + p x) (b x) (c x + e x) U U :=
  h.min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_principal_mass_self hx
    (hb hx) (hc hx) hmu (hp hx) (he hx) U

/-- Pointwise coercivity for a uniformly elliptic principal coefficient after adding a
nonnegative principal matrix and nonnegative mass perturbation. -/
lemma isCoercive_energyIntegrand_add_principal_mass
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    {b₀ : EuclideanSpace ℝ n} {c₀ d : ℝ} {B : Matrix n n ℝ}
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (hmu : beta ^ 2 / (2 * lam) < mu)
    (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ) (hd : 0 ≤ d) :
    IsCoercive (energyIntegrand (a x + B) b₀ (c₀ + d)) :=
  isCoercive_energyIntegrand_of_bounds h.pos
    (lower_bound_toQuadraticForm'_add (h.lower_bound hx) hB) hb
    (hc.trans (le_add_of_nonneg_right hd)) hmu

grind_pattern isCoercive_energyIntegrand_add_principal_mass =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, ‖b₀‖ ≤ beta, mu ≤ c₀,
  beta ^ 2 / (2 * lam) < mu, 0 ≤ d,
  IsCoercive (energyIntegrand (a x + B) b₀ (c₀ + d))

/-- Coefficient-field version of pointwise coercivity after adding nonnegative principal and
mass perturbation fields. -/
lemma isCoercive_energyIntegrand_add_principal_mass_on
    (h : UniformlyEllipticOn Ω a lam Lam)
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → mu ≤ c x) (hmu : beta ^ 2 / (2 * lam) < mu)
    (hp : ∀ ⦃x⦄, x ∈ Ω → ∀ ξ : EuclideanSpace ℝ n, 0 ≤ (p x).toQuadraticForm' ξ)
    (he : ∀ ⦃x⦄, x ∈ Ω → 0 ≤ e x) {x : X} (hx : x ∈ Ω) :
    IsCoercive (energyIntegrand (a x + p x) (b x) (c x + e x)) :=
  h.isCoercive_energyIntegrand_add_principal_mass hx (hb hx) (hc hx) hmu (hp hx) (he hx)

end UniformlyEllipticOn

end PDE

end TauCeti
