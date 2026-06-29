/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.InnerProductSpace.LaxMilgram
public import TauCeti.Analysis.PDE.EnergyFormLinearity
public import TauCeti.Analysis.PDE.UniformEllipticEnergy

/-!
# Coercive energy integrands under nonnegative perturbations

The pointwise Lax--Milgram layer in `TauCeti.Analysis.PDE.UniformEllipticEnergy` proves
coercivity of the finite-dimensional jet integrand
`energyIntegrand A b c` from a uniformly elliptic principal coefficient, a drift bound, and
a sufficiently positive mass floor.  This file records the corresponding monotonicity:
adding a principal coefficient with nonnegative quadratic form, and adding a nonnegative
mass coefficient, preserves the same coercivity estimate.

This is the finite-dimensional bookkeeping used when the later weak energy form is split
into a coercive model plus a nonnegative potential or principal perturbation.  It is still
pointwise: no Sobolev space, weak derivative, or integrated energy form is introduced here.

## Main declarations

* `TauCeti.PDE.isCoercive_energyIntegrand_add_principal_mass_of_isCoercive`: coercivity is
  preserved by such nonnegative perturbations.
* `TauCeti.PDE.isCoercive_energyIntegrand_add_principal_mass_of_bounds`: the raw-bound
  coercivity estimate after perturbation.
* `TauCeti.PDE.UniformlyEllipticOn.isCoercive_energyIntegrand_add_principal_mass` and
  `..._on`: the same API for the roadmap's named uniform ellipticity hypothesis.

The perturbation argument is the standard monotonicity of the quadratic energy density in
the energy method, as in Evans, *Partial Differential Equations*, Chapter 6.
-/

public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {X n : Type*} [Fintype n] [DecidableEq n]

variable {A B : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ d : ℝ}
variable {lam beta mu : ℝ}

/-- A coercive pointwise energy integrand remains coercive after adding a nonnegative
principal quadratic form and a nonnegative mass coefficient. -/
lemma isCoercive_energyIntegrand_add_principal_mass_of_isCoercive
    (h : IsCoercive (energyIntegrand A b₀ c₀))
    (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ) (hd : 0 ≤ d) :
    IsCoercive (energyIntegrand (A + B) b₀ (c₀ + d)) := by
  refine TauCeti.IsCoercive.mono (V := ℝ × EuclideanSpace ℝ n)
    (B := energyIntegrand A b₀ c₀)
    (C := energyIntegrand (A + B) b₀ (c₀ + d)) h fun U => ?_
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

/-- Coercivity from raw lower bounds is preserved after adding a nonnegative principal
quadratic form and a nonnegative mass coefficient. -/
lemma isCoercive_energyIntegrand_add_principal_mass_of_bounds (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (hmu : beta ^ 2 / (2 * lam) < mu)
    (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ) (hd : 0 ≤ d) :
    IsCoercive (energyIntegrand (A + B) b₀ (c₀ + d)) :=
  isCoercive_energyIntegrand_of_bounds hlam (lower_bound_toQuadraticForm'_add hA hB) hb
    (hc.trans (le_add_of_nonneg_right hd)) hmu

/-- The shifted Laplacian jet form remains coercive after adding a nonnegative principal
quadratic form and a nonnegative mass coefficient. -/
lemma isCoercive_energyIntegrand_one_add_principal_mass {c d : ℝ}
    (hc : 0 < c) (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ)
    (hd : 0 ≤ d) :
    IsCoercive (energyIntegrand ((1 : Matrix n n ℝ) + B) 0 (c + d)) :=
  isCoercive_energyIntegrand_add_principal_mass_of_isCoercive
    (isCoercive_energyIntegrand_one_zero_mass (n := n) hc) hB hd

namespace UniformlyEllipticOn

variable {Ω : Set X} {a : X → Matrix n n ℝ} {b : X → EuclideanSpace ℝ n}
variable {c : X → ℝ} {p : X → Matrix n n ℝ} {q : X → ℝ}
variable {Lam : ℝ}

/-- The `UniformlyEllipticOn` coercivity estimate remains valid after adding a nonnegative
principal quadratic form and a nonnegative mass coefficient at the same point. -/
lemma isCoercive_energyIntegrand_add_principal_mass
    (h : UniformlyEllipticOn Ω a lam Lam) {x : X} (hx : x ∈ Ω)
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (hmu : beta ^ 2 / (2 * lam) < mu)
    (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ) (hd : 0 ≤ d) :
    IsCoercive (energyIntegrand (a x + B) b₀ (c₀ + d)) :=
  PDE.isCoercive_energyIntegrand_add_principal_mass_of_bounds h.pos (h.lower_bound hx)
    hb hc hmu hB hd

grind_pattern isCoercive_energyIntegrand_add_principal_mass =>
  UniformlyEllipticOn Ω a lam Lam, x ∈ Ω, ‖b₀‖ ≤ beta, mu ≤ c₀,
  beta ^ 2 / (2 * lam) < mu, 0 ≤ d,
  IsCoercive (energyIntegrand (a x + B) b₀ (c₀ + d))

/-- Domain version of coercivity preservation under nonnegative principal and mass
perturbations. -/
lemma isCoercive_energyIntegrand_add_principal_mass_on
    (h : UniformlyEllipticOn Ω a lam Lam)
    (hb : ∀ ⦃x⦄, x ∈ Ω → ‖b x‖ ≤ beta)
    (hc : ∀ ⦃x⦄, x ∈ Ω → mu ≤ c x) (hmu : beta ^ 2 / (2 * lam) < mu)
    (hp : ∀ ⦃x⦄, x ∈ Ω → ∀ ξ : EuclideanSpace ℝ n,
      0 ≤ (p x).toQuadraticForm' ξ)
    (hq : ∀ ⦃x⦄, x ∈ Ω → 0 ≤ q x) {x : X} (hx : x ∈ Ω) :
    IsCoercive (energyIntegrand (a x + p x) (b x) (c x + q x)) :=
  h.isCoercive_energyIntegrand_add_principal_mass hx (hb hx) (hc hx) hmu (hp hx) (hq hx)

end UniformlyEllipticOn

end PDE

end TauCeti
