/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

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

* `TauCeti.PDE.energyIntegrand_add_principal_mass_self`: the diagonal of
  `energyIntegrand (A + B) b (c + d)` is the old diagonal plus the nonnegative principal
  and mass contributions.
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

/-- Adding a principal coefficient `B` and a mass coefficient `d` changes the diagonal
energy density by `B`'s quadratic form on the gradient plus `d u²`. -/
lemma energyIntegrand_add_principal_mass_self (U : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand (A + B) b₀ (c₀ + d) U U =
      energyIntegrand A b₀ c₀ U U + B.toQuadraticForm' U.2 + d * U.1 ^ 2 := by
  rw [energyIntegrand_self, energyIntegrand_self, toQuadraticForm'_add]
  ring

/-- The diagonal of `energyIntegrand (A + B) b c` is the old diagonal plus the quadratic
form of `B` on the gradient. -/
lemma energyIntegrand_add_principal_self (U : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand (A + B) b₀ c₀ U U =
      energyIntegrand A b₀ c₀ U U + B.toQuadraticForm' U.2 := by
  simpa using
    (energyIntegrand_add_principal_mass_self (A := A) (B := B) (b₀ := b₀) (c₀ := c₀)
      (d := 0) U)

/-- The diagonal of `energyIntegrand A b (c + d)` is the old diagonal plus `d u²`. -/
lemma energyIntegrand_add_mass_self (U : ℝ × EuclideanSpace ℝ n) :
    energyIntegrand A b₀ (c₀ + d) U U =
      energyIntegrand A b₀ c₀ U U + d * U.1 ^ 2 := by
  rw [energyIntegrand_self, energyIntegrand_self]
  ring

/-- A coercive pointwise energy integrand remains coercive after adding a nonnegative
principal quadratic form and a nonnegative mass coefficient. -/
lemma isCoercive_energyIntegrand_add_principal_mass_of_isCoercive
    (h : IsCoercive (energyIntegrand A b₀ c₀))
    (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ) (hd : 0 ≤ d) :
    IsCoercive (energyIntegrand (A + B) b₀ (c₀ + d)) := by
  rcases h with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, fun U => ?_⟩
  rw [energyIntegrand_add_principal_mass_self]
  calc
    C * ‖U‖ * ‖U‖ ≤ energyIntegrand A b₀ c₀ U U := hC U
    _ ≤ energyIntegrand A b₀ c₀ U U + (B.toQuadraticForm' U.2 + d * U.1 ^ 2) :=
      le_add_of_nonneg_right (add_nonneg (hB U.2) (mul_nonneg hd (sq_nonneg U.1)))
    _ = energyIntegrand A b₀ c₀ U U + B.toQuadraticForm' U.2 + d * U.1 ^ 2 := by
      ring

/-- The raw-bound coercivity lower estimate remains valid after adding a nonnegative
principal quadratic form and a nonnegative mass coefficient. -/
lemma min_coercivityConstant_mul_norm_sq_le_energyIntegrand_add_principal_mass_self
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (hmu : beta ^ 2 / (2 * lam) < mu)
    (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ) (hd : 0 ≤ d)
    (U : ℝ × EuclideanSpace ℝ n) :
    min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U‖ ^ 2
      ≤ energyIntegrand (A + B) b₀ (c₀ + d) U U := by
  rw [energyIntegrand_add_principal_mass_self]
  calc
    min (lam / 2) (mu - beta ^ 2 / (2 * lam)) * ‖U‖ ^ 2
        ≤ energyIntegrand A b₀ c₀ U U :=
      min_coercivityConstant_mul_norm_sq_le_energyIntegrand_self hlam hA hb hc hmu U
    _ ≤ energyIntegrand A b₀ c₀ U U + (B.toQuadraticForm' U.2 + d * U.1 ^ 2) :=
      le_add_of_nonneg_right (add_nonneg (hB U.2) (mul_nonneg hd (sq_nonneg U.1)))
    _ = energyIntegrand A b₀ c₀ U U + B.toQuadraticForm' U.2 + d * U.1 ^ 2 := by
      ring

/-- Coercivity from raw lower bounds is preserved after adding a nonnegative principal
quadratic form and a nonnegative mass coefficient. -/
lemma isCoercive_energyIntegrand_add_principal_mass_of_bounds (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ n, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hb : ‖b₀‖ ≤ beta) (hc : mu ≤ c₀) (hmu : beta ^ 2 / (2 * lam) < mu)
    (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ) (hd : 0 ≤ d) :
    IsCoercive (energyIntegrand (A + B) b₀ (c₀ + d)) :=
  isCoercive_energyIntegrand_add_principal_mass_of_isCoercive
    (isCoercive_energyIntegrand_of_bounds hlam hA hb hc hmu) hB hd

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
