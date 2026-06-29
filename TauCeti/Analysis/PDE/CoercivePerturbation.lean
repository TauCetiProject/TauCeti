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
* `TauCeti.PDE.min_one_mass_mul_norm_sq_le_energyIntegrand_one_add_principal_mass_self`:
  explicit shifted-Laplacian diagonal lower bound after such perturbations.

The perturbation argument is the standard monotonicity of the quadratic energy density in
the energy method, as in Evans, *Partial Differential Equations*, Chapter 6.
-/

public section

namespace TauCeti

namespace PDE

open Matrix
open scoped InnerProductSpace

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {A B : Matrix n n ℝ} {b₀ : EuclideanSpace ℝ n} {c₀ d : ℝ}

/-- A coercive pointwise energy integrand remains coercive after adding a nonnegative
principal quadratic form and a nonnegative mass coefficient. -/
lemma isCoercive_energyIntegrand_add_principal_mass_of_isCoercive
    (h : IsCoercive (energyIntegrand A b₀ c₀))
    (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ) (hd : 0 ≤ d) :
    IsCoercive (energyIntegrand (A + B) b₀ (c₀ + d)) := by
  refine TauCeti.IsCoercive.mono
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

grind_pattern isCoercive_energyIntegrand_add_principal_mass_of_isCoercive =>
  IsCoercive (energyIntegrand A b₀ c₀), 0 ≤ d,
  IsCoercive (energyIntegrand (A + B) b₀ (c₀ + d))

/-- The shifted Laplacian diagonal lower bound remains valid after adding a nonnegative
principal quadratic form and a nonnegative mass coefficient. -/
lemma min_one_mass_mul_norm_sq_le_energyIntegrand_one_add_principal_mass_self {c d : ℝ}
    (hc : 0 ≤ c) (hB : ∀ ξ : EuclideanSpace ℝ n, 0 ≤ B.toQuadraticForm' ξ)
    (hd : 0 ≤ d) (U : ℝ × EuclideanSpace ℝ n) :
    min 1 c * ‖U‖ ^ 2 ≤ energyIntegrand ((1 : Matrix n n ℝ) + B) 0 (c + d) U U :=
  calc
    min 1 c * ‖U‖ ^ 2 ≤ min 1 (c + d) * ‖U‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_min_left 1 (le_add_of_nonneg_right hd))
        (sq_nonneg ‖U‖)
    _ ≤ energyIntegrand ((1 : Matrix n n ℝ) + B) 0 (c + d) U U :=
      min_lam_mass_mul_norm_sq_le_energyIntegrand_zero_drift_self zero_le_one
        (A := (1 : Matrix n n ℝ) + B)
        (lower_bound_toQuadraticForm'_add (A := (1 : Matrix n n ℝ)) (B := B)
          (by intro ξ; simp) hB)
        (add_nonneg hc hd) U

end PDE

end TauCeti
