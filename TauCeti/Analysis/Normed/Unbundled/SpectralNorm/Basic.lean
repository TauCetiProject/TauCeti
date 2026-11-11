/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm

/-!
# Basic facts about the spectral norm

For an element of a field extension that is transcendental over a normed field `K`, the minimal
polynomial is zero, so its spectral norm over `K` is zero. In an algebraic normed field extension
of a complete ultrametric field the norm is the spectral norm, so an element `x` whose minimal
polynomial has degree `d` and constant coefficient `a₀` satisfies `‖x‖ ^ d = ‖a₀‖`.

## Main results

* `TauCeti.spectralNorm_eq_zero_of_not_isAlgebraic`: the spectral norm over `K` of an element that
  is transcendental over `K` is zero.
* `NormedAlgebra.norm_pow_natDegree_minpoly_eq_norm_coeff_zero`: `‖x‖ ^ d = ‖a₀‖` for `x` with
  minimal polynomial of degree `d` and constant coefficient `a₀`.
-/

public section

namespace TauCeti

open Polynomial

variable {K : Type*} [NormedField K]

/-- The spectral norm of an element that is transcendental over `K` is zero, since its minimal
polynomial is `0`. -/
theorem spectralNorm_eq_zero_of_not_isAlgebraic {L : Type*} [Field L] [Algebra K L] {y : L}
    (hy : ¬ IsAlgebraic K y) : spectralNorm K L y = 0 := by
  have h0 : spectralValueTerms (0 : K[X]) = 0 :=
    funext fun n ↦ spectralValueTerms_of_natDegree_le _ (by simp)
  rw [spectralNorm, minpoly.eq_zero fun h ↦ hy h.isAlgebraic, spectralValue, h0]
  exact ciSup_const

end TauCeti

/-- In an algebraic normed field extension `L` of a complete ultrametric field `K`, the norm of an
element `x` raised to the degree of its minimal polynomial is the norm of the constant coefficient
of that polynomial. -/
theorem NormedAlgebra.norm_pow_natDegree_minpoly_eq_norm_coeff_zero (K : Type*) {L : Type*}
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [NormedField L]
    [NormedAlgebra K L] [Algebra.IsAlgebraic K L] (x : L) :
    ‖x‖ ^ (minpoly K x).natDegree = ‖(minpoly K x).coeff 0‖ := by
  have hd : ((minpoly K x).natDegree : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)).ne'
  rw [NormedAlgebra.norm_eq_spectralNorm K, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
    ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hd, Real.rpow_one]
