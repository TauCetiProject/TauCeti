/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import TauCeti.Analysis.Normed.Ring.LogGauge.Rational

/-!
# Commensurability in algebraic extensions of complete fields

Let `K` be a complete nontrivially normed field with an ultrametric norm and `L` an algebraic
normed field extension of `K`. The norm of `L` is the spectral norm, so an element `x` whose
minimal polynomial has degree `d` and constant coefficient `a₀` satisfies `‖x‖ ^ d = ‖a₀‖`. Hence
every nonzero norm of `L` has a positive power that is a norm of `K`. If every nonzero norm of `K`
is a rational power of `‖ϖ‖` for a multiplicative pseudo-uniformiser `ϖ` of `K`, the same holds
in `L`: commensurability passes to algebraic extensions. For instance, the nonzero norms of an
algebraic closure of `ℚ_[p]` are the rational powers of `p`.

## Main results

* `NormedAlgebra.norm_pow_natDegree_minpoly_eq_norm_coeff_zero`: `‖x‖ ^ d = ‖a₀‖` for `x` with
  minimal polynomial of degree `d` and constant coefficient `a₀`.
* `TauCeti.NormedRing.PseudoUniformizer.isCommensurable_of_isAlgebraic`: commensurability passes
  from `K` to every multiplicative pseudo-uniformiser of `L`.

## References

* J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Chapter II, §§4, 6.
-/

public section

variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedField L] [NormedAlgebra K L] [Algebra.IsAlgebraic K L]

variable (K) in
/-- In an algebraic normed field extension `L` of a complete ultrametric field `K`, the norm of an
element `x` raised to the degree of its minimal polynomial is the norm of the constant coefficient
of that polynomial. -/
theorem NormedAlgebra.norm_pow_natDegree_minpoly_eq_norm_coeff_zero (x : L) :
    ‖x‖ ^ (minpoly K x).natDegree = ‖(minpoly K x).coeff 0‖ := by
  have hd : ((minpoly K x).natDegree : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral x)).ne'
  rw [NormedAlgebra.norm_eq_spectralNorm K, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
    ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hd, Real.rpow_one]

namespace TauCeti.NormedRing.PseudoUniformizer

/-- **Commensurability passes to algebraic extensions.** If the norm of a complete ultrametric
field `K` is commensurable with `ϖ`, then the norm of an algebraic normed field extension `L` of
`K` is commensurable with every multiplicative pseudo-uniformiser `ϖ'` of `L`. -/
theorem isCommensurable_of_isAlgebraic {ϖ : PseudoUniformizer K} (hϖ : ϖ.IsCommensurable)
    (ϖ' : PseudoUniformizer L) : ϖ'.IsCommensurable :=
  isCommensurable_of_forall_exists_norm_eq_pow hϖ ϖ' fun y _ ↦
    ⟨_, minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral y), _,
      (NormedAlgebra.norm_pow_natDegree_minpoly_eq_norm_coeff_zero K y).symm⟩

end TauCeti.NormedRing.PseudoUniformizer
