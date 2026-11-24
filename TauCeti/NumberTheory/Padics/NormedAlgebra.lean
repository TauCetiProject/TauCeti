/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic

/-!
# Norms in finite extensions of `ℚ_[p]`

Let `K` be a normed field extension of `ℚ_[p]` of finite degree `n`. The norm of `K` is the
spectral norm, so an element `x` whose minimal polynomial has degree `d` and constant coefficient
`a₀` satisfies `‖x‖ ^ d = ‖a₀‖`. Since `d` divides `n` and `‖a₀‖` is an integer power of `p`, the
`n`-th power of the norm of every nonzero element of `K` is an integer power of `p`.

## Main results

* `TauCeti.exists_norm_pow_finrank_eq_zpow`: in an extension of `ℚ_[p]` of degree `n`, the `n`-th
  powers of the nonzero norms lie in `p ^ ℤ`.

## References

* J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer, 1999, Chapter II, §4.
-/

public section

namespace TauCeti

/-- **Norms in a finite extension of `ℚ_[p]`.** If `K` is a normed field extension of `ℚ_[p]` of
finite degree `n`, then the `n`-th power of the norm of every nonzero element of `K` is an integer
power of `p`. -/
theorem exists_norm_pow_finrank_eq_zpow {p : ℕ} [Fact p.Prime] {K : Type*} [NormedField K]
    [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K] {x : K} (hx : x ≠ 0) :
    ∃ m : ℤ, ‖x‖ ^ Module.finrank ℚ_[p] K = (p : ℝ) ^ m := by
  have hint : IsIntegral ℚ_[p] x := .of_finite ℚ_[p] x
  obtain ⟨k, hk⟩ := minpoly.degree_dvd hint
  refine ⟨-((minpoly ℚ_[p] x).coeff 0).valuation * k, ?_⟩
  rw [hk, pow_mul,
    NormedAlgebra.norm_pow_natDegree_minpoly_eq_norm_coeff_zero ℚ_[p] hint.isAlgebraic,
    Padic.norm_eq_zpow_neg_valuation (minpoly.coeff_zero_ne_zero hint hx), zpow_mul,
    zpow_natCast]

end TauCeti
