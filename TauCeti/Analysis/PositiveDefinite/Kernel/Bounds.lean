/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.PosSemidef

/-!
# Hermitian symmetry and bounds for subtraction kernels

This file records the reality of `ψ 0` and symmetry under negation for Hermitian subtraction
kernels `(a, b) ↦ ψ (a - b)`. For positive-semidefinite subtraction kernels, the scalar
Cauchy--Schwarz estimates from `TauCeti.Analysis.Matrix.PosSemidef` give nonnegativity of
`re (ψ 0)` and the uniform norm bound `‖ψ z‖ ≤ re (ψ 0)`. These properties supply the conjugate
symmetry and boundedness used in the Fourier analysis of positive-definite functions.

## Main declarations

* `Matrix.IsHermitian.map_neg_eq_star`: a function with Hermitian subtraction kernel satisfies
  `ψ (-v) = star (ψ v)`.
* `Matrix.IsHermitian.map_zero_eq_ofReal_re`: for an `RCLike`-valued function with Hermitian
  subtraction kernel, the value at `0` is real.
* `Matrix.PosSemidef.map_zero_re_nonneg` and `Matrix.PosSemidef.norm_apply_le_map_zero_re`:
  for an `RCLike`-valued function with positive-semidefinite subtraction kernel, the real part of
  its value at `0` is nonnegative and bounds the function uniformly in norm.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open ComplexConjugate
open scoped ComplexOrder

namespace Matrix

namespace IsHermitian

/-- A function with Hermitian subtraction kernel satisfies `ψ (-v) = star (ψ v)`. -/
theorem map_neg_eq_star {R V : Type*} [Star R] [SubNegZeroMonoid V] {ψ : V → R}
    (h : Matrix.IsHermitian fun a b : V => ψ (a - b)) (v : V) :
    ψ (-v) = star (ψ v) := by
  simpa only [sub_zero, zero_sub] using (h.apply 0 v).symm

variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*} {ψ : V → 𝕜}

/-- The value at `0` of an `RCLike`-valued function with Hermitian subtraction kernel is real. -/
theorem map_zero_eq_ofReal_re [SubNegZeroMonoid V]
    (h : Matrix.IsHermitian fun a b : V => ψ (a - b)) :
    ψ 0 = (RCLike.re (ψ 0) : 𝕜) := by
  have hzero : conj (ψ 0) = ψ 0 := by
    simpa only [neg_zero, starRingEnd_apply] using (h.map_neg_eq_star 0).symm
  exact (RCLike.conj_eq_iff_re.mp hzero).symm

end IsHermitian

namespace PosSemidef

variable {𝕜 : Type*} [RCLike 𝕜] {V : Type*} {ψ : V → 𝕜}

/-- The value at `0` of a function with positive-semidefinite subtraction kernel has nonnegative
real part. -/
theorem map_zero_re_nonneg [SubNegZeroMonoid V]
    (hpd : Matrix.PosSemidef fun a b : V => ψ (a - b)) :
    0 ≤ RCLike.re (ψ 0) := by
  have h : (0 : 𝕜) ≤ ψ 0 := by
    simpa only [sub_zero] using hpd.diag_nonneg (i := 0)
  exact (RCLike.nonneg_iff.mp h).1

/-- A function with positive-semidefinite subtraction kernel is uniformly bounded by the real part
of its value at `0`. -/
theorem norm_apply_le_map_zero_re [AddGroup V]
    (hpd : Matrix.PosSemidef fun a b : V => ψ (a - b)) (z : V) :
    ‖ψ z‖ ≤ RCLike.re (ψ 0) := by
  refine le_of_sq_le_sq ?_ hpd.map_zero_re_nonneg
  simpa only [sub_zero, sub_self, RCLike.normSq_eq_def', pow_two] using hpd.normSq_le z 0

end PosSemidef

end Matrix
