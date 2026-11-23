/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.PosSemidef.Basic

/-!
# Hermitian symmetry and bounds for subtraction and group kernels

This file records the reality of `ψ 0` and symmetry under negation for Hermitian subtraction
kernels `(a, b) ↦ ψ (a - b)`, together with norm and real-part bounds for positive-semidefinite
kernels. For subtraction kernels, the scalar Cauchy--Schwarz estimates from
`TauCeti.Analysis.Matrix.PosSemidef.Basic` give nonnegativity of `re (ψ 0)` and the uniform norm
bound `‖ψ z‖ ≤ re (ψ 0)`. For normalized (`φ 1 = 1`) positive-definite functions on a group, with
kernel `(g, h) ↦ φ (g⁻¹ * h)`, they yield `‖φ g‖ ≤ 1`, `0 ≤ 1 - re (φ g)`, and
`‖φ g - 1‖ ^ 2 ≤ 2 * (1 - re (φ g))`.

## Main declarations

* `Matrix.IsHermitian.map_neg_eq_star`: a function with Hermitian subtraction kernel satisfies
  `ψ (-v) = star (ψ v)`.
* `Matrix.IsHermitian.map_zero_eq_ofReal_re`: for an `RCLike`-valued function with Hermitian
  subtraction kernel, the value at `0` is real.
* `Matrix.PosSemidef.map_zero_re_nonneg` and `Matrix.PosSemidef.norm_apply_le_map_zero_re`:
  for an `RCLike`-valued function with positive-semidefinite subtraction kernel, the real part of
  its value at `0` is nonnegative and bounds the function uniformly in norm.
* `Matrix.PosSemidef.norm_apply_le_one`, `Matrix.PosSemidef.one_sub_re_nonneg`, and
  `Matrix.PosSemidef.norm_sub_one_sq_le`: norm and real-part bounds for normalized
  positive-definite functions on a group.

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

variable {G : Type*} [Group G]

/-- A normalized positive-definite function on a group is bounded by `1` in norm. -/
theorem norm_apply_le_one {φ : G → 𝕜} (hφ : (of fun g h : G ↦ φ (g⁻¹ * h)).PosSemidef)
    (h1 : φ 1 = 1) (g : G) : ‖φ g‖ ≤ 1 := by
  simpa using hφ.norm_le_one_of_apply_self_eq_one (a := 1) (b := g) (by simp [h1]) (by simp [h1])

/-- For a normalized positive-definite function `φ` on a group, `0 ≤ 1 - re (φ g)`. -/
theorem one_sub_re_nonneg {φ : G → 𝕜} (hφ : (of fun g h : G ↦ φ (g⁻¹ * h)).PosSemidef)
    (h1 : φ 1 = 1) (g : G) : 0 ≤ 1 - RCLike.re (φ g) := by
  linarith [RCLike.re_le_norm (φ g), hφ.norm_apply_le_one h1 g]

/-- For a normalized positive-definite function `φ` on a group,
`‖φ g - 1‖ ^ 2 ≤ 2 * (1 - re (φ g))`. -/
theorem norm_sub_one_sq_le {φ : G → 𝕜} (hφ : (of fun g h : G ↦ φ (g⁻¹ * h)).PosSemidef)
    (h1 : φ 1 = 1) (g : G) : ‖φ g - 1‖ ^ 2 ≤ 2 * (1 - RCLike.re (φ g)) := by
  have hsq : RCLike.normSq (φ g) ≤ 1 := by
    simpa [RCLike.normSq_eq_def'] using
      pow_le_pow_left₀ (norm_nonneg _) (hφ.norm_apply_le_one h1 g) 2
  rw [← RCLike.normSq_eq_def', RCLike.normSq_sub (φ g) 1, RCLike.normSq_one]
  simp only [map_one, mul_one]
  linarith

end PosSemidef

end Matrix
