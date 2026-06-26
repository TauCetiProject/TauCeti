/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.Kernel

/-!
# The finitely supported Gram form of a positive-definite kernel

This file packages the finitely supported Hermitian form attached to a positive-definite kernel.
For a kernel `K : α → α → 𝕜` and finitely supported coefficient vectors `x y : α →₀ 𝕜`, the form is

`∑ a ∈ x.support, ∑ b ∈ y.support, conj (x a) * y b * K a b`.

The diagonal nonnegativity of this form is exactly the `Matrix.PosSemidef` content in
`TauCeti.IsPositiveDefiniteKernel`, but a named finitely supported form is the object needed by
the later GNS/Kolmogorov construction: its null space is quotiented, then completed.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C ("Positive-definite
functions and Bochner's theorem"), specifically the positive-definite-kernel / GNS-Kolmogorov API
prerequisite. No Mathlib code is vendored; the proofs reuse Mathlib's positive-semidefinite matrix
API through `TauCeti.IsPositiveDefiniteKernel`.

## Main declarations

* `TauCeti.positiveDefiniteKernelFinsuppForm`: the finitely supported Gram form attached to a
  kernel.
* `TauCeti.positiveDefiniteKernelFinsuppForm_self_nonneg`: nonnegativity on the diagonal for
  positive-definite kernels.
* `TauCeti.positiveDefiniteKernelFinsuppForm_conj_symm`: conjugate symmetry of the form.
* `TauCeti.positiveDefiniteKernelFinsuppForm_single_single`: the value on two basis vectors.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open ComplexConjugate
open scoped ComplexOrder

namespace TauCeti

universe u v

variable {𝕜 : Type u} [RCLike 𝕜] {α : Type v}

/-- The finitely supported Hermitian form associated to a kernel `K`.

For positive-definite `K`, the diagonal value
`positiveDefiniteKernelFinsuppForm K x x` is nonnegative. This is the pre-inner-product form used
before quotienting by its null space in the GNS/Kolmogorov construction. -/
noncomputable def positiveDefiniteKernelFinsuppForm (K : α → α → 𝕜)
    (x y : α →₀ 𝕜) : 𝕜 :=
  x.sum fun a xa => y.sum fun b yb => conj xa * yb * K a b

variable {K : α → α → 𝕜}

/-- The finitely supported Gram form is zero when the left vector is zero. -/
@[simp]
theorem positiveDefiniteKernelFinsuppForm_zero_left (y : α →₀ 𝕜) :
    positiveDefiniteKernelFinsuppForm K 0 y = 0 := by
  simp [positiveDefiniteKernelFinsuppForm]

/-- The finitely supported Gram form is zero when the right vector is zero. -/
@[simp]
theorem positiveDefiniteKernelFinsuppForm_zero_right (x : α →₀ 𝕜) :
    positiveDefiniteKernelFinsuppForm K x 0 = 0 := by
  simp [positiveDefiniteKernelFinsuppForm]

/-- The diagonal finitely supported Gram form of a positive-definite kernel is nonnegative. -/
theorem positiveDefiniteKernelFinsuppForm_self_nonneg
    (hK : IsPositiveDefiniteKernel K) (x : α →₀ 𝕜) :
    0 ≤ positiveDefiniteKernelFinsuppForm K x x := by
  have hK' := (isPositiveDefiniteKernel_def K).mp hK
  simpa [positiveDefiniteKernelFinsuppForm, Finsupp.sum, dotProduct, Matrix.mulVec,
    Matrix.of_apply, Pi.star_apply, RCLike.star_def, Finset.mul_sum, mul_assoc, mul_left_comm,
    mul_comm] using hK'.2 x

/-- The finitely supported Gram form attached to a positive-definite kernel is conjugate
symmetric. -/
theorem positiveDefiniteKernelFinsuppForm_conj_symm
    (hK : IsPositiveDefiniteKernel K) (x y : α →₀ 𝕜) :
    conj (positiveDefiniteKernelFinsuppForm K x y)
      = positiveDefiniteKernelFinsuppForm K y x := by
  classical
  rw [positiveDefiniteKernelFinsuppForm, positiveDefiniteKernelFinsuppForm]
  simp_rw [Finsupp.sum, map_sum, map_mul, RCLike.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [isPositiveDefiniteKernel_conj_symm hK a b]
  ring

/-- The finitely supported Gram form takes the expected value on two basis vectors. -/
@[simp]
theorem positiveDefiniteKernelFinsuppForm_single_single (a b : α) (r s : 𝕜) :
    positiveDefiniteKernelFinsuppForm K (Finsupp.single a r) (Finsupp.single b s)
      = conj r * s * K a b := by
  classical
  simp [positiveDefiniteKernelFinsuppForm]

/-- On a single finitely supported basis vector, the diagonal Gram form is the scalar norm-square
times the corresponding diagonal kernel value. -/
theorem positiveDefiniteKernelFinsuppForm_single_self (a : α) (r : 𝕜) :
    positiveDefiniteKernelFinsuppForm K (Finsupp.single a r) (Finsupp.single a r)
      = RCLike.normSq r * K a a := by
  classical
  rw [positiveDefiniteKernelFinsuppForm_single_single, RCLike.conj_mul,
    show ((‖r‖ : 𝕜) ^ 2) = (RCLike.normSq r : 𝕜) by
      rw [← map_pow, RCLike.normSq_eq_def']]

end TauCeti
