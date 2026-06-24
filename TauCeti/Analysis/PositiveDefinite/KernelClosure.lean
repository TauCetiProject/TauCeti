/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.Kernel

/-!
# Finite closure for positive-definite kernels

This file adds finite closure API for `TauCeti.IsPositiveDefiniteKernel`, the two-variable
positive-definite kernel predicate used in the positive-definite-function and Bochner part of the
`OneParameterSemigroups` roadmap.

The basic kernel file already proves the binary closure operations: sums, nonnegative real scalar
multiples, pointwise products, and rank-one kernels `(a, b) ↦ conj (g a) * g b`. This module
packages their finite consequences. These are the forms used by finite-rank kernel constructions
and by the finite-dimensional approximations that feed the later GNS/Kolmogorov decomposition:
finite sums of rank-one kernels are positive definite, and finite Schur products of
positive-definite kernels are positive definite.

No external formalization is vendored. The proofs are direct inductions through the existing
Tau Ceti binary kernel API, which itself uses Mathlib's positive-semidefinite matrix calculus.

## Main declarations

* `TauCeti.isPositiveDefiniteKernel_zero`, `TauCeti.isPositiveDefiniteKernel_one`, and
  `TauCeti.isPositiveDefiniteKernel_const_of_nonneg`: constant positive-definite kernels.
* `TauCeti.isPositiveDefiniteKernel_sum`: finite sums of positive-definite kernels.
* `TauCeti.isPositiveDefiniteKernel_prod`: finite pointwise products of positive-definite
  kernels.
* `TauCeti.isPositiveDefiniteKernel_sum_smul`: finite sums with nonnegative real weights.
* `TauCeti.isPositiveDefiniteKernel_pow`: Schur powers of a positive-definite kernel.
* `TauCeti.isPositiveDefiniteKernel_sum_conj_mul`: finite sums of rank-one kernels.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 3.
-/

public section

open scoped ComplexConjugate

namespace TauCeti

universe u v w

variable {𝕜 : Type u} [RCLike 𝕜]
variable {α : Type v}

/-- The zero kernel is positive definite. -/
theorem isPositiveDefiniteKernel_zero :
    IsPositiveDefiniteKernel (fun _ _ : α => (0 : 𝕜)) := by
  simpa using isPositiveDefiniteKernel_conj_mul (𝕜 := 𝕜) (α := α) (fun _ => (0 : 𝕜))

/-- The constant kernel with value `1` is positive definite. -/
theorem isPositiveDefiniteKernel_one :
    IsPositiveDefiniteKernel (fun _ _ : α => (1 : 𝕜)) := by
  simpa using isPositiveDefiniteKernel_conj_mul (𝕜 := 𝕜) (α := α) (fun _ => (1 : 𝕜))

/-- A nonnegative real constant, viewed in an `RCLike` field, gives a positive-definite
constant kernel. -/
theorem isPositiveDefiniteKernel_const_of_nonneg {r : ℝ} (hr : 0 ≤ r) :
    IsPositiveDefiniteKernel (fun _ _ : α => (r : 𝕜)) := by
  convert isPositiveDefiniteKernel_smul (𝕜 := 𝕜) (α := α)
    (K := fun _ _ : α => (1 : 𝕜)) hr isPositiveDefiniteKernel_one using 1
  ext a b
  exact @Algebra.algebraMap_eq_smul_one ℝ 𝕜 _ _ _ r

/-- Finite sums of positive-definite kernels are positive definite. -/
theorem isPositiveDefiniteKernel_sum {ι : Type w} {s : Finset ι}
    {K : ι → α → α → 𝕜} (hK : ∀ i ∈ s, IsPositiveDefiniteKernel (K i)) :
    IsPositiveDefiniteKernel (fun a b => ∑ i ∈ s, K i a b) := by
  have h := Finset.sum_induction K IsPositiveDefiniteKernel
    (fun _ _ => isPositiveDefiniteKernel_add) isPositiveDefiniteKernel_zero hK
  have heq : (∑ i ∈ s, K i) = fun a b => ∑ i ∈ s, K i a b := by
    ext a b
    simp
  rwa [heq] at h

/-- Finite pointwise products of positive-definite kernels are positive definite. -/
theorem isPositiveDefiniteKernel_prod {ι : Type w} {s : Finset ι}
    {K : ι → α → α → 𝕜} (hK : ∀ i ∈ s, IsPositiveDefiniteKernel (K i)) :
    IsPositiveDefiniteKernel (fun a b => ∏ i ∈ s, K i a b) := by
  have h := Finset.prod_induction K IsPositiveDefiniteKernel
    (fun _ _ => isPositiveDefiniteKernel_mul) isPositiveDefiniteKernel_one hK
  have heq : (∏ i ∈ s, K i) = fun a b => ∏ i ∈ s, K i a b := by
    ext a b
    simp
  rwa [heq] at h

/-- Finite sums of positive-definite kernels with nonnegative real weights are positive
definite. This is the weighted finite-mixture form most often used in examples. -/
theorem isPositiveDefiniteKernel_sum_smul {ι : Type w} {s : Finset ι}
    {r : ι → ℝ} {K : ι → α → α → 𝕜} (hr : ∀ i ∈ s, 0 ≤ r i)
    (hK : ∀ i ∈ s, IsPositiveDefiniteKernel (K i)) :
    IsPositiveDefiniteKernel (fun a b => ∑ i ∈ s, r i • K i a b) :=
  isPositiveDefiniteKernel_sum fun i hi =>
    isPositiveDefiniteKernel_smul (hr i hi) (hK i hi)

/-- Schur powers of a positive-definite kernel are positive definite. -/
theorem isPositiveDefiniteKernel_pow {K : α → α → 𝕜}
    (hK : IsPositiveDefiniteKernel K) (n : ℕ) :
    IsPositiveDefiniteKernel (fun a b => K a b ^ n) := by
  induction n with
  | zero =>
      simpa using isPositiveDefiniteKernel_one (𝕜 := 𝕜) (α := α)
  | succ n ih =>
      simpa [pow_succ] using isPositiveDefiniteKernel_mul ih hK

/-- Finite sums of rank-one kernels `(a, b) ↦ conj (gᵢ a) * gᵢ b` are positive definite.
These are the finite-rank positive-definite kernels used as the elementary building blocks for
the later GNS/Kolmogorov decomposition. -/
theorem isPositiveDefiniteKernel_sum_conj_mul {ι : Type w} (s : Finset ι)
    (g : ι → α → 𝕜) :
    IsPositiveDefiniteKernel
      (fun a b => ∑ i ∈ s, conj (g i a) * g i b) :=
  isPositiveDefiniteKernel_sum fun i _ => isPositiveDefiniteKernel_conj_mul (g i)

/-- Finite products of rank-one kernels are positive definite. This is the Schur-product
companion to `TauCeti.isPositiveDefiniteKernel_sum_conj_mul`. -/
theorem isPositiveDefiniteKernel_prod_conj_mul {ι : Type w} (s : Finset ι)
    (g : ι → α → 𝕜) :
    IsPositiveDefiniteKernel
      (fun a b => ∏ i ∈ s, conj (g i a) * g i b) :=
  isPositiveDefiniteKernel_prod fun i _ => isPositiveDefiniteKernel_conj_mul (g i)

/-- Finite nonnegative real combinations of rank-one kernels are positive definite. -/
theorem isPositiveDefiniteKernel_sum_smul_conj_mul {ι : Type w} {s : Finset ι}
    {r : ι → ℝ} (hr : ∀ i ∈ s, 0 ≤ r i) (g : ι → α → 𝕜) :
    IsPositiveDefiniteKernel
      (fun a b => ∑ i ∈ s, r i • (conj (g i a) * g i b)) :=
  isPositiveDefiniteKernel_sum_smul hr fun i _ => isPositiveDefiniteKernel_conj_mul (g i)

end TauCeti
