/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.KernelClosure
public import Mathlib.Data.NNReal.Basic

/-!
# Positive-definite functions on `[0, ∞) × V`

This file records the Berg--Christensen--Ressel semigroup-group positive-definiteness predicate
for functions on `ℝ≥0 × V`. For an additive group `V`, the intended involution is
`(t, v) ↦ (t, -v)`, so the finite quadratic forms use the entries
`F (tᵢ + tⱼ, vᵢ - vⱼ)`.

The generic positive-definite-kernel predicate already captures the finite Gram-matrix condition.
Here we name its BCR specialization for the kernel
`K p q = F (p.1 + q.1, p.2 - q.2)`, rather than installing a global negation `StarAddMonoid`
instance on every additive group `V`, which would conflict with Mathlib's ordinary star
conventions. The result is the named hypothesis needed for the BCR Laplace--Fourier
representation target in the `OneParameterSemigroups` roadmap.

This advances `TauCetiRoadmap/OneParameterSemigroups/README.md`, Part C, Objects: the roadmap asks
for `IsSemigroupGroupPD` as the positive-definite predicate on `ℝ≥0 × V` with involution
`(t, a)⋆ = (t, -a)`.

## Main declarations

* `TauCeti.IsSemigroupGroupPD`: the BCR positive-definiteness predicate on `ℝ≥0 × V`.
* `TauCeti.IsSemigroupGroupPD.sum_nonneg`: the defining inequality over any finite index type.
* `TauCeti.IsSemigroupGroupPD.map_zero_nonneg`: the value at `(0, 0)` is nonnegative.
* `TauCeti.IsSemigroupGroupPD.conj_symm`: conjugate symmetry for the BCR involution.
* `TauCeti.IsSemigroupGroupPD.add`, `TauCeti.IsSemigroupGroupPD.const_mul`, and
  `TauCeti.IsSemigroupGroupPD.sum`: closure under the basic finite linear operations needed by
  the later semigroup representation theory.

## References

* C. Berg, J. P. R. Christensen, P. Ressel, *Harmonic Analysis on Semigroups* (GTM 100, 1984),
  Chapter 4.
-/

public section

open ComplexConjugate
open scoped ComplexOrder
open scoped NNReal

namespace TauCeti

variable {V : Type*} [AddCommGroup V] {F G : ℝ≥0 × V → ℂ}

/-- A function on `ℝ≥0 × V` is semigroup-group positive definite, in the
Berg--Christensen--Ressel sense, if all finite quadratic forms formed using the involution
`(t, v) ↦ (t, -v)` are nonnegative:
`∑ᵢⱼ cᵢ conj(cⱼ) F(tᵢ + tⱼ, vᵢ - vⱼ) ≥ 0`. -/
@[expose] def IsSemigroupGroupPD (F : ℝ≥0 × V → ℂ) : Prop :=
  IsPositiveDefiniteKernel fun p q : ℝ≥0 × V => F (p.1 + q.1, p.2 - q.2)

namespace IsSemigroupGroupPD

/-- Semigroup-group positive-definiteness over an arbitrary finite index type. -/
theorem sum_nonneg (hF : IsSemigroupGroupPD F) {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (p : ι → ℝ≥0 × V) :
    0 ≤ ∑ i, ∑ j, c i * conj (c j) * F ((p i).1 + (p j).1, (p i).2 - (p j).2) := by
  classical
  have hpos := (isPositiveDefiniteKernel_iff.mp hF).2 p (fun i => conj (c i))
  simpa only [Complex.conj_conj] using hpos

/-- The value of a semigroup-group positive-definite function at the identity is nonnegative. -/
theorem map_zero_nonneg (hF : IsSemigroupGroupPD F) : 0 ≤ F (0, 0) := by
  simpa using isPositiveDefiniteKernel_apply_self_nonneg hF ((0, 0) : ℝ≥0 × V)

/-- The value at the identity of a semigroup-group positive-definite function has zero imaginary
part. -/
@[simp]
theorem map_zero_im (hF : IsSemigroupGroupPD F) : (F (0, 0)).im = 0 :=
  ((Complex.nonneg_iff.mp hF.map_zero_nonneg).2).symm

/-- The real part of the value at the identity of a semigroup-group positive-definite function is
nonnegative. -/
theorem map_zero_re_nonneg (hF : IsSemigroupGroupPD F) : 0 ≤ (F (0, 0)).re :=
  (Complex.nonneg_iff.mp hF.map_zero_nonneg).1

/-- The `2 × 2` BCR Hermitian sub-form at two points. -/
theorem quadForm_two_nonneg (hF : IsSemigroupGroupPD F) (p q : ℝ≥0 × V) (c₀ c₁ : ℂ) :
    0 ≤ c₀ * conj c₀ * F (p.1 + p.1, p.2 - p.2)
      + c₀ * conj c₁ * F (p.1 + q.1, p.2 - q.2)
      + c₁ * conj c₀ * F (q.1 + p.1, q.2 - p.2)
      + c₁ * conj c₁ * F (q.1 + q.1, q.2 - q.2) := by
  have h := hF.sum_nonneg ![c₀, c₁] ![p, q]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact le_of_le_of_eq h (by ring)

/-- A semigroup-group positive-definite function is conjugate symmetric for the
BCR involution: `conj (F (s + t, w - v)) = F (t + s, v - w)`. -/
@[simp]
theorem conj_symm (hF : IsSemigroupGroupPD F) (p q : ℝ≥0 × V) :
    conj (F (q.1 + p.1, q.2 - p.2)) = F (p.1 + q.1, p.2 - q.2) := by
  simpa using isPositiveDefiniteKernel_conj_symm hF q p

/-- Semigroup-group positive-definite functions are closed under addition. -/
theorem add (hF : IsSemigroupGroupPD F) (hG : IsSemigroupGroupPD G) :
    IsSemigroupGroupPD (fun x => F x + G x) := by
  exact isPositiveDefiniteKernel_add hF hG

/-- Semigroup-group positive-definite functions are closed under multiplication by a nonnegative
complex scalar. -/
theorem const_mul {k : ℂ} (hk : 0 ≤ k) (hF : IsSemigroupGroupPD F) :
    IsSemigroupGroupPD (fun x => k * F x) := by
  change IsPositiveDefiniteKernel fun p q : ℝ≥0 × V =>
    k * F (p.1 + q.1, p.2 - q.2)
  simpa [Algebra.smul_def] using
    isPositiveDefiniteKernel_smul_of_nonneg (α := ℝ≥0 × V) (K := fun p q : ℝ≥0 × V =>
      F (p.1 + q.1, p.2 - q.2)) hk hF

/-- Semigroup-group positive-definite functions are closed under finite sums. -/
theorem sum {ι : Type*} {s : Finset ι} {H : ι → ℝ≥0 × V → ℂ}
    (hH : ∀ i ∈ s, IsSemigroupGroupPD (H i)) :
    IsSemigroupGroupPD (fun x => ∑ i ∈ s, H i x) := by
  classical
  change IsPositiveDefiniteKernel fun p q : ℝ≥0 × V =>
    ∑ i ∈ s, H i (p.1 + q.1, p.2 - q.2)
  simpa using isPositiveDefiniteKernel_sum (α := ℝ≥0 × V)
    (K := fun (i : ι) (p q : ℝ≥0 × V) => H i (p.1 + q.1, p.2 - q.2)) hH

end IsSemigroupGroupPD

end TauCeti
