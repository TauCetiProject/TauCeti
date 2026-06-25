/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.PositiveDefinite.Basic
public import Mathlib.Data.NNReal.Basic

/-!
# Positive-definite functions on `[0, ∞) × V`

This file records the Berg--Christensen--Ressel semigroup-group positive-definiteness predicate
for functions on `ℝ≥0 × V`. For an additive group `V`, the intended involution is
`(t, v) ↦ (t, -v)`, so the finite quadratic forms use the entries
`F (tᵢ + tⱼ, vᵢ - vⱼ)`.

The generic predicate `TauCeti.IsPositiveDefinite` already handles involutive additive monoids.
Here we spell out the BCR specialization directly, rather than installing a global negation
`StarAddMonoid` instance on every additive group `V`, which would conflict with Mathlib's ordinary
star conventions. The result is the named hypothesis needed for the BCR Laplace--Fourier
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
  ∀ (n : ℕ) (c : Fin n → ℂ) (p : Fin n → ℝ≥0 × V),
    0 ≤ ∑ i, ∑ j, c i * conj (c j) * F ((p i).1 + (p j).1, (p i).2 - (p j).2)

namespace IsSemigroupGroupPD

/-- Semigroup-group positive-definiteness over an arbitrary finite index type. -/
theorem sum_nonneg (hF : IsSemigroupGroupPD F) {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (p : ι → ℝ≥0 × V) :
    0 ≤ ∑ i, ∑ j, c i * conj (c j) * F ((p i).1 + (p j).1, (p i).2 - (p j).2) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have h := hF (Fintype.card ι) (fun i => c (e i)) (fun i => p (e i))
  refine le_of_le_of_eq h ?_
  exact Fintype.sum_equiv e _ _ fun i =>
    Fintype.sum_equiv e _ _ fun j => rfl

/-- The value of a semigroup-group positive-definite function at the identity is nonnegative. -/
theorem map_zero_nonneg (hF : IsSemigroupGroupPD F) : 0 ≤ F (0, 0) := by
  have h := hF 1 ![1] ![(0, 0)]
  simpa [Fin.sum_univ_one] using h

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
  have h := hF 2 ![c₀, c₁] ![p, q]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact le_of_le_of_eq h (by ring)

/-- A semigroup-group positive-definite function is conjugate symmetric for the
BCR involution: `conj (F (s + t, w - v)) = F (t + s, v - w)`. -/
@[simp]
theorem conj_symm (hF : IsSemigroupGroupPD F) (p q : ℝ≥0 × V) :
    conj (F (q.1 + p.1, q.2 - p.2)) = F (p.1 + q.1, p.2 - q.2) := by
  have hp : (F (p.1 + p.1, p.2 - p.2)).im = 0 := by
    have h := hF.quadForm_two_nonneg p p 1 0
    simpa using (Complex.nonneg_iff.mp h).2.symm
  have hq : (F (q.1 + q.1, q.2 - q.2)).im = 0 := by
    have h := hF.quadForm_two_nonneg q q 1 0
    simpa using (Complex.nonneg_iff.mp h).2.symm
  have hp0 : (F (p.1 + p.1, 0)).im = 0 := by simpa [sub_self] using hp
  have hq0 : (F (q.1 + q.1, 0)).im = 0 := by simpa [sub_self] using hq
  have him :
      (F (q.1 + p.1, q.2 - p.2)).im + (F (p.1 + q.1, p.2 - q.2)).im = 0 := by
    have h := (Complex.nonneg_iff.mp (hF.quadForm_two_nonneg p q 1 1)).2
    simp [Complex.add_im, hp0, hq0] at h
    linarith
  have hre :
      (F (q.1 + p.1, q.2 - p.2)).re = (F (p.1 + q.1, p.2 - q.2)).re := by
    have h := (Complex.nonneg_iff.mp (hF.quadForm_two_nonneg p q 1 Complex.I)).2
    simp [Complex.add_im, Complex.mul_im, hp0, hq0] at h
    linarith
  apply Complex.ext
  · rw [Complex.conj_re]
    exact hre
  · rw [Complex.conj_im]
    linarith

/-- Semigroup-group positive-definite functions are closed under addition. -/
theorem add (hF : IsSemigroupGroupPD F) (hG : IsSemigroupGroupPD G) :
    IsSemigroupGroupPD (fun x => F x + G x) := by
  intro n c p
  have hsplit :
      ∑ i, ∑ j, c i * conj (c j) *
          (F ((p i).1 + (p j).1, (p i).2 - (p j).2) +
            G ((p i).1 + (p j).1, (p i).2 - (p j).2))
        = (∑ i, ∑ j, c i * conj (c j) *
            F ((p i).1 + (p j).1, (p i).2 - (p j).2))
          + ∑ i, ∑ j, c i * conj (c j) *
            G ((p i).1 + (p j).1, (p i).2 - (p j).2) := by
    simp only [mul_add, Finset.sum_add_distrib]
  simpa only [hsplit] using add_nonneg (hF n c p) (hG n c p)

/-- Semigroup-group positive-definite functions are closed under multiplication by a nonnegative
complex scalar. -/
theorem const_mul {k : ℂ} (hk : 0 ≤ k) (hF : IsSemigroupGroupPD F) :
    IsSemigroupGroupPD (fun x => k * F x) := by
  intro n c p
  have hpull :
      ∑ i, ∑ j, c i * conj (c j) *
          (k * F ((p i).1 + (p j).1, (p i).2 - (p j).2))
        = k * ∑ i, ∑ j, c i * conj (c j) *
          F ((p i).1 + (p j).1, (p i).2 - (p j).2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hpull]
  exact mul_nonneg hk (hF n c p)

/-- Semigroup-group positive-definite functions are closed under finite sums. -/
theorem sum {ι : Type*} {s : Finset ι} {H : ι → ℝ≥0 × V → ℂ}
    (hH : ∀ i ∈ s, IsSemigroupGroupPD (H i)) :
    IsSemigroupGroupPD (fun x => ∑ i ∈ s, H i x) := by
  classical
  have heq : (∑ i ∈ s, H i) = fun x => ∑ i ∈ s, H i x :=
    funext fun x => Finset.sum_apply x s H
  rw [← heq]
  exact Finset.sum_induction H IsSemigroupGroupPD (fun _ _ => add)
      (by
        intro n c p
        simp)
      hH

end IsSemigroupGroupPD

end TauCeti
