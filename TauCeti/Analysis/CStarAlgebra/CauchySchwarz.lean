/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Module.Constructions

/-!
# Cauchy–Schwarz bounds for finite sums in a C⋆-algebra

For elements `aₖ, bₖ` of a non-unital C⋆-algebra `D` indexed by a finite set, this file proves

`‖∑ aₖ bₖ‖² ≤ ‖∑ aₖ aₖ⋆‖ ‖∑ bₖ⋆ bₖ‖`,

and its consequence `‖∑ aₖ x bₖ‖² ≤ ‖∑ aₖ aₖ⋆‖ ‖x‖² ‖∑ bₖ⋆ bₖ‖`. The sum `∑ aₖ bₖ` is the inner
product of the columns `(bₖ⋆)` and `(aₖ)` of the Hilbert `D`-module `C⋆ᵐᵒᵈ(D, ι → D)`, so the
bound is the Cauchy–Schwarz inequality of that module. The three-factor bound follows by applying
the two-factor bound to `aₖ x` in place of `aₖ`. When `D` is unital, setting `x = 1` in the
three-factor bound recovers the two-factor one; since `D` need not be unital, the two-factor bound
is proved first.

## Main declarations

* `Finset.norm_sum_mul_sq_le`: `‖∑ aₖ bₖ‖² ≤ ‖∑ aₖ aₖ⋆‖ ‖∑ bₖ⋆ bₖ‖`.
* `Finset.norm_sum_mul_mul_sq_le`: `‖∑ aₖ x bₖ‖² ≤ ‖∑ aₖ aₖ⋆‖ ‖x‖² ‖∑ bₖ⋆ bₖ‖`.
* `Finset.norm_sum_star_mul_mul_le`: `‖∑ aₖ⋆ b aₖ‖ ≤ ‖b‖ ‖∑ aₖ⋆ aₖ‖`.
* `Finset.norm_sum_mul_mul_star_le`: `‖∑ aₖ b aₖ⋆‖ ≤ ‖b‖ ‖∑ aₖ aₖ⋆‖`.
* `Finset.norm_sum_mul_sum_mul_le_sq`: `‖∑ i, xᵢ (∑ j, xⱼ²) xᵢ‖ ≤ ‖∑ i, xᵢ²‖²`
  for self-adjoint `xᵢ`.
* `Finset.norm_sum_alternating_four_le`: `‖∑ i, ∑ j, xᵢ xⱼ xᵢ xⱼ‖ ≤ ‖∑ i, xᵢ²‖²`
  for self-adjoint `xᵢ`.

## References

* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Proposition 1.1.
-/

public section

open scoped InnerProductSpace WithCStarModule ComplexOrder

namespace Finset

variable {D ι : Type*} [NonUnitalCStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

/-- The bound `‖∑ aₖ bₖ‖² ≤ ‖∑ aₖ aₖ⋆‖ ‖∑ bₖ⋆ bₖ‖` for sums over a finite type. -/
private theorem norm_sum_mul_sq_le_of_fintype [Fintype ι] (a b : ι → D) :
    ‖∑ k, a k * b k‖ ^ 2 ≤ ‖∑ k, a k * star (a k)‖ * ‖∑ k, star (b k) * b k‖ := by
  let u : C⋆ᵐᵒᵈ(D, ι → D) := (WithCStarModule.equiv D (ι → D)).symm fun k => star (b k)
  let v : C⋆ᵐᵒᵈ(D, ι → D) := (WithCStarModule.equiv D (ι → D)).symm a
  have huv : ⟪u, v⟫_D = ∑ k, a k * b k := by
    simp [u, v, WithCStarModule.pi_inner, WithCStarModule.inner_def]
  have hu : ‖u‖ ^ 2 = ‖∑ k, star (b k) * b k‖ := by
    simp [u, WithCStarModule.pi_norm_sq, WithCStarModule.inner_def]
  have hv : ‖v‖ ^ 2 = ‖∑ k, a k * star (a k)‖ := by
    simp [v, WithCStarModule.pi_norm_sq, WithCStarModule.inner_def]
  rw [← huv, ← hu, ← hv, ← mul_pow, mul_comm]
  gcongr
  exact CStarModule.norm_inner_le (C⋆ᵐᵒᵈ(D, ι → D))

/-- The Cauchy–Schwarz bound `‖∑ aₖ bₖ‖² ≤ ‖∑ aₖ aₖ⋆‖ ‖∑ bₖ⋆ bₖ‖` for finite sums in a
C⋆-algebra. -/
theorem norm_sum_mul_sq_le (s : Finset ι) (a b : ι → D) :
    ‖∑ k ∈ s, a k * b k‖ ^ 2 ≤ ‖∑ k ∈ s, a k * star (a k)‖ * ‖∑ k ∈ s, star (b k) * b k‖ := by
  have := norm_sum_mul_sq_le_of_fintype (fun k : s => a k) (fun k : s => b k)
  rwa [s.sum_coe_sort (fun k => a k * b k), s.sum_coe_sort (fun k => a k * star (a k)),
    s.sum_coe_sort (fun k => star (b k) * b k)] at this

/-- The Cauchy–Schwarz bound `‖∑ aₖ x bₖ‖² ≤ ‖∑ aₖ aₖ⋆‖ ‖x‖² ‖∑ bₖ⋆ bₖ‖` for finite sums in a
C⋆-algebra. -/
theorem norm_sum_mul_mul_sq_le (s : Finset ι) (a b : ι → D) (x : D) :
    ‖∑ k ∈ s, a k * x * b k‖ ^ 2 ≤
      ‖∑ k ∈ s, a k * star (a k)‖ * ‖x‖ ^ 2 * ‖∑ k ∈ s, star (b k) * b k‖ := by
  have hle : ∑ k ∈ s, a k * x * star (a k * x) ≤ ‖x * star x‖ • ∑ k ∈ s, a k * star (a k) := by
    rw [Finset.smul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    simpa [mul_assoc] using CStarAlgebra.star_right_conjugate_le_norm_smul (a k) (x * star x)
  have h0 : 0 ≤ ∑ k ∈ s, a k * x * star (a k * x) :=
    Finset.sum_nonneg fun k _ => mul_star_self_nonneg _
  have hax : ‖∑ k ∈ s, a k * x * star (a k * x)‖ ≤ ‖∑ k ∈ s, a k * star (a k)‖ * ‖x‖ ^ 2 := by
    refine (CStarAlgebra.norm_le_norm_of_le_of_nonneg hle h0).trans_eq ?_
    rw [norm_smul, norm_norm, CStarRing.norm_self_mul_star, sq, mul_comm]
  refine (norm_sum_mul_sq_le s (fun k => a k * x) b).trans ?_
  gcongr

/-- Conjugating an element `b` by a finite family `a` satisfies
`‖∑ k ∈ s, star (a k) * b * a k‖ ≤ ‖b‖ * ‖∑ k ∈ s, star (a k) * a k‖`. -/
theorem norm_sum_star_mul_mul_le (s : Finset ι) (a : ι → D) (b : D) :
    ‖∑ k ∈ s, star (a k) * b * a k‖ ≤ ‖b‖ * ‖∑ k ∈ s, star (a k) * a k‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)), mul_pow]
  have h := norm_sum_mul_mul_sq_le s (fun k => star (a k)) a b
  simp only [star_star] at h
  exact h.trans_eq (by ring)

/-- Right-starred conjugation of `b` by a finite family `a` satisfies
`‖∑ k ∈ s, a k * b * star (a k)‖ ≤ ‖b‖ * ‖∑ k ∈ s, a k * star (a k)‖`. -/
theorem norm_sum_mul_mul_star_le (s : Finset ι) (a : ι → D) (b : D) :
    ‖∑ k ∈ s, a k * b * star (a k)‖ ≤ ‖b‖ * ‖∑ k ∈ s, a k * star (a k)‖ := by
  simpa only [star_star] using norm_sum_star_mul_mul_le s (fun k => star (a k)) b

/-- Conjugating `∑ j ∈ s, x j * x j` by a self-adjoint family `x` satisfies
`‖∑ i ∈ s, x i * (∑ j ∈ s, x j * x j) * x i‖ ≤ ‖∑ i ∈ s, x i * x i‖ ^ 2`. -/
theorem norm_sum_mul_sum_mul_le_sq (s : Finset ι) {x : ι → D}
    (hx : ∀ i ∈ s, IsSelfAdjoint (x i)) :
    ‖∑ i ∈ s, x i * (∑ j ∈ s, x j * x j) * x i‖ ≤ ‖∑ i ∈ s, x i * x i‖ ^ 2 := by
  have h := norm_sum_star_mul_mul_le s x (∑ j ∈ s, x j * x j)
  have hsum : ∑ i ∈ s, star (x i) * x i = ∑ i ∈ s, x i * x i :=
    Finset.sum_congr rfl fun i hi => by rw [(hx i hi).star_eq]
  have hconj : ∑ i ∈ s, star (x i) * (∑ j ∈ s, x j * x j) * x i =
      ∑ i ∈ s, x i * (∑ j ∈ s, x j * x j) * x i :=
    Finset.sum_congr rfl fun i hi => by rw [(hx i hi).star_eq]
  rwa [hconj, hsum, ← sq] at h

/-- Alternating four-factor Cauchy–Schwarz bound for self-adjoint elements:
`‖∑ i ∈ s, ∑ j ∈ s, x i * x j * x i * x j‖ ≤ ‖∑ i ∈ s, x i * x i‖ ^ 2`. -/
theorem norm_sum_alternating_four_le (s : Finset ι) {x : ι → D}
    (hx : ∀ i ∈ s, IsSelfAdjoint (x i)) :
    ‖∑ i ∈ s, ∑ j ∈ s, x i * x j * x i * x j‖ ≤ ‖∑ i ∈ s, x i * x i‖ ^ 2 := by
  rw [← sq_le_sq₀ (norm_nonneg _) (sq_nonneg _)]
  let a : ι × ι → D := fun p => x p.1 * x p.2
  have hprod : ∑ i ∈ s, ∑ j ∈ s, x i * x j * x i * x j = ∑ p ∈ s ×ˢ s, a p * a p := by
    rw [Finset.sum_product]
    simp only [a, mul_assoc]
  have hrow_eq : ∑ p ∈ s ×ˢ s, a p * star (a p) =
      ∑ i ∈ s, x i * (∑ j ∈ s, x j * x j) * x i := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [a, star_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc, (hx i hi).star_eq]
    exact Finset.sum_congr rfl fun j hj => by rw [(hx j hj).star_eq]
  have hcol_eq : ∑ p ∈ s ×ˢ s, star (a p) * a p =
      ∑ j ∈ s, x j * (∑ i ∈ s, x i * x i) * x j := by
    rw [Finset.sum_product_right]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [a, star_mul, Finset.mul_sum, Finset.sum_mul, mul_assoc, (hx j hj).star_eq]
    exact Finset.sum_congr rfl fun i hi => by rw [(hx i hi).star_eq]
  have hrow : ‖∑ p ∈ s ×ˢ s, a p * star (a p)‖ ≤ ‖∑ i ∈ s, x i * x i‖ ^ 2 :=
    hrow_eq ▸ norm_sum_mul_sum_mul_le_sq s hx
  have hcol : ‖∑ p ∈ s ×ˢ s, star (a p) * a p‖ ≤ ‖∑ i ∈ s, x i * x i‖ ^ 2 :=
    hcol_eq ▸ norm_sum_mul_sum_mul_le_sq s hx
  rw [hprod]
  exact (norm_sum_mul_sq_le (s ×ˢ s) a a).trans <|
    (mul_le_mul hrow hcol (norm_nonneg _) (sq_nonneg _)).trans_eq (by ring)

end Finset
