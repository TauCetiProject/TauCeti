/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# The row–column inequality in a C⋆-algebra

A finite family `(u i)` in a C⋆-algebra `A` is a row `[u₁ ⋯ uₙ]` and a family `(v i)` is a column;
their product is `∑ᵢ uᵢ vᵢ`, and the norms of the row and of the column are
`‖∑ᵢ uᵢ uᵢ*‖^(1/2)` and `‖∑ᵢ vᵢ* vᵢ‖^(1/2)`. The norm of the product is at most the product of
these norms. This is the Cauchy–Schwarz inequality `‖⟪x, y⟫‖ ≤ ‖x‖ ‖y‖` of the Hilbert
`A`-module `Aⁿ` (Mathlib's `C⋆ᵐᵒᵈ(A, ι → A)`), whose inner product is `⟪x, y⟫ = ∑ᵢ yᵢ xᵢ*`.

For a self-adjoint family `(x i)` with square sum `T = ∑ₖ xₖ²`, the file also bounds the two
quartic sums `∑ᵢ xᵢ T xᵢ` and `∑ᵢ ∑ⱼ xᵢ xⱼ xᵢ xⱼ` by `‖T‖²`
(`TauCeti.norm_sum_mul_sum_mul_self_mul_le`, `TauCeti.norm_sum_sum_mul_mul_mul_le`). The first
follows from `0 ≤ xᵢ T xᵢ ≤ ‖T‖ xᵢ²`, the second from the row–column inequality for the products
`xᵢ xⱼ`. These are the pairing terms of the fourth moment of a Rademacher sum.

## References

* G. Pisier, *Grothendieck's theorem, past and present*, Bull. Amer. Math. Soc. 49 (2012),
  237–323, §9 (the row–column estimate in the proof of Lemma 9.2).
-/

public section

open CStarModule

namespace TauCeti

variable {ι A : Type*} [Fintype ι] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **The row–column inequality.** In a C⋆-algebra,
`‖∑ᵢ uᵢ vᵢ‖ ≤ ‖∑ᵢ uᵢ uᵢ*‖^(1/2) ‖∑ᵢ vᵢ* vᵢ‖^(1/2)`: the product of a row and a column has norm
at most the product of their norms. -/
theorem norm_sum_mul_le_sqrt_mul_sqrt (u v : ι → A) :
    ‖∑ i, u i * v i‖ ≤ √‖∑ i, u i * star (u i)‖ * √‖∑ i, star (v i) * v i‖ := by
  have h := norm_inner_le (A := A) (WithCStarModule A (ι → A))
    (x := (WithCStarModule.equiv A (ι → A)).symm fun i => star (v i))
    (y := (WithCStarModule.equiv A (ι → A)).symm u)
  simp only [WithCStarModule.pi_inner, WithCStarModule.pi_norm, WithCStarModule.inner_def,
    WithCStarModule.equiv_symm_pi_apply, star_star] at h
  rwa [mul_comm (√_)]

section SelfAdjoint

variable {x : ι → A}

/-- For a self-adjoint family with square sum `T = ∑ⱼ xⱼ²`, the sum `∑ᵢ xᵢ T xᵢ` lies between `0`
and `‖T‖ T`, so its norm is at most `‖T‖²`. -/
theorem norm_sum_mul_sum_mul_self_mul_le (hx : ∀ k, IsSelfAdjoint (x k)) :
    ‖∑ i, x i * (∑ j, x j * x j) * x i‖ ≤ ‖∑ k, x k * x k‖ ^ 2 := by
  have hstar (k : ι) : star (x k) = x k := (hx k).star_eq
  have hT : 0 ≤ ∑ k, x k * x k :=
    Finset.sum_nonneg fun k _ => by simpa only [hstar] using star_mul_self_nonneg (x k)
  have hB : ∑ i, x i * (∑ j, x j * x j) * x i ≤ ‖∑ k, x k * x k‖ • ∑ k, x k * x k := by
    rw [Finset.smul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    simpa only [hstar] using
      CStarAlgebra.star_left_conjugate_le_norm_smul (x i) _ hT.isSelfAdjoint
  have hB₀ : 0 ≤ ∑ i, x i * (∑ j, x j * x j) * x i :=
    Finset.sum_nonneg fun i _ => by simpa only [hstar] using star_left_conjugate_nonneg hT (x i)
  refine (CStarAlgebra.norm_le_norm_of_le_of_nonneg hB hB₀).trans_eq ?_
  rw [norm_smul, norm_norm, sq]

/-- For a self-adjoint family, the crossing sum `∑ᵢ ∑ⱼ xᵢ xⱼ xᵢ xⱼ` is bounded in norm by
`∑ᵢ xᵢ (∑ⱼ xⱼ²) xᵢ`: this is the row–column inequality for the products `xᵢ xⱼ`. -/
theorem norm_sum_sum_mul_mul_mul_le (hx : ∀ k, IsSelfAdjoint (x k)) :
    ‖∑ i, ∑ j, x i * x j * x i * x j‖ ≤ ‖∑ i, x i * (∑ j, x j * x j) * x i‖ := by
  have hstar (k : ι) : star (x k) = x k := (hx k).star_eq
  have h := norm_sum_mul_le_sqrt_mul_sqrt (fun p : ι × ι => x p.1 * x p.2)
    (fun p => x p.1 * x p.2)
  have hrow : ∑ p : ι × ι, x p.1 * x p.2 * star (x p.1 * x p.2) =
      ∑ i, x i * (∑ j, x j * x j) * x i := by
    simp only [Fintype.sum_prod_type, star_mul, hstar, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  have hcol : ∑ p : ι × ι, star (x p.1 * x p.2) * (x p.1 * x p.2) =
      ∑ i, x i * (∑ j, x j * x j) * x i := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp only [star_mul, hstar, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [hrow, hcol, Real.mul_self_sqrt (norm_nonneg _), Fintype.sum_prod_type] at h
  simpa only [mul_assoc] using h

end SelfAdjoint

end TauCeti
