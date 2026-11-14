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
bound is the Cauchy–Schwarz inequality of that module. Since `D` need not be unital, the
three-factor bound is not the special case `x = 1` of the two-factor one; it follows by applying
the two-factor bound to `aₖ x` instead.

## Main declarations

* `Finset.norm_sum_mul_sq_le`: `‖∑ aₖ bₖ‖² ≤ ‖∑ aₖ aₖ⋆‖ ‖∑ bₖ⋆ bₖ‖`.
* `Finset.norm_sum_mul_mul_sq_le`: `‖∑ aₖ x bₖ‖² ≤ ‖∑ aₖ aₖ⋆‖ ‖x‖² ‖∑ bₖ⋆ bₖ‖`.

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

end Finset
