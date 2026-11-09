/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.Module.Defs

/-!
# Gram matrices in right Hilbert C⋆-modules

A right Hilbert `A`-module is represented, following Mathlib's convention, as
`CStarModule Aᵐᵒᵖ E`: the right action `x a` is `MulOpposite.op a • x` and the `A`-valued inner
product is `MulOpposite.unop (inner Aᵐᵒᵖ x y)`. For a finite family `x : n → E`, its Gram matrix
`CStarMatrix.gram A x` has entries `⟨x i, x j⟩_A` and lies in the C⋆-algebra
`CStarMatrix n n A`.

The Gram matrix is positive. Its quadratic forms are the inner products of the corresponding
combinations, `∑ i j, (a i)⋆ ⟨x i, x j⟩_A (b j) = ⟨∑ i, x i a i, ∑ j, x j b j⟩_A`, so this follows
from the quadratic-form criterion `CStarMatrix.nonneg_iff_forall_sum_nonneg`. Positivity of Gram
matrices is the basic input for positivity of the inner products on interior tensor products and
for the comparison between finite frames and projections.

## Main declarations

* `CStarMatrix.gram`: the Gram matrix of a finite family in a right Hilbert C⋆-module.
* `CStarMatrix.sum_star_mul_gram_mul`: the quadratic forms of a Gram matrix are inner products.
* `CStarMatrix.gram_nonneg`: Gram matrices are positive.

## References

* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Lemma 4.2.
* I. Raeburn and D. P. Williams, *Morita Equivalence and Continuous-Trace C⋆-Algebras*,
  Lemma 2.65.
-/

public section

open MulOpposite

namespace CStarMatrix

variable {A E n : Type*}

/-- The Gram matrix `(⟨x i, x j⟩_A)_(i,j)` of a family `x` of vectors in a right Hilbert
`A`-module `E`, given as `CStarModule Aᵐᵒᵖ E`. -/
def gram (A : Type*) [Inner Aᵐᵒᵖ E] (x : n → E) : CStarMatrix n n A :=
  ofMatrix (Matrix.of fun i j => unop (inner Aᵐᵒᵖ (x i) (x j)))

@[simp]
lemma gram_apply [Inner Aᵐᵒᵖ E] (x : n → E) (i j : n) :
    gram A x i j = unop (inner Aᵐᵒᵖ (x i) (x j)) := (rfl)

variable [NonUnitalCStarAlgebra A] [PartialOrder A]
  [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E]

/-- The quadratic forms of a Gram matrix are the inner products of the corresponding right
linear combinations. -/
lemma sum_star_mul_gram_mul [Fintype n] (x : n → E) (a b : n → A) :
    ∑ i, ∑ j, star (a i) * gram A x i j * b j =
      unop (inner Aᵐᵒᵖ (∑ i, op (a i) • x i) (∑ j, op (b j) • x j)) := by
  rw [Finset.sum_comm]
  simp only [gram_apply, CStarModule.inner_sum_right, CStarModule.inner_op_smul_right,
    CStarModule.inner_sum_left, CStarModule.inner_op_smul_left, Finset.unop_sum, unop_mul,
    unop_star, unop_op, Finset.sum_mul, mul_assoc]

variable [StarOrderedRing A]

/-- The Gram matrix of a finite family in a right Hilbert C⋆-module is positive. -/
theorem gram_nonneg [Fintype n] (x : n → E) : 0 ≤ gram A x :=
  nonneg_iff_forall_sum_nonneg.mpr fun a => by
    rw [sum_star_mul_gram_mul, unop_nonneg]
    exact CStarModule.inner_self_nonneg

end CStarMatrix
