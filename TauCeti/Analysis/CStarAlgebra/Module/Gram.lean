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
* `CStarMatrix.isSelfAdjoint_gram`: Gram matrices are self-adjoint (purely algebraically).
* `CStarMatrix.sum_star_mul_gram_mul`: the quadratic forms of a Gram matrix are inner products.
* `CStarMatrix.sum_inner_smul_of_gram_eq_one`: a family with identity Gram matrix reconstructs
  every vector in its right `A`-linear span.
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

section SelfAdjoint

variable [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm Aᵐᵒᵖ]
  [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E]

/-- Every Gram matrix is self-adjoint, by the conjugate symmetry of the module inner product. -/
theorem isSelfAdjoint_gram (x : n → E) : IsSelfAdjoint (gram A x) := by
  ext i j
  simp [CStarMatrix.star_apply, gram_apply, ← unop_star, CStarModule.star_inner]

end SelfAdjoint

section Algebraic

variable [NonUnitalSeminormedRing A] [StarRing A] [Module ℂ A] [StarModule ℂ A] [PartialOrder A]
  [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E]

/-- The quadratic forms of a Gram matrix are the inner products of the corresponding right
linear combinations. This only uses the algebraic `CStarModule` axioms, so the coefficients need
not form a complete C⋆-algebra. -/
lemma sum_star_mul_gram_mul [Fintype n] (x : n → E) (a b : n → A) :
    ∑ i, ∑ j, star (a i) * gram A x i j * b j =
      unop (inner Aᵐᵒᵖ (∑ i, op (a i) • x i) (∑ j, op (b j) • x j)) := by
  rw [Finset.sum_comm]
  simp only [gram_apply, CStarModule.inner_sum_right, CStarModule.inner_op_smul_right,
    CStarModule.inner_sum_left, CStarModule.inner_op_smul_left, Finset.unop_sum, unop_mul,
    unop_star, unop_op, Finset.sum_mul, mul_assoc]

end Algebraic

section UnitalAlgebraic

variable [Fintype n] [DecidableEq n] [Ring A] [StarRing A] [Module ℂ A] [PartialOrder A]
  [Norm Aᵐᵒᵖ] [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E]

/-- If a finite family `x : n → E` has identity Gram matrix `gram A x = 1`, pairing `x i` against
a right linear combination `∑ j, op (c j) • x j` recovers the `i`-th coefficient `op (c i)`. -/
theorem inner_sum_op_smul_of_gram_eq_one {x : n → E} (hx : gram A x = 1) (c : n → A) (i : n) :
    inner Aᵐᵒᵖ (x i) (∑ j, op (c j) • x j) = op (c i) := by
  apply unop_injective
  have hsum : inner Aᵐᵒᵖ (x i) (∑ j, op (c j) • x j) = ∑ j, inner Aᵐᵒᵖ (x i) (op (c j) • x j) :=
    map_sum (AddMonoidHom.mk' (inner Aᵐᵒᵖ (x i)) fun _ _ ↦ CStarModule.inner_add_right) _ _
  rw [hsum, Finset.unop_sum]
  have hgram (j : n) : unop (inner Aᵐᵒᵖ (x i) (x j)) = (1 : CStarMatrix n n A) i j := by
    rw [← gram_apply, hx]
  simp [CStarModule.inner_op_smul_right, hgram, one_apply]

/-- A finite family `x : n → E` with identity Gram matrix `gram A x = 1` reconstructs every vector
in its right `A`-linear span by `u = ∑ i, ⟪x i, u⟫ • x i`. -/
theorem sum_inner_smul_of_gram_eq_one {x : n → E} (hx : gram A x = 1) {u : E}
    (hu : ∃ c : n → A, ∑ j, op (c j) • x j = u) :
    ∑ i, inner Aᵐᵒᵖ (x i) u • x i = u := by
  obtain ⟨c, rfl⟩ := hu
  simp_rw [inner_sum_op_smul_of_gram_eq_one hx c]

end UnitalAlgebraic

variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E]

/-- The Gram matrix of a finite family in a right Hilbert C⋆-module is positive. -/
theorem gram_nonneg [Fintype n] (x : n → E) : 0 ≤ gram A x :=
  nonneg_iff_forall_sum_nonneg.mpr fun a => by
    rw [sum_star_mul_gram_mul, unop_nonneg]
    exact CStarModule.inner_self_nonneg

end CStarMatrix
