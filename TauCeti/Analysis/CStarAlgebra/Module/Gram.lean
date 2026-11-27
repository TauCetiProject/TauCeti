/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import TauCeti.Analysis.CStarAlgebra.CStarMatrix

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt
import TauCeti.Analysis.CStarAlgebra.Module.Basic

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
* `TauCeti.CStarMatrix.isSelfAdjoint_gram`: Gram matrices are self-adjoint (purely algebraically).
* `CStarMatrix.sum_star_mul_gram_mul`: the quadratic forms of a Gram matrix are inner products.
* `TauCeti.CStarMatrix.sum_inner_smul_of_gram_eq_one`: a family with identity Gram matrix
  reconstructs every vector in its right `A`-linear span.
* `CStarMatrix.gram_nonneg`: Gram matrices are positive.
* `TauCeti.CStarMatrix.exists_gram_eq_one_of_isStrictlyPositive`: a finite family with strictly
  positive Gram matrix can be renormalized to one with Gram matrix `1` spanning the same vectors.

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

variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E]

/-- The Gram matrix of a finite family in a right Hilbert C⋆-module is positive. -/
theorem gram_nonneg [Fintype n] (x : n → E) : 0 ≤ gram A x :=
  nonneg_iff_forall_sum_nonneg.mpr fun a => by
    rw [sum_star_mul_gram_mul, unop_nonneg]
    exact CStarModule.inner_self_nonneg

end CStarMatrix

namespace TauCeti.CStarMatrix

variable {A E n : Type*}

section SelfAdjoint

variable [NonUnitalRing A] [StarRing A] [Module ℂ A] [PartialOrder A] [Norm Aᵐᵒᵖ]
  [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E]

/-- Every Gram matrix is self-adjoint, by the conjugate symmetry of the module inner product. -/
theorem isSelfAdjoint_gram (x : n → E) : IsSelfAdjoint (_root_.CStarMatrix.gram A x) := by
  ext i j
  simp [_root_.CStarMatrix.star_apply, _root_.CStarMatrix.gram_apply, ← unop_star]

end SelfAdjoint

section UnitalAlgebraic

variable [Fintype n] [DecidableEq n] [Ring A] [StarRing A] [Module ℂ A] [PartialOrder A]
  [Norm Aᵐᵒᵖ] [AddCommGroup E] [Module ℂ E] [SMul Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E]

/-- If a finite family `x : n → E` has identity Gram matrix `gram A x = 1`, pairing `x i` against
a right linear combination `∑ j, op (c j) • x j` recovers the `i`-th coefficient `op (c i)`. -/
theorem inner_sum_op_smul_of_gram_eq_one {x : n → E} (hx : _root_.CStarMatrix.gram A x = 1)
    (c : n → A) (i : n) :
    inner Aᵐᵒᵖ (x i) (∑ j, op (c j) • x j) = op (c i) := by
  apply unop_injective; rw [TauCeti.CStarModule.inner_sum_right', Finset.unop_sum]
  have hgram (j : n) : unop (inner Aᵐᵒᵖ (x i) (x j)) = (1 : _root_.CStarMatrix n n A) i j := by
    rw [← _root_.CStarMatrix.gram_apply, hx]
  simp [CStarModule.inner_op_smul_right, hgram, _root_.CStarMatrix.one_apply]

/-- A finite family `x : n → E` with identity Gram matrix `gram A x = 1` reconstructs every vector
in its right `A`-linear span by `u = ∑ i, ⟪x i, u⟫ • x i`. -/
theorem sum_inner_smul_of_gram_eq_one {x : n → E} (hx : _root_.CStarMatrix.gram A x = 1) {u : E}
    (hu : ∃ c : n → A, ∑ j, op (c j) • x j = u) :
    ∑ i, inner Aᵐᵒᵖ (x i) u • x i = u := by
  obtain ⟨c, rfl⟩ := hu
  simp_rw [inner_sum_op_smul_of_gram_eq_one hx c]

end UnitalAlgebraic

/-- Over a unital C⋆-algebra `A`, a finite family `y : n → E` with strictly positive Gram matrix
`IsStrictlyPositive (gram A y)` can be renormalized by `B = CFC.sqrt (Ring.inverse (gram A y))`
to a family `j ↦ ∑ k, op (B k j) • y k` with Gram matrix `1` spanning the same vectors. -/
theorem exists_gram_eq_one_of_isStrictlyPositive [Fintype n] [DecidableEq n] {A E : Type*}
    [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [AddCommGroup E] [Module ℂ E] [Module Aᵐᵒᵖ E] [Norm E] [CStarModule Aᵐᵒᵖ E] {y : n → E}
    (hM : IsStrictlyPositive (_root_.CStarMatrix.gram A y)) :
    ∃ B S : _root_.CStarMatrix n n A,
      _root_.CStarMatrix.gram A (fun j ↦ ∑ k, op (B k j) • y k) = 1 ∧
      ∀ k, ∑ j, op (S j k) • ∑ l, op (B l j) • y l = y k := by
  have : ContinuousFunctionalCalculus ℝ (_root_.CStarMatrix n n A) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  set M := _root_.CStarMatrix.gram A y
  let S := CFC.sqrt M
  let B := CFC.sqrt (Ring.inverse M)
  have hBS : B * S = 1 := by
    dsimp only [B, S]
    rw [CFC.sqrt_ringInverse]
    exact Ring.inverse_mul_cancel (CFC.sqrt M) (hM.sqrt M).isUnit
  refine ⟨B, S, ?_, fun k ↦ ?_⟩
  · ext i j
    rw [_root_.CStarMatrix.gram_apply, ← _root_.CStarMatrix.sum_star_mul_gram_mul]
    have hmul : (star B * M * B) i j = ∑ k, ∑ l, star (B k i) * M k l * B l j := by
      simp only [_root_.CStarMatrix.mul_apply, _root_.CStarMatrix.star_apply, Finset.sum_mul,
        mul_assoc]
      exact Finset.sum_comm
    rw [← hmul, (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq, ← CFC.conjSqrt_apply,
      CFC.conjSqrt_ringInverse_self M hM]
  · simp only [Finset.smul_sum, smul_smul, ← op_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, ← Finset.op_sum, ← _root_.CStarMatrix.mul_apply, hBS,
      _root_.CStarMatrix.one_apply, apply_ite op, ite_smul]
    simp

end TauCeti.CStarMatrix
