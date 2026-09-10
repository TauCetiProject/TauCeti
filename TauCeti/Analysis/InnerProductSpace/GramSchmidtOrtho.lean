/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# The diagonal coefficient of the Gram-Schmidt process

Mathlib's `InnerProductSpace.gramSchmidt_triangular` records that, in the basis `b` it is fed,
`gramSchmidt 𝕜 b i` has no component along `b j` for `i < j`.  This file supplies the diagonal
companion: the component along `b i` itself is `1`, because the Gram-Schmidt step subtracts from
`b i` only vectors spanned by the earlier basis vectors.  Together the two say that the matrix of
the Gram-Schmidt process is lower unitriangular.

## Main results

* `TauCeti.InnerProductSpace.repr_gramSchmidt_self_eq_one` — the Gram-Schmidt process leaves the
  coefficient of a basis vector along itself equal to `1`.
-/

public section

open Finset InnerProductSpace Module

namespace TauCeti

namespace InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

/-- The Gram-Schmidt process does not change the coefficient of a basis vector along itself:
`gramSchmidt 𝕜 b i` differs from `b i` by a combination of the strictly earlier `gramSchmidt`
vectors, each of which has no component along `b i`. -/
theorem repr_gramSchmidt_self_eq_one (b : Basis ι 𝕜 E) (i : ι) :
    b.repr (gramSchmidt 𝕜 b i) i = 1 := by
  have h := congrArg (fun x ↦ b.repr x i) (gramSchmidt_def'' 𝕜 (b : ι → E) i)
  simp only [Basis.repr_self, Finsupp.single_eq_same, map_add, map_sum, map_smul,
    Finsupp.add_apply, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul] at h
  rw [Finset.sum_eq_zero (fun j hj ↦ ?_), add_zero] at h
  · exact h.symm
  · rw [gramSchmidt_triangular (Finset.mem_Iio.mp hj) b, mul_zero]

end InnerProductSpace

end TauCeti
