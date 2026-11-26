/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic

/-!
# Change of coefficients of scalar matrices, and matrices over a product

This file complements the `RingHom.mapMatrix` and `Matrix.prodEquiv` API of
`Mathlib.Data.Matrix.Basic`.

## Main results

* `RingHom.mapMatrix_smul_one`: `f.mapMatrix` sends the scalar matrix `a • 1` to `f a • 1`.
* `Matrix.map_fst_prodEquiv_symm`, `Matrix.map_snd_prodEquiv_symm`: the components of the matrix
  over `α × β` built from a pair of matrices are the two matrices of the pair.
* `Matrix.mul_eq_of_map_fst_of_map_snd`: a product of matrices over `A × B` is determined by its
  two components.
-/

public section

namespace RingHom

/-- `f.mapMatrix` sends the scalar matrix `a • 1` to `f a • 1`. -/
theorem mapMatrix_smul_one {m α β : Type*} [Fintype m] [DecidableEq m]
    [NonAssocSemiring α] [NonAssocSemiring β] (f : α →+* β) (a : α) :
    f.mapMatrix (a • (1 : Matrix m m α)) = f a • 1 := by
  rw [f.mapMatrix_apply, Matrix.map_smul' _ _ _ (map_mul f),
    Matrix.map_one _ (map_zero f) (map_one f)]

end RingHom

namespace Matrix

/-! ### Matrices over a product -/

section Prod

variable {m n : Type*}

-- Not `@[simp]`: `Matrix.prodEquiv_symm_apply` already rewrites the left-hand side.
/-- The first component of the matrix over `α × β` with components `p.1` and `p.2` is `p.1`. -/
theorem map_fst_prodEquiv_symm {α β : Type*} (p : Matrix m n α × Matrix m n β) :
    ((prodEquiv m n α β).symm p).map Prod.fst = p.1 := by
  simpa only [prodEquiv_apply] using congrArg Prod.fst ((prodEquiv m n α β).apply_symm_apply p)

-- Not `@[simp]`: `Matrix.prodEquiv_symm_apply` already rewrites the left-hand side.
/-- The second component of the matrix over `α × β` with components `p.1` and `p.2` is `p.2`. -/
theorem map_snd_prodEquiv_symm {α β : Type*} (p : Matrix m n α × Matrix m n β) :
    ((prodEquiv m n α β).symm p).map Prod.snd = p.2 := by
  simpa only [prodEquiv_apply] using congrArg Prod.snd ((prodEquiv m n α β).apply_symm_apply p)

/-- A product of matrices over `A × B` is determined by its two components: both component maps
are multiplicative. -/
theorem mul_eq_of_map_fst_of_map_snd {A B ν : Type*} [NonUnitalNonAssocSemiring A]
    [NonUnitalNonAssocSemiring B] [Fintype ν] {P : Matrix m ν (A × B)} {Q : Matrix ν n (A × B)}
    {R : Matrix m n (A × B)} (hfst : P.map Prod.fst * Q.map Prod.fst = R.map Prod.fst)
    (hsnd : P.map Prod.snd * Q.map Prod.snd = R.map Prod.snd) : P * Q = R := by
  refine (prodEquiv m n A B).injective (Prod.ext ?_ ?_)
  · simpa only [prodEquiv_apply, ← NonUnitalRingHom.coe_fst, ← Matrix.map_mul] using hfst
  · simpa only [prodEquiv_apply, ← NonUnitalRingHom.coe_snd, ← Matrix.map_mul] using hsnd

end Prod

end Matrix
