/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Replacing one basis vector by an arbitrary vector

Let `f` be an alternating map of `n + 1` arguments and `b` a basis indexed by `Fin (n + 1)`.
Evaluating `f` on a vector `w` followed by the basis with its `i`-th vector removed gives
`(-1) ^ i` times the `i`-th coordinate of `w`, times `f b`. This is the coordinate formula for
the contraction of a top-degree form with a vector, the alternating-map form of Cramer's rule.
-/

public section

namespace AlternatingMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M]
  [Module R N] {n : ℕ}

/-- Evaluating an alternating map on `w` followed by the basis `b` with its `i`-th vector removed
gives `(-1) ^ i` times the `i`-th coordinate of `w` times the value on `b`. -/
theorem map_vecCons_removeNth_basis (f : M [⋀^Fin (n + 1)]→ₗ[R] N)
    (b : Module.Basis (Fin (n + 1)) R M) (w : M) (i : Fin (n + 1)) :
    f (Matrix.vecCons w (i.removeNth b)) = ((-1) ^ (i : ℕ) * b.repr w i) • f b := by
  classical
  -- Move `w` into the `i`-th slot, then expand it in the basis: only its `i`-th coordinate
  -- survives, since every other basis vector already occurs among the remaining arguments.
  rw [← f.neg_one_pow_smul_map_insertNth, Fin.insertNth_removeNth]
  conv_lhs => rw [← b.sum_repr w]
  rw [f.map_update_sum, Finset.sum_eq_single i]
  · rw [f.map_update_smul, Function.update_eq_self]
    simp [mul_smul, ← Int.cast_smul_eq_zsmul R]
  · intro j _ hji
    rw [f.map_update_smul, f.map_update_self _ hji.symm, smul_zero]
  · simp

end AlternatingMap
