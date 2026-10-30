/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Data.Matrix.Mul

/-!
# Infinitesimal matrices over the dual numbers

A matrix over `R` becomes infinitesimal over the dual numbers `TrivSqZeroExt R R` when its
entries are multiplied by `ε`, that is, mapped entrywise by `TrivSqZeroExt.inr`. Products of two
such matrices vanish, so a product of matrices `1 + ε M_a` is `1 + ε ∑ M_a`, and `1 + ε M` acts on
a dual vector `u + ε u'` as `u + ε (M u + u')`. These are the computations behind reading off a
differential from an evaluation at dual numbers.
-/

public section

open TrivSqZeroExt

variable {R : Type*} [Semiring R]

namespace Matrix

variable {l m n : Type*}

/-- The product of two infinitesimal matrices vanishes. -/
theorem map_inr_mul_map_inr [Fintype m] (M : Matrix l m R) (N : Matrix m n R) :
    M.map (inr : R → TrivSqZeroExt R R) * N.map (inr : R → TrivSqZeroExt R R) = 0 := by
  ext i j : 1
  simp [Matrix.mul_apply, inr_mul_inr]

/-- The matrix `1 + ε M` acts on the dual vector `u + ε u'` as `u + ε (M u + u')`. -/
theorem one_add_map_inr_mulVec [Fintype n] [DecidableEq n] (M : Matrix n n R) (u u' : n → R) :
    (1 + M.map (inr : R → TrivSqZeroExt R R)) *ᵥ (fun i ↦ inl (u i) + inr (u' i)) =
      fun i ↦ inl (u i) + inr ((M *ᵥ u + u') i) := by
  ext i
  · simp [mulVec, dotProduct, Matrix.one_apply, fst_sum, add_mul, ite_mul, apply_ite fst]
  · simp [mulVec, dotProduct, Matrix.one_apply, snd_sum, add_mul, ite_mul, Finset.sum_add_distrib,
      add_comm]

end Matrix

namespace List

/-- A product of matrices `1 + ε M_a` is `1 + ε ∑ M_a`, since products of infinitesimal matrices
vanish. -/
theorem prod_map_one_add_map_inr {α n : Type*} [Fintype n] [DecidableEq n] (l : List α)
    (M : α → Matrix n n R) :
    (l.map fun a ↦ 1 + (M a).map (inr : R → TrivSqZeroExt R R)).prod =
      1 + (l.map M).sum.map inr := by
  induction l with
  | nil => simp [Matrix.map_zero _ (inr_zero R)]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.sum_cons, add_mul, one_mul,
      mul_add, mul_one, Matrix.map_inr_mul_map_inr, add_zero, Matrix.map_add _ (inr_add R)]
    abel

end List
