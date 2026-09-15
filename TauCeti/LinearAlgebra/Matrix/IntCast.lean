/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic

/-!
# Entrywise integer casts of matrices

An integral matrix is read over an arbitrary ring by casting its entries. The cast is the ring
morphism `Int.castRingHom`, so `Matrix.map_mul` already says that it turns a product into a
product; what that lemma is stated for is the bundled morphism, whose coercion does not match the
unbundled `Int.cast` that explicit tables are read with. This file records the unbundled form,
which is the one an explicitly tabulated integral matrix is used in.

Addition needs no such lemma: `Matrix.map_add _ Int.cast_add` is already in the unbundled form.

## Main results

* `Matrix.map_intCast_mul`: entrywise integer casts turn a matrix product into the product of the
  casts.
-/

public section

namespace Matrix

/-- **Entrywise integer casts turn a matrix product into the product of the casts.** -/
theorem map_intCast_mul {l m n R : Type*} [Fintype m] [NonAssocRing R] (M : Matrix l m ℤ)
    (N : Matrix m n ℤ) :
    (M * N).map (Int.cast : ℤ → R) =
      M.map (Int.cast : ℤ → R) * N.map (Int.cast : ℤ → R) := by
  ext a b
  rw [map_apply, mul_apply, mul_apply, Int.cast_sum]
  exact Finset.sum_congr rfl fun c _ => by rw [Int.cast_mul, map_apply, map_apply]

end Matrix
