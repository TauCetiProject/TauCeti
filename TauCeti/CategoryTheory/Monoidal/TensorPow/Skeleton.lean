/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Skeleton
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Basic

/-!
# Tensor powers in the skeleton of a monoidal category

In the skeleton of a monoidal category `C`, the monoidal product is multiplication and the monoidal
unit is `1`. Consequently, passing to the skeleton sends `TauCeti.tensorPow X n` to the `n`-th
power `toSkeleton X ^ n` (`TauCeti.toSkeleton_tensorPow`).

## Main results

* `TauCeti.toSkeleton_tensorPow`: `toSkeleton (tensorPow X n) = toSkeleton X ^ n`.
-/

public section

open CategoryTheory MonoidalCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Passing to the skeleton sends the `n`-th tensor power of an object to its `n`-th power in the
skeleton monoid. -/
@[simp]
theorem toSkeleton_tensorPow (X : C) (n : ℕ) :
    toSkeleton (tensorPow X n) = toSkeleton X ^ n := by
  induction n with
  | zero => exact Skeleton.one_eq.symm
  | succ n ih => rw [tensorPow_succ, Skeleton.toSkeleton_tensorObj, ih, pow_succ']

end TauCeti
