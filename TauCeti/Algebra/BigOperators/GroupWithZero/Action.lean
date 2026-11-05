/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.NoncommProd

/-!
# Scalar multiplication of noncommutative products

Mathlib's `Finset.smul_prod` says that scaling every factor of a product over `s` by `b` scales
the product by `b ^ s.card`. This file proves the same for the product `Finset.noncommProd` of a
family that commutes pairwise on `s`, in a possibly noncommutative monoid.

## Main results

* `Finset.smul_noncommProd`: `b ^ s.card • s.noncommProd f _ = s.noncommProd (b • f ·) _`.
-/

public section

open scoped Function

namespace Finset

variable {ι M N : Type*}

/-- Scaling every factor of a noncommutative product over `s` by `b` scales the product by
`b ^ s.card`. -/
theorem smul_noncommProd [Monoid M] [Monoid N] [MulAction M N] [IsScalarTower M N N]
    [SMulCommClass M N N] (s : Finset ι) (b : M) (f : ι → N)
    (comm : (s : Set ι).Pairwise (Commute on f)) :
    b ^ s.card • s.noncommProd f comm =
      s.noncommProd (fun i ↦ b • f i) (comm.mono' fun _ _ h ↦ (h.smul_left b).smul_right b) := by
  induction s using cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [noncommProd_cons, noncommProd_cons, ← ih (comm.mono (by simp)), smul_mul_smul_comm,
      card_cons, pow_succ']

end Finset
