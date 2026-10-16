/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Pointwise.Set

/-!
# Pointwise set addition in distributive scalar actions

This file records the distributivity of a scalar action over the Minkowski sum of two sets. It is
the set-level counterpart of `smul_add`; unlike the one-sided inclusion `Set.add_smul_subset`, it
uses a single scalar on both summands and is therefore an equality.

## Main results

* `Set.smul_set_add`: scalar multiplication distributes over pointwise set addition.
-/

public section

open scoped Pointwise

namespace Set

variable {α E : Type*} [AddMonoid E] [DistribSMul α E]

/-- Scalar multiplication distributes over Minkowski addition of sets. -/
@[simp] theorem smul_set_add (c : α) (A B : Set E) : c • (A + B) = c • A + c • B :=
  image_image2_distrib (smul_add c)

end Set
