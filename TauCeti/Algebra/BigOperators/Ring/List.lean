/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Shifting one factor of a list product by a scalar

In an `R`-algebra `A`, the product of a list is affine in each factor. In particular, shifting one
factor `a` by the scalar `algebraMap R A c` changes the product by `c` times the product of the
list with that factor deleted. This is the step that centres one letter of a word at a time.

## Main results

* `List.prod_append_sub_algebraMap_cons`:
  `(l₁ ++ (a - algebraMap R A c) :: l₂).prod = (l₁ ++ a :: l₂).prod - c • (l₁ ++ l₂).prod`.
-/

public section

namespace List

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- Shifting the factor `a` of the product of `l₁ ++ a :: l₂` by the scalar `algebraMap R A c`
subtracts `c` times the product of `l₁ ++ l₂`. -/
theorem prod_append_sub_algebraMap_cons (l₁ l₂ : List A) (a : A) (c : R) :
    (l₁ ++ (a - algebraMap R A c) :: l₂).prod = (l₁ ++ a :: l₂).prod - c • (l₁ ++ l₂).prod := by
  simp only [prod_append, prod_cons, sub_mul, mul_sub, Algebra.smul_def, Algebra.left_comm _ c]

end List
