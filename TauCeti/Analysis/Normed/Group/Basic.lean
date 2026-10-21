/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Squared triangle inequality

In a seminormed additive group, the squared distance between two points is at most twice the sum
of their squared distances to any third point: the triangle inequality through `c`, squared with
`(x + y) ^ 2 ≤ 2 (x ^ 2 + y ^ 2)`.

## Main declarations

* `TauCeti.norm_sub_sq_le_two_mul` -- the squared triangle inequality through an intermediate
  point.
-/

public section

namespace TauCeti

/-- **Squared triangle inequality.** The squared distance from `a` to `b` is at most twice the sum
of the squared distances from `a` and from `b` to an intermediate point `c`. -/
theorem norm_sub_sq_le_two_mul {E : Type*} [SeminormedAddCommGroup E] (a b c : E) :
    ‖a - b‖ ^ 2 ≤ 2 * (‖a - c‖ ^ 2 + ‖b - c‖ ^ 2) :=
  (pow_le_pow_left₀ (norm_nonneg _)
    ((norm_sub_le_norm_sub_add_norm_sub a c b).trans_eq (by rw [norm_sub_rev c b])) 2).trans
    add_sq_le

end TauCeti
