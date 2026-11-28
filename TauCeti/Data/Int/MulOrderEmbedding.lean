/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.PNat.Defs
public import Mathlib.Order.Hom.Basic

/-!
# Multiplication by a positive integer as an order embedding of `ℤ`

Mathlib's `OrderEmbedding.mulLeft` needs strict monotonicity of multiplication on the left in
every factor, which `ℤ` lacks because of `0` and the negative integers. Multiplication by a
positive integer `d` is still strictly monotone, so it is an order embedding of `ℤ`.

## Main definitions

* `Int.mulOrderEmbedding d`: the order embedding `k ↦ d * k` of `ℤ` for `d : ℕ+`.
-/

public section

namespace Int

/-- Multiplication by a positive integer as an order embedding of `ℤ`. -/
def mulOrderEmbedding (d : ℕ+) : ℤ ↪o ℤ :=
  OrderEmbedding.ofStrictMono (fun k ↦ (d : ℤ) * k)
    (strictMono_mul_left_of_pos (by exact_mod_cast d.pos))

/-- `Int.mulOrderEmbedding d` sends `k` to `d * k`. -/
@[simp]
theorem mulOrderEmbedding_apply (d : ℕ+) (k : ℤ) : mulOrderEmbedding d k = d * k :=
  (rfl)

end Int
