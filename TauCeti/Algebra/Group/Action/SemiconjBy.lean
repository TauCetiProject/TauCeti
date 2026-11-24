/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs

/-!
# Scalar-twisted commutation with products

When an element `x` of a semigroup commutes past `b` and `c` up to compatible scalars `s` and `t`,
so that `x * b = s • (b * x)` and `x * c = t • (c * x)`, it commutes past `b * c` up to `s * t`.
Dually, when `a` and `c` commute past `b` up to `s` and `t`, their product `a * c` commutes past
`b` up to `t * s`. These closure rules parallel `SemiconjBy.mul_right` and `SemiconjBy.mul_left`
for Koszul supercommutation and `q`-commutation relations.

## Main results

* `TauCeti.mul_mul_eq_smul_of_mul_eq_smul_right`: closure under multiplication in the right factor.
* `TauCeti.mul_mul_eq_smul_of_mul_eq_smul_left`: closure under multiplication in the left factor.
-/

public section

namespace TauCeti

variable {M α : Type*} [Mul M] [Semigroup α] [SMul M α]
  [IsScalarTower M M α] [IsScalarTower M α α] [SMulCommClass M α α]

/-- If `x` commutes past `b` and `c` up to scalars `s` and `t`, then `x` commutes past `b * c`
up to `s * t`. -/
theorem mul_mul_eq_smul_of_mul_eq_smul_right {x b c : α} {s t : M}
    (hb : x * b = s • (b * x)) (hc : x * c = t • (c * x)) :
    x * (b * c) = (s * t) • ((b * c) * x) := by
  calc
    x * (b * c) = x * b * c := (mul_assoc x b c).symm
    _ = s • (b * (x * c)) := by rw [hb, smul_mul_assoc, mul_assoc]
    _ = (s * t) • ((b * c) * x) := by rw [hc, mul_smul_comm, ← smul_assoc, smul_eq_mul, mul_assoc]

/-- If `a` and `c` commute past `b` up to scalars `s` and `t`, then `a * c` commutes past `b`
up to `t * s`. -/
theorem mul_mul_eq_smul_of_mul_eq_smul_left {a c b : α} {s t : M}
    (ha : a * b = s • (b * a)) (hc : c * b = t • (b * c)) :
    a * c * b = (t * s) • (b * (a * c)) := by
  calc
    a * c * b = a * (c * b) := mul_assoc a c b
    _ = t • (a * b * c) := by rw [hc, mul_smul_comm, mul_assoc]
    _ = (t * s) • (b * (a * c)) := by rw [ha, smul_mul_assoc, ← smul_assoc, smul_eq_mul, mul_assoc]

end TauCeti
