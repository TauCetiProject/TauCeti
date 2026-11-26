/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Exponentials of elements with vanishing cube, with only `½` inverted

Let `A` be a commutative ring, `M` an `A`-algebra, and `N : M` with `N³ = 0`. Given `h : A` with
`2h = 1`, the truncated exponential

```text
exp(a N) = 1 + a N + h a² N²
```

is additive in `a : A`: `exp((a + b) N) = exp(a N) exp(b N)`
(`TauCeti.one_add_smul_add_smul_mul_self_add`). Unlike `IsNilpotent.exp`, which divides by every
factorial and so needs a `ℚ`-algebra, this needs only `½`, as for the short root subgroups of the
odd orthogonal groups.
-/

public section

namespace TauCeti

variable {A M : Type*} [CommRing A] [Ring M] [Algebra A M]

/-- **The exponential of an element with vanishing cube is additive**: if `N³ = 0` and `2h = 1`,
then `exp((a + b) N) = exp(a N) exp(b N)`, where `exp(a N) = 1 + a N + h a² N²`. -/
theorem one_add_smul_add_smul_mul_self_add {N : M} {h : A} (hh : 2 * h = 1)
    (h3 : N * N * N = 0) (a b : A) :
    1 + (a + b) • N + (h * (a + b) * (a + b)) • (N * N) =
      (1 + a • N + (h * a * a) • (N * N)) * (1 + b • N + (h * b * b) • (N * N)) := by
  have h3' : N * (N * N) = 0 := by rw [← mul_assoc, h3]
  have h4 : N * N * (N * N) = 0 := by rw [← mul_assoc, h3, zero_mul]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_assoc, mul_smul_comm]
  simp only [h3, h3', h4, smul_zero, add_zero]
  linear_combination (norm := module) (a * b * hh) • (N * N)

end TauCeti
