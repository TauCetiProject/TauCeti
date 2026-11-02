/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Module

/-!
# Vanishing of a family fixed by a matrix

A family `y : n → P` in a module over a ring `A` satisfying `yᵢ = ∑ⱼ Bᵢⱼ • yⱼ` is exactly a
fixed point of Mathlib's `Matrix n n A`-action on `n → P` (`Matrix.Module.matrixModule`), so it
is killed by `1 - B`. If `1 - B` is a unit, `y` vanishes.

This is pure algebra: `P` carries no topology and `A` need not be commutative. Criteria producing
`IsUnit (1 - B)`, such as topological nilpotence of the entries of `B`, live elsewhere, so this
statement applies to abstract subquotients without importing them.

## Main results

* `TauCeti.eq_zero_of_isUnit_one_sub_of_forall_eq_sum_smul`: a family fixed by `B` vanishes as
  soon as `1 - B` is a unit.

## References

* [S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §3.7.2/1, where this is the algebraic engine behind closedness of finitely generated
  submodules.
-/

public section

open scoped Matrix.Module

namespace TauCeti

/-- **A family fixed by a matrix vanishes when `1 - B` is a unit.** If `y : n → P` satisfies
`yᵢ = ∑ⱼ Bᵢⱼ • yⱼ` for every `i` and `1 - B` is invertible in `Matrix n n A`, then `y = 0`. The
ring `A` need not be commutative. -/
theorem eq_zero_of_isUnit_one_sub_of_forall_eq_sum_smul {A : Type*} [Ring A] {n : Type*}
    [Fintype n] [DecidableEq n] {P : Type*} [AddCommGroup P] [Module A P]
    {B : Matrix n n A} (hU : IsUnit (1 - B))
    {y : n → P} (hy : ∀ i, y i = ∑ j, B i j • y j) : y = 0 := by
  refine hU.smul_eq_zero.mp ?_
  rw [sub_smul, one_smul, sub_eq_zero]
  ext i
  rw [Matrix.Module.smul_apply, ← hy i]

end TauCeti
