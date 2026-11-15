/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Module
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrix modules

A family `y : n → P` in a module over a ring `A` satisfying `yᵢ = ∑ⱼ Bᵢⱼ • yⱼ` is exactly a
fixed point of Mathlib's `Matrix n n A`-action on `n → P` (`Matrix.Module.matrixModule`), so it
is killed by `1 - B`. If `1 - B` is a unit, `y` vanishes.

This is pure algebra: `P` carries no topology and `A` need not be commutative. Criteria producing
`IsUnit (1 - B)`, such as topological nilpotence of the entries of `B`, live elsewhere, so this
statement applies to abstract subquotients without importing them.

The scoped column action on `ι → R` agrees with the matrix-to-endomorphism algebra
equivalence; in particular its action map is bijective. This identifies the matrix module
used by matrix Morita equivalence with the usual full endomorphism representation.

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

namespace Matrix.Module

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The scoped column action agrees with the usual matrix-to-endomorphism equivalence. -/
theorem lsmul_eq_toLinAlgEquiv' :
    (Algebra.lsmul R R (ι → R) : Matrix ι ι R →ₐ[R] _) =
      Matrix.toLinAlgEquiv'.toAlgHom := by
  ext a v i
  simp [Matrix.Module.smul_apply, Matrix.mulVec, dotProduct]

/-- The native column action is the full endomorphism algebra of the column space. -/
theorem lsmul_bijective :
    Function.Bijective (Algebra.lsmul R R (ι → R) : Matrix ι ι R →ₐ[R] _) := by
  rw [lsmul_eq_toLinAlgEquiv']
  exact Matrix.toLinAlgEquiv'.bijective

end Matrix.Module
