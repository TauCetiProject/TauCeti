/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import TauCeti.LinearAlgebra.TensorProduct.Range

/-!
# Descent of bracket equations after extension of scalars

The adjoint endomorphism of a Lie algebra commutes with extension of scalars.  Consequently, a
bracket equation `x = ⁅x, y⁆` that has a solution after a faithfully flat extension already has a
solution over the original coefficient ring.  In particular, passing to an algebraic closure cannot
create a solution to such an equation.

The compatibility with the adjoint action uses `LieModule.toEnd_baseChange` from
`Mathlib/Algebra/Lie/BaseChange.lean`.

## Main results

* `LieAlgebra.exists_eq_lie_of_one_tmul_mem_range_ad`: membership of `1 ⊗ₜ x` in the range of
  the extended adjoint endomorphism descends to an equation `x = ⁅x, y⁆`.
-/

public section

open TensorProduct
open scoped TensorProduct

namespace LieAlgebra

universe u v w

variable (R : Type u) (A : Type v) (L : Type w)
variable [CommRing R] [CommRing A] [Algebra R A]
variable [LieRing L] [LieAlgebra R L]

/-- A bracket equation that becomes solvable after a faithfully flat extension of scalars was
already solvable over the original coefficient ring. -/
theorem exists_eq_lie_of_one_tmul_mem_range_ad [Module.FaithfullyFlat R A] (x : L)
    (hx : (1 : A) ⊗ₜ[R] x ∈
      LinearMap.range (ad A (A ⊗[R] L) ((1 : A) ⊗ₜ[R] x))) :
    ∃ y : L, x = ⁅x, y⁆ := by
  have had : ad A (A ⊗[R] L) ((1 : A) ⊗ₜ[R] x) = (ad R L x).baseChange A :=
    LieModule.toEnd_baseChange R A L L x
  rw [had] at hx
  obtain ⟨y, hy⟩ := (LinearMap.one_tmul_mem_range_baseChange_iff (ad R L x) x).mp hx
  exact ⟨y, by simpa only [ad_apply] using hy.symm⟩

end LieAlgebra
