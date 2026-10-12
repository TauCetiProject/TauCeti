/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import TauCeti.LinearAlgebra.TensorProduct.Range

/-!
# Extension of Lie submodules and descent of bracket equations

Over a faithfully flat coefficient algebra, membership of `1 ⊗ₜ x` in the extension of a Lie
submodule descends to membership of `x` in the submodule itself; this is the underlying
`Submodule.one_tmul_mem_baseChange_iff` read through `LieSubmodule.coe_baseChange`.
Extension of scalars preserves arbitrary suprema of Lie submodules, and under faithful flatness
it also reflects their equality, by `LieSubmodule.baseChange_inj`.

The adjoint endomorphism of a Lie algebra commutes with extension of scalars.  Consequently, a
bracket equation `x = ⁅x, y⁆` that has a solution after a faithfully flat extension already has a
solution over the original coefficient ring.  In particular, passing to an algebraic closure cannot
create a solution to such an equation.

The compatibility with the adjoint action uses `LieModule.toEnd_baseChange` from
`Mathlib/Algebra/Lie/BaseChange.lean`.

## Main results

* `LieSubmodule.baseChange_iSup`: extension of scalars preserves arbitrary suprema of Lie
  submodules.
* `LieSubmodule.baseChange_inj`: faithfully flat extension of scalars reflects equality of Lie
  submodules.
* `LieSubmodule.one_tmul_mem_baseChange_iff`: **membership in a Lie submodule may be checked after
  a faithfully flat extension of scalars.**
* `LieAlgebra.exists_eq_lie_of_one_tmul_mem_range_ad`: membership of `1 ⊗ₜ x` in the range of
  the extended adjoint endomorphism descends to an equation `x = ⁅x, y⁆`.
-/

public section

open TensorProduct
open scoped TensorProduct

universe u v w x

namespace LieSubmodule

variable {R : Type u} {A : Type v} {L : Type w} {M : Type x}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- Extension of scalars preserves arbitrary suprema of Lie submodules. -/
@[simp]
theorem baseChange_iSup {ι : Sort*} (N : ι → LieSubmodule R L M) :
    (⨆ i, N i).baseChange A = ⨆ i, (N i).baseChange A := by
  simp only [← toSubmodule_inj, coe_baseChange, iSup_toSubmodule]
  rw [Submodule.iSup_eq_span, Submodule.baseChange_span, Set.image_iUnion,
    Submodule.span_iUnion]
  simp only [Submodule.baseChange_eq_span, Submodule.map_coe]

/-- Faithfully flat extension of scalars reflects equality of Lie submodules. -/
@[simp]
theorem baseChange_inj [Module.FaithfullyFlat R A] (N P : LieSubmodule R L M) :
    N.baseChange A = P.baseChange A ↔ N = P := by
  rw [← toSubmodule_inj, coe_baseChange, coe_baseChange, Submodule.baseChange_inj,
    toSubmodule_inj]

/-- **Over a faithfully flat coefficient algebra, a vector lies in a Lie submodule exactly when
its canonical image lies in the extension of that submodule.** -/
@[simp]
theorem one_tmul_mem_baseChange_iff [Module.FaithfullyFlat R A] (N : LieSubmodule R L M) (m : M) :
    (1 : A) ⊗ₜ[R] m ∈ N.baseChange A ↔ m ∈ N := by
  rw [← mem_toSubmodule, coe_baseChange, Submodule.one_tmul_mem_baseChange_iff, mem_toSubmodule]

end LieSubmodule

namespace LieAlgebra

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
