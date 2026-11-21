/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian

/-!
# Restrictions of Lie algebra equivalences to the centre

Every Lie algebra equivalence `e : L ≃ₗ⁅R⁆ M` carries the centre `Z(L)` onto `Z(M)`
(`LieEquiv.map_center`), inducing a Lie algebra equivalence `LieEquiv.restrictCenter` between the
centres that respects inverses and composition.

## Main definitions

* `LieEquiv.restrictCenter`: restriction of a Lie algebra equivalence to the centre.

## Main results

* `LieEquiv.map_center`: every Lie algebra equivalence maps the centre onto the centre.
* `LieEquiv.restrictCenter_symm` and `LieEquiv.restrictCenter_trans`: compatibility of
  `LieEquiv.restrictCenter` with inverses and composition.
-/

public section

open LieAlgebra

namespace LieEquiv

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

/-- Every Lie algebra equivalence maps the centre onto the centre. -/
theorem map_center (e : L ≃ₗ⁅R⁆ M) :
    (center R L).toLieSubalgebra.map e.toLieHom = (center R M).toLieSubalgebra := by
  ext y
  rw [LieSubalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [LieIdeal.mem_toLieSubalgebra, LieModule.mem_maxTrivSubmodule]
    intro w
    obtain ⟨u, rfl⟩ := e.surjective w
    rw [coe_toLieHom, ← e.map_lie, (LieModule.mem_maxTrivSubmodule R L L x).mp hx u, map_zero]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [LieIdeal.mem_toLieSubalgebra, LieModule.mem_maxTrivSubmodule]
    intro u
    apply e.injective
    rw [e.toLieHom.map_lie, map_zero, coe_toLieHom, e.apply_symm_apply]
    exact (LieModule.mem_maxTrivSubmodule R M M y).mp hy (e u)

/-- Restriction of a Lie algebra equivalence to the centre. -/
def restrictCenter (e : L ≃ₗ⁅R⁆ M) : center R L ≃ₗ⁅R⁆ center R M :=
  e.ofSubalgebras (center R L).toLieSubalgebra (center R M).toLieSubalgebra e.map_center

@[simp, grind =]
theorem coe_restrictCenter (e : L ≃ₗ⁅R⁆ M) (z : center R L) :
    (e.restrictCenter z : M) = e z :=
  e.ofSubalgebras_apply _ _ e.map_center z

@[simp, grind =]
theorem coe_restrictCenter_symm (e : L ≃ₗ⁅R⁆ M) (z : center R M) :
    (e.restrictCenter.symm z : L) = e.symm z :=
  e.ofSubalgebras_symm_apply _ _ e.map_center z

/-- Restricting the inverse equivalence to the centre equals the inverse of the restriction. -/
@[simp]
theorem restrictCenter_symm (e : L ≃ₗ⁅R⁆ M) :
    e.symm.restrictCenter = e.restrictCenter.symm := by
  ext z
  simp

/-- Restricting a composite equivalence to the centre composes the restrictions. -/
theorem restrictCenter_trans {N : Type*} [LieRing N] [LieAlgebra R N]
    (e₁ : L ≃ₗ⁅R⁆ M) (e₂ : M ≃ₗ⁅R⁆ N) :
    (e₁.trans e₂).restrictCenter = e₁.restrictCenter.trans e₂.restrictCenter := by
  ext z
  simp

end LieEquiv
