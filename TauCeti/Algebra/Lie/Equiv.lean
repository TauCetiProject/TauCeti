/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian

/-!
# Lie algebra equivalences on centres

Every Lie algebra equivalence `e : L ≃ₗ⁅R⁆ M` carries `Z(L)` onto `Z(M)`
(`LieEquiv.map_center_toLieSubalgebra`), inducing
`LieEquiv.restrictCenter : center R L ≃ₗ⁅R⁆ center R M`.

## Main definitions and results

* `LieEquiv.map_center_toLieSubalgebra`, `LieEquiv.restrictCenter`, `LieEquiv.restrictCenter_refl`,
  `LieEquiv.restrictCenter_symm`, `LieEquiv.restrictCenter_trans`.
-/

public section

open LieAlgebra

namespace LieEquiv

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

/-- Every Lie algebra equivalence maps the centre onto the centre as Lie subalgebras. -/
theorem map_center_toLieSubalgebra (e : L ≃ₗ⁅R⁆ M) :
    (center R L).toLieSubalgebra.map e.toLieHom = (center R M).toLieSubalgebra := by
  ext y
  simp only [LieSubalgebra.mem_map, LieIdeal.mem_toLieSubalgebra, LieModule.mem_maxTrivSubmodule]
  refine ⟨?_, fun hy ↦ ⟨e.symm y, fun u ↦ e.injective ?_, e.apply_symm_apply y⟩⟩
  · rintro ⟨x, hx, rfl⟩ w
    obtain ⟨u, rfl⟩ := e.surjective w
    rw [coe_toLieHom, ← e.map_lie, hx u, map_zero]
  · rw [e.toLieHom.map_lie, map_zero, coe_toLieHom, e.apply_symm_apply]; exact hy (e u)

/-- Restriction of a Lie algebra equivalence to the centre. -/
def restrictCenter (e : L ≃ₗ⁅R⁆ M) : center R L ≃ₗ⁅R⁆ center R M :=
  e.ofSubalgebras (center R L).toLieSubalgebra (center R M).toLieSubalgebra
    e.map_center_toLieSubalgebra

@[simp, grind =]
theorem coe_restrictCenter (e : L ≃ₗ⁅R⁆ M) (z : center R L) : (e.restrictCenter z : M) = e z :=
  e.ofSubalgebras_apply _ _ e.map_center_toLieSubalgebra z

@[simp, grind =]
theorem coe_restrictCenter_symm (e : L ≃ₗ⁅R⁆ M) (z : center R M) :
    (e.restrictCenter.symm z : L) = e.symm z :=
  e.ofSubalgebras_symm_apply _ _ e.map_center_toLieSubalgebra z

/-- Restricting the identity equivalence to the centre gives the identity equivalence. -/
@[simp]
theorem restrictCenter_refl : (LieEquiv.refl : L ≃ₗ⁅R⁆ L).restrictCenter = LieEquiv.refl := by
  ext z; simp

/-- Restricting the inverse equivalence to the centre equals the inverse of the restriction. -/
@[simp]
theorem restrictCenter_symm (e : L ≃ₗ⁅R⁆ M) :
    e.symm.restrictCenter = e.restrictCenter.symm := by
  ext z; simp

/-- Restricting a composite equivalence to the centre composes the restrictions. -/
@[simp]
theorem restrictCenter_trans {N : Type*} [LieRing N] [LieAlgebra R N]
    (e₁ : L ≃ₗ⁅R⁆ M) (e₂ : M ≃ₗ⁅R⁆ N) :
    (e₁.trans e₂).restrictCenter = e₁.restrictCenter.trans e₂.restrictCenter := by
  ext z; simp

end LieEquiv
