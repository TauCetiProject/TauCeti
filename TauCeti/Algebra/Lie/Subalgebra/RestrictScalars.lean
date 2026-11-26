/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange

/-!
# Lie subalgebra inclusions after restricting scalars

A Lie subalgebra over an algebra `A` includes into its ambient Lie algebra over the smaller
scalar ring `R`. The domain uses `RestrictScalars`, so this inclusion can be composed with
Lie homomorphisms defined on the underlying `R`-Lie algebra.

## Main results

* `LieSubalgebra.restrictScalarsIncl`: inclusion over the smaller scalar ring.
* `LieSubalgebra.restrictScalarsIncl_apply`: its underlying inclusion formula.
* `LieSubalgebra.restrictScalarsIncl_injective`: the inclusion is injective.
* `LieSubalgebra.mem_range_restrictScalarsIncl`: its range has the original carrier.
* `LieSubalgebra.center_range_restrictScalarsIncl_eq_bot`: a Lie subalgebra with trivial centre
  still has trivial centre after restricting scalars, for instance from `ℂ` to `ℝ`.

## References

* `Mathlib.Algebra.Lie.BaseChange`, for scalar restriction of Lie algebras.
* `Mathlib.Algebra.Lie.Subalgebra`, for inclusions and ranges of Lie homomorphisms.
-/

public section

namespace LieSubalgebra

variable {A L : Type*} [CommRing A] [LieRing L] [LieAlgebra A L]
  (K : LieSubalgebra A L) (R : Type*) [CommRing R] [Algebra R A]
  [LieAlgebra R L] [IsScalarTower R A L]

/-- The inclusion of a Lie subalgebra, viewed as a Lie homomorphism over the smaller scalars. -/
def restrictScalarsIncl : RestrictScalars R A K →ₗ⁅R⁆ L where
  toFun x := K.incl (RestrictScalars.addEquiv R A K x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' r x := by
    rw [RestrictScalars.addEquiv_map_smul, map_smul, algebraMap_smul, RingHom.id_apply]
  map_lie' {x y} := K.incl.map_lie x y

/-- Scalar restriction preserves the underlying inclusion into the ambient Lie algebra. -/
@[simp]
theorem restrictScalarsIncl_apply (x : RestrictScalars R A K) :
    K.restrictScalarsIncl R x = (RestrictScalars.addEquiv R A K x : L) := by
  rfl

/-- The inclusion over the smaller scalar ring is injective. -/
theorem restrictScalarsIncl_injective : Function.Injective (K.restrictScalarsIncl R) := by
  intro x y h
  apply (RestrictScalars.addEquiv R A K).injective
  apply Subtype.ext
  simpa only [restrictScalarsIncl_apply] using h

/-- The range of the scalar-restricted inclusion is the original Lie subalgebra carrier. -/
-- Normalize the whole range-membership predicate before `LieHom.mem_range` expands it.
@[simp↓]
theorem mem_range_restrictScalarsIncl (x : L) :
    x ∈ (K.restrictScalarsIncl R).range ↔ x ∈ K := by
  rw [LieHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    rw [restrictScalarsIncl_apply]
    exact (RestrictScalars.addEquiv R A K y).property
  · intro hx
    refine ⟨(RestrictScalars.addEquiv R A K).symm ⟨x, hx⟩, ?_⟩
    simp only [restrictScalarsIncl_apply, AddEquiv.apply_symm_apply]

open LieAlgebra in
/-- A Lie subalgebra with trivial centre over `A` still has trivial centre over a smaller scalar
ring `R`: the brackets over `R` and over `A` agree. -/
theorem center_range_restrictScalarsIncl_eq_bot (hK : center A K = ⊥) :
    center R (K.restrictScalarsIncl R).range = ⊥ := by
  refine (LieSubmodule.eq_bot_iff _).mpr fun ⟨Z, hZ⟩ hZc ↦ Subtype.ext ?_
  rw [LieModule.mem_maxTrivSubmodule] at hZc
  have hZK : Z ∈ K := (mem_range_restrictScalarsIncl K R Z).mp hZ
  have hcK : (⟨Z, hZK⟩ : K) ∈ center A K := by
    rw [LieModule.mem_maxTrivSubmodule]
    rintro ⟨X, hX⟩
    have := congrArg Subtype.val
      (hZc ⟨X, (mem_range_restrictScalarsIncl K R X).mpr hX⟩)
    exact Subtype.ext (by simpa only [coe_bracket, ZeroMemClass.coe_zero] using this)
  rw [hK, LieSubmodule.mem_bot] at hcK
  simpa using congrArg Subtype.val hcK

end LieSubalgebra
