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
* `LieEquiv.ofSubalgebrasRestrictScalars`: restricting a Lie equivalence onto a subalgebra and a
  scalar-restricted subalgebra.
* `LieEquiv.coe_ofSubalgebrasRestrictScalars_apply`: underlying value of that restriction.

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

end LieSubalgebra

namespace LieEquiv

/-- Restrict an `R`-Lie equivalence `e : L₁ ≃ₗ⁅R⁆ L₂` to an `R`-Lie subalgebra `H` of `L₁` and a
scalar-restricted `A`-Lie subalgebra `RestrictScalars R A K` of `L₂`, whenever `e` maps `H` onto
`(K.restrictScalarsIncl R).range`. -/
noncomputable def ofSubalgebrasRestrictScalars
    {R A L₁ L₂ : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]
    [LieAlgebra A L₂] [IsScalarTower R A L₂]
    (e : L₁ ≃ₗ⁅R⁆ L₂) (H : LieSubalgebra R L₁) (K : LieSubalgebra A L₂)
    (hHK : H.map (e : L₁ →ₗ⁅R⁆ L₂) = (K.restrictScalarsIncl R).range) :
    H ≃ₗ⁅R⁆ RestrictScalars R A K :=
  (e.ofSubalgebras H (K.restrictScalarsIncl R).range hHK).trans
    (LieEquiv.ofInjective (K.restrictScalarsIncl R) (K.restrictScalarsIncl_injective R)).symm

/-- Evaluating `LieEquiv.ofSubalgebrasRestrictScalars` returns the underlying image under `e`. -/
@[simp]
theorem coe_ofSubalgebrasRestrictScalars_apply
    {R A L₁ L₂ : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]
    [LieAlgebra A L₂] [IsScalarTower R A L₂]
    (e : L₁ ≃ₗ⁅R⁆ L₂) (H : LieSubalgebra R L₁) (K : LieSubalgebra A L₂)
    (hHK : H.map (e : L₁ →ₗ⁅R⁆ L₂) = (K.restrictScalarsIncl R).range) (x : H) :
    (RestrictScalars.addEquiv R A K (e.ofSubalgebrasRestrictScalars H K hHK x) : L₂) = e x := by
  have h := congrArg Subtype.val
    ((LieEquiv.ofInjective (K.restrictScalarsIncl R)
      (K.restrictScalarsIncl_injective R)).apply_symm_apply
      (e.ofSubalgebras H (K.restrictScalarsIncl R).range hHK x))
  simpa only [LieEquiv.ofSubalgebrasRestrictScalars, LieEquiv.trans_apply,
    LieEquiv.ofInjective_apply, LieSubalgebra.restrictScalarsIncl_apply,
    LieEquiv.ofSubalgebras_apply] using h

end LieEquiv
