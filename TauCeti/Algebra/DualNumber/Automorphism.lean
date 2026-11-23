/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import TauCeti.Algebra.TrivSqZeroExt.MapEquiv

/-!
# Automorphisms of the dual numbers

Let `R` be a reduced commutative ring. An `R`-algebra endomorphism `f` of the dual numbers `R[ε]`
sends `ε` to an element squaring to zero; its `R`-component then squares to zero in `R`, so it
vanishes, and `f ε = b • ε` with `b = (f ε).snd`. For an automorphism the coefficient `b` is a
unit, because the inverse automorphism supplies an inverse coefficient. Since an algebra map out of
`R[ε]` is determined by its value on `ε`, the automorphisms of `R[ε]` are exactly the maps
`ε ↦ u • ε` for the units `u` of `R`, that is, the maps `TrivSqZeroExt.mapEquiv e` for the linear
automorphisms `e` of `R`: `DualNumber.mapEquivMulEquiv` is a group isomorphism
`(R ≃ₗ[R] R) ≃* (R[ε] ≃ₐ[R] R[ε])`.

The reducedness hypothesis cannot simply be dropped: over `R = 𝔽₂[δ]/(δ²)` the assignment
`ε ↦ δ + ε` defines an automorphism of `R[ε]`, since `(δ + ε)² = 2δε = 0`, and it does not
preserve the line `R • ε`.

## Main results

* `DualNumber.apply_eps_eq_snd_smul_eps`: over a reduced ring, an endomorphism `f` of `R[ε]`
  sends `ε` to `(f ε).snd • ε`.
* `DualNumber.isUnit_snd_apply_eps`: for an automorphism, this coefficient is a unit.
* `DualNumber.mapEquivMulEquiv`: the automorphism group of `R[ε]` is the group of linear
  automorphisms of `R`, acting on the coefficient of `ε`.
-/

public section

open TrivSqZeroExt

namespace DualNumber

variable {R : Type*} [CommRing R]

/-- Over a reduced ring, an endomorphism of the dual numbers sends `ε` to an element with zero
`R`-component. -/
theorem fst_apply_eps_eq_zero [IsReduced R] {F : Type*} [FunLike F R[ε] R[ε]]
    [AlgHomClass F R R[ε] R[ε]] (f : F) : (f ε).fst = 0 := by
  refine IsNilpotent.eq_zero ⟨2, ?_⟩
  rw [pow_two, ← fst_mul, ← map_mul, eps_mul_eps, map_zero, fst_zero]

/-- Over a reduced ring, an endomorphism of the dual numbers multiplies `ε` by the
`ε`-coefficient of its image. -/
theorem apply_eps_eq_snd_smul_eps [IsReduced R] {F : Type*} [FunLike F R[ε] R[ε]]
    [AlgHomClass F R R[ε] R[ε]] (f : F) : f ε = (f ε).snd • ε := by
  conv_lhs => rw [← inl_fst_add_inr_snd_eq (f ε)]
  rw [fst_apply_eps_eq_zero, inl_zero, zero_add, inr_eq_smul_eps]

/-- Over a reduced ring, an automorphism of the dual numbers multiplies `ε` by a unit. -/
theorem isUnit_snd_apply_eps [IsReduced R] (φ : R[ε] ≃ₐ[R] R[ε]) : IsUnit (φ ε).snd := by
  refine IsUnit.of_mul_eq_one (φ.symm ε).snd ?_
  -- Applying `φ` to `φ.symm ε = c • ε` gives `ε = c • φ ε = (c * b) • ε`.
  have h : (ε : R[ε]) = ((φ.symm ε).snd * (φ ε).snd) • ε := by
    conv_lhs => rw [← φ.apply_symm_apply ε, apply_eps_eq_snd_smul_eps φ.symm, map_smul,
      apply_eps_eq_snd_smul_eps φ, smul_smul]
  have h' := congrArg snd h
  rwa [snd_smul, snd_eps, smul_eq_mul, mul_one, eq_comm, mul_comm] at h'

/-- Over a reduced ring, every automorphism of the dual numbers is `TrivSqZeroExt.mapEquiv e` for
some linear automorphism `e` of `R`. -/
theorem exists_mapEquiv_eq [IsReduced R] (φ : R[ε] ≃ₐ[R] R[ε]) :
    ∃ e : R ≃ₗ[R] R, mapEquiv e = φ := by
  obtain ⟨u, hu⟩ := isUnit_snd_apply_eps φ
  refine ⟨LinearEquiv.smulOfUnit u, AlgEquiv.coe_toAlgHom_injective <| algHom_ext ?_⟩
  rw [AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom, apply_eps_eq_snd_smul_eps φ, ← hu,
    ← one_smul R (ε : R[ε]), ← inr_eq_smul_eps, coe_mapEquiv, map_inr, LinearEquiv.coe_coe,
    LinearEquiv.smulOfUnit, DistribMulAction.toLinearEquiv_apply, Units.smul_def, inr_smul]

variable (R) in
/-- **The automorphisms of the dual numbers.** Over a reduced commutative ring `R`, every
`R`-algebra automorphism of `R[ε]` is `TrivSqZeroExt.mapEquiv e` for a unique linear automorphism
`e` of `R`, namely the multiplication by the unit `(φ ε).snd`; composition corresponds to
composition. -/
noncomputable def mapEquivMulEquiv [IsReduced R] : (R ≃ₗ[R] R) ≃* (R[ε] ≃ₐ[R] R[ε]) :=
  MulEquiv.ofBijective (mapEquivHom R R) <| by
    rw [coe_mapEquivHom]
    exact ⟨mapEquiv_injective, exists_mapEquiv_eq⟩

@[simp]
theorem mapEquivMulEquiv_apply [IsReduced R] (e : R ≃ₗ[R] R) :
    mapEquivMulEquiv R e = mapEquiv e := by
  rw [mapEquivMulEquiv, MulEquiv.ofBijective_apply, coe_mapEquivHom]

/-- The linear automorphism of `R` attached to an automorphism `φ` of `R[ε]` is the multiplication
by the `ε`-coefficient of `φ ε`. -/
@[simp]
theorem mapEquivMulEquiv_symm_apply_apply [IsReduced R] (φ : R[ε] ≃ₐ[R] R[ε]) (r : R) :
    (mapEquivMulEquiv R).symm φ r = r * (φ ε).snd := by
  conv_rhs => rw [← (mapEquivMulEquiv R).apply_symm_apply φ, mapEquivMulEquiv_apply,
    ← one_smul R (ε : R[ε]), ← inr_eq_smul_eps, coe_mapEquiv, map_inr, snd_inr,
    LinearEquiv.coe_coe]
  rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

end DualNumber
