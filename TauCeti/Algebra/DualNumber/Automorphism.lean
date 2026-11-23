/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Nilpotent.Defs
public import TauCeti.Algebra.TrivSqZeroExt.MapEquiv

/-!
# Automorphisms of the dual numbers

Let `R` be a commutative semiring. An `R`-algebra endomorphism `f` of the dual numbers `R[ε]`
sends `ε` to an element `a + b • ε` squaring to zero, that is, with `a ^ 2 = 0` and `2 * a * b = 0`.
For an automorphism `φ` the coefficient `b` is a unit over every `R`, because applying `φ` to
`φ.symm ε` supplies an inverse coefficient; so `a ^ 2 = 0` and `2 * a = 0`. When `R` has no
nonzero such `a` — for instance when `R` is reduced, or when `2` is invertible in `R` — this
forces `a = 0`, and `φ ε = b • ε`. Since an algebra map out of `R[ε]` is determined by its value
on `ε`, the automorphisms of `R[ε]` are then exactly the maps `ε ↦ u • ε` for the units `u` of `R`,
that is, the maps `TauCeti.TrivSqZeroExt.mapEquiv e` for the linear automorphisms `e` of `R`:
`TauCeti.DualNumber.mapEquivMulEquiv` is a group isomorphism `(R ≃ₗ[R] R) ≃* (R[ε] ≃ₐ[R] R[ε])`.

The hypothesis is also necessary: if `a ≠ 0` satisfies `a ^ 2 = 0` and `2 * a = 0`, then
`ε ↦ a + ε` defines an automorphism of `R[ε]` (with inverse `ε ↦ -a + ε` when `R` is a ring, since
`(a + ε) ^ 2 = a ^ 2 + 2 * a • ε = 0`) that does not preserve the line `R • ε`. For instance,
`a = δ` over `R = 𝔽₂[δ]/(δ²)`.

## Main results

* `TauCeti.DualNumber.map_eps`: `TrivSqZeroExt.map f` sends `ε` to `f 1 • ε`.
* `TauCeti.DualNumber.apply_eps_eq_snd_smul_eps`: over a reduced semiring, an endomorphism `f` of
  `R[ε]` sends `ε` to `(f ε).snd • ε`.
* `TauCeti.DualNumber.isUnit_snd_apply_eps`: for an automorphism, the coefficient of `ε` in the
  image of `ε` is a unit.
* `TauCeti.DualNumber.mapEquivMulEquiv`: the automorphism group of `R[ε]` is the group of linear
  automorphisms of `R`, acting on the coefficient of `ε`.
-/

public section

open DualNumber TrivSqZeroExt

namespace TauCeti.DualNumber

variable {R : Type*} [CommSemiring R]

/-- `TrivSqZeroExt.map f` multiplies `ε` by `f 1`. -/
@[simp]
theorem map_eps (f : R →ₗ[R] R) : map f ε = f 1 • ε :=
  (map_inr f 1).trans (inr_eq_smul_eps _)

/-- Over a reduced semiring, an endomorphism of the dual numbers sends `ε` to an element with zero
`R`-component. -/
@[simp]
theorem fst_apply_eps_eq_zero [IsReduced R] {F : Type*} [FunLike F R[ε] R[ε]]
    [AlgHomClass F R R[ε] R[ε]] (f : F) : (f ε).fst = 0 :=
  ((IsNilpotent.map ⟨2, by rw [pow_two, eps_mul_eps]⟩ f).map (fstHom R R R)).eq_zero

/-- Over a reduced semiring, an endomorphism of the dual numbers multiplies `ε` by the
`ε`-coefficient of its image. -/
theorem apply_eps_eq_snd_smul_eps [IsReduced R] {F : Type*} [FunLike F R[ε] R[ε]]
    [AlgHomClass F R R[ε] R[ε]] (f : F) : f ε = (f ε).snd • ε := by
  conv_lhs => rw [← inl_fst_add_inr_snd_eq (f ε)]
  rw [fst_apply_eps_eq_zero, inl_zero, zero_add, inr_eq_smul_eps]

/-- An automorphism of the dual numbers multiplies `ε`, up to an `R`-component, by a unit. -/
theorem isUnit_snd_apply_eps (φ : R[ε] ≃ₐ[R] R[ε]) : IsUnit (φ ε).snd := by
  refine IsUnit.of_mul_eq_one (φ.symm ε).snd ?_
  -- Applying `φ` to `φ.symm ε = c + d • ε` gives `ε = c + d • φ ε`; compare `ε`-coefficients.
  have h := congrArg snd (φ.apply_symm_apply ε)
  rwa [← inl_fst_add_inr_snd_eq (φ.symm ε), inr_eq_smul_eps, map_add, map_smul,
    ← algebraMap_eq_inl, AlgEquiv.commutes, snd_add, snd_smul, algebraMap_eq_inl, snd_inl,
    zero_add, snd_eps, smul_eq_mul, mul_comm] at h

/-- If `R` has no nonzero `a` with `a ^ 2 = 0` and `2 * a = 0`, for instance if `R` is reduced or
`2` is invertible in `R`, then an automorphism of the dual numbers sends `ε` to an element with
zero `R`-component. -/
theorem fst_algEquiv_apply_eps_eq_zero (hR : ∀ a : R, a ^ 2 = 0 → 2 * a = 0 → a = 0)
    (φ : R[ε] ≃ₐ[R] R[ε]) : (φ ε).fst = 0 := by
  -- Write `φ ε = a + b • ε`; then `(φ ε) ^ 2 = 0` gives `a ^ 2 = 0` and `2 * a * b = 0`.
  have h : φ ε * φ ε = 0 := by rw [← map_mul, eps_mul_eps, map_zero]
  refine hR _ ?_ ((isUnit_snd_apply_eps φ).mul_left_eq_zero.mp ?_)
  · rw [pow_two, ← fst_mul, h, fst_zero]
  · have h' := congrArg snd h
    rwa [DualNumber.snd_mul, snd_zero, mul_comm (φ ε).snd, ← two_mul, ← mul_assoc] at h'

/-- If `R` has no nonzero `a` with `a ^ 2 = 0` and `2 * a = 0`, for instance if `R` is reduced or
`2` is invertible in `R`, then every automorphism of the dual numbers is
`TauCeti.TrivSqZeroExt.mapEquiv e` for some linear automorphism `e` of `R`. -/
theorem exists_mapEquiv_eq (hR : ∀ a : R, a ^ 2 = 0 → 2 * a = 0 → a = 0)
    (φ : R[ε] ≃ₐ[R] R[ε]) : ∃ e : R ≃ₗ[R] R, TrivSqZeroExt.mapEquiv e = φ := by
  obtain ⟨u, hu⟩ := isUnit_snd_apply_eps φ
  refine ⟨LinearEquiv.smulOfUnit u, AlgEquiv.coe_toAlgHom_injective <| DualNumber.algHom_ext ?_⟩
  ext
  · simp [fst_algEquiv_apply_eps_eq_zero hR]
  · simp [← hu, LinearEquiv.smulOfUnit, Units.smul_def]

/-- **The automorphisms of the dual numbers.** If `R` has no nonzero `a` with `a ^ 2 = 0` and
`2 * a = 0`, for instance if `R` is reduced or `2` is invertible in `R`, then every `R`-algebra
automorphism `φ` of `R[ε]` is `TauCeti.TrivSqZeroExt.mapEquiv e` for a unique linear automorphism
`e` of `R`, namely the multiplication by the unit `(φ ε).snd`; composition corresponds to
composition. -/
noncomputable def mapEquivMulEquiv (hR : ∀ a : R, a ^ 2 = 0 → 2 * a = 0 → a = 0) :
    (R ≃ₗ[R] R) ≃* (R[ε] ≃ₐ[R] R[ε]) :=
  MulEquiv.ofBijective (TrivSqZeroExt.mapEquivHom R R) <| by
    rw [TrivSqZeroExt.coe_mapEquivHom]
    exact ⟨TrivSqZeroExt.mapEquiv_injective, exists_mapEquiv_eq hR⟩

@[simp]
theorem mapEquivMulEquiv_apply (hR : ∀ a : R, a ^ 2 = 0 → 2 * a = 0 → a = 0) (e : R ≃ₗ[R] R) :
    mapEquivMulEquiv hR e = TrivSqZeroExt.mapEquiv e := by
  rw [mapEquivMulEquiv, MulEquiv.ofBijective_apply, TrivSqZeroExt.coe_mapEquivHom]

/-- The linear automorphism of `R` attached to an automorphism `φ` of `R[ε]` is the multiplication
by the `ε`-coefficient of `φ ε`. -/
@[simp]
theorem mapEquivMulEquiv_symm_apply_apply (hR : ∀ a : R, a ^ 2 = 0 → 2 * a = 0 → a = 0)
    (φ : R[ε] ≃ₐ[R] R[ε]) (r : R) : (mapEquivMulEquiv hR).symm φ r = r * (φ ε).snd := by
  conv_rhs => rw [← (mapEquivMulEquiv hR).apply_symm_apply φ, mapEquivMulEquiv_apply,
    TrivSqZeroExt.coe_mapEquiv, map_eps, snd_smul, snd_eps, smul_eq_mul, mul_one,
    LinearEquiv.coe_coe]
  rw [← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

end TauCeti.DualNumber
