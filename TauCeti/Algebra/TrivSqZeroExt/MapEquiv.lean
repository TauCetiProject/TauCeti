/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Linear equivalences induce algebra equivalences of trivial square-zero extensions

Over a commutative semiring `R`, Mathlib's `TrivSqZeroExt.map` sends a linear map `f : M →ₗ[R] N`
to the algebra homomorphism `R ⊕ M →ₐ[R] R ⊕ N` that fixes `R` and applies `f` to the
square-zero part. This file packages the case of a linear equivalence: `TrivSqZeroExt.mapEquiv e`
is an algebra equivalence with inverse `mapEquiv e.symm`, and `e ↦ mapEquiv e` is a group
homomorphism from the linear automorphisms of `M` to the algebra automorphisms of `R ⊕ M`.

For the dual numbers `R[ε] = R ⊕ R` this homomorphism sends the multiplication by a unit `u`
to the automorphism `ε ↦ u • ε`; over a reduced ring these are all the automorphisms of `R[ε]`
(`DualNumber.mapEquivMulEquiv`).

## Main definitions

* `TrivSqZeroExt.mapEquiv`: the algebra equivalence `R ⊕ M ≃ₐ[R] R ⊕ N` induced by a linear
  equivalence `M ≃ₗ[R] N`.
* `TrivSqZeroExt.mapEquivHom`: the group homomorphism `(M ≃ₗ[R] M) →* (R ⊕ M ≃ₐ[R] R ⊕ M)`.
-/

public section

@[inherit_doc] local notation "tsze" => TrivSqZeroExt

namespace TrivSqZeroExt

variable {R M N P : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
  [AddCommMonoid N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
  [AddCommMonoid P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]

/-- The algebra equivalence `R ⊕ M ≃ₐ[R] R ⊕ N` induced by a linear equivalence `e : M ≃ₗ[R] N`:
it fixes `R` and applies `e` to the square-zero part. As a map it is `TrivSqZeroExt.map e`
(`TrivSqZeroExt.coe_mapEquiv`), and its inverse is `mapEquiv e.symm`
(`TrivSqZeroExt.mapEquiv_symm`). -/
def mapEquiv (e : M ≃ₗ[R] N) : tsze R M ≃ₐ[R] tsze R N :=
  AlgEquiv.ofAlgHom (map e.toLinearMap) (map e.symm.toLinearMap)
    (by rw [← map_comp_map, LinearEquiv.comp_symm, map_id])
    (by rw [← map_comp_map, LinearEquiv.symm_comp, map_id])

@[simp]
theorem toAlgHom_mapEquiv (e : M ≃ₗ[R] N) :
    (mapEquiv e : tsze R M →ₐ[R] tsze R N) = map e.toLinearMap := by
  rw [mapEquiv, AlgEquiv.toAlgHom_ofAlgHom]

@[simp]
theorem coe_mapEquiv (e : M ≃ₗ[R] N) : ⇑(mapEquiv e) = map e.toLinearMap := by
  rw [← AlgEquiv.coe_toAlgHom, toAlgHom_mapEquiv]

@[simp]
theorem mapEquiv_symm (e : M ≃ₗ[R] N) : (mapEquiv e).symm = mapEquiv e.symm := by
  rw [mapEquiv, mapEquiv, AlgEquiv.ofAlgHom_symm]
  simp_rw [LinearEquiv.symm_symm]

@[simp]
theorem mapEquiv_refl : mapEquiv (LinearEquiv.refl R M) = AlgEquiv.refl :=
  AlgEquiv.coe_toAlgHom_injective <| by
    rw [toAlgHom_mapEquiv, LinearEquiv.refl_toLinearMap, map_id, AlgEquiv.refl_toAlgHom]

@[simp]
theorem mapEquiv_trans (e : M ≃ₗ[R] N) (e' : N ≃ₗ[R] P) :
    mapEquiv (e.trans e') = (mapEquiv e).trans (mapEquiv e') :=
  AlgEquiv.ext fun x ↦ by
    rw [AlgEquiv.trans_apply, coe_mapEquiv, coe_mapEquiv, coe_mapEquiv, LinearEquiv.coe_trans,
      map_comp_map, AlgHom.comp_apply]

theorem mapEquiv_injective : Function.Injective (mapEquiv : (M ≃ₗ[R] N) → _) := fun e e' h ↦
  LinearEquiv.ext fun m ↦ inr_injective (R := R) <| by
    rw [← LinearEquiv.coe_coe, ← map_inr, ← coe_mapEquiv, h, coe_mapEquiv, map_inr,
      LinearEquiv.coe_coe]

variable (R M) in
/-- The group homomorphism from the linear automorphisms of `M` to the algebra automorphisms of
`R ⊕ M`, sending `e` to `TrivSqZeroExt.mapEquiv e`. It is injective
(`TrivSqZeroExt.mapEquiv_injective`). -/
def mapEquivHom : (M ≃ₗ[R] M) →* (tsze R M ≃ₐ[R] tsze R M) where
  toFun := mapEquiv
  map_one' := mapEquiv_refl
  map_mul' e e' := mapEquiv_trans e' e

@[simp]
theorem coe_mapEquivHom : ⇑(mapEquivHom R M) = mapEquiv := by
  rw [mapEquivHom, MonoidHom.coe_mk, OneHom.coe_mk]


end TrivSqZeroExt
