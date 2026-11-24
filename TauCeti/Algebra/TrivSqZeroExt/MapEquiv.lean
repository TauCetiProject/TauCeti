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
square-zero part. This file packages the case of a linear equivalence:
`TauCeti.TrivSqZeroExt.mapEquiv e` is an algebra equivalence with inverse `mapEquiv e.symm`, and
`e ↦ mapEquiv e` is a group homomorphism from the linear automorphisms of `M` to the algebra
automorphisms of `R ⊕ M`.

For the dual numbers `R[ε] = R ⊕ R` this homomorphism sends the multiplication by a unit `u`
to the automorphism `ε ↦ u • ε`; when `R` has no nonzero `a` with `a ^ 2 = 0` and `2 * a = 0`
(for instance when `R` is reduced or `2` is invertible) these are all the automorphisms of `R[ε]`
(`TauCeti.DualNumber.mapEquivMulEquiv`).

## Main definitions

* `TauCeti.TrivSqZeroExt.mapEquiv`: the algebra equivalence `R ⊕ M ≃ₐ[R] R ⊕ N` induced by a linear
  equivalence `M ≃ₗ[R] N`.
* `TauCeti.TrivSqZeroExt.mapEquivHom`: the group homomorphism `(M ≃ₗ[R] M) →* (R ⊕ M ≃ₐ[R] R ⊕ M)`.
-/

public section

@[inherit_doc] local notation "tsze" => TrivSqZeroExt

open TrivSqZeroExt

namespace TauCeti.TrivSqZeroExt

variable {R M N P : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
  [AddCommMonoid N] [Module R N] [Module Rᵐᵒᵖ N] [IsCentralScalar R N]
  [AddCommMonoid P] [Module R P] [Module Rᵐᵒᵖ P] [IsCentralScalar R P]

/-- The algebra equivalence `R ⊕ M ≃ₐ[R] R ⊕ N` induced by a linear equivalence `e : M ≃ₗ[R] N`:
it fixes `R` and applies `e` to the square-zero part. As a map it is `TrivSqZeroExt.map e`
(`TauCeti.TrivSqZeroExt.coe_mapEquiv`), and its inverse is `mapEquiv e.symm`
(`TauCeti.TrivSqZeroExt.mapEquiv_symm`). -/
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
  AlgEquiv.ext fun x ↦ TrivSqZeroExt.ext (by simp) (by simp)

theorem mapEquiv_injective : Function.Injective (mapEquiv : (M ≃ₗ[R] N) → _) := fun e e' h ↦
  LinearEquiv.ext fun m ↦ inr_injective (R := R) <| by
    simpa using congrArg (fun g ↦ g (inr m)) h

variable (R M) in
/-- The group homomorphism from the linear automorphisms of `M` to the algebra automorphisms of
`R ⊕ M`, sending `e` to `TauCeti.TrivSqZeroExt.mapEquiv e`. It is injective
(`TauCeti.TrivSqZeroExt.mapEquiv_injective`). -/
def mapEquivHom : (M ≃ₗ[R] M) →* (tsze R M ≃ₐ[R] tsze R M) where
  toFun := mapEquiv
  map_one' := mapEquiv_refl
  map_mul' e e' := mapEquiv_trans e' e

@[simp]
theorem coe_mapEquivHom : ⇑(mapEquivHom R M) = mapEquiv := (rfl)

end TauCeti.TrivSqZeroExt
