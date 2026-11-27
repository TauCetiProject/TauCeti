/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.GeneralLinearGroup.Unitization.Basic

/-!
# `K₁` of a direct sum of C⋆-algebras

For C⋆-algebras `A` and `B`, the projections and inclusions of the direct sum `A × B` induce
mutually inverse isomorphisms `K₁(A × B) ≃* K₁(A) × K₁(B)` of the nonunital `K₁`-groups
(`TauCeti.UnitizationKOne.prodEquiv`): `K₁` preserves finite direct sums.

The composite `K₁(A) → K₁(A × B) → K₁(A)` is the identity and `K₁(B) → K₁(A × B) → K₁(A)` is
induced by the zero star homomorphism, so trivial (`TauCeti.UnitizationKOne.map_zero_eq_one`).
The other composite rests on the decomposition of an invertible matrix `u` over `(A × B)⁺`: write
`u = s + n₁ + n₂`, with `s` its scalar part and `n₁`, `n₂` with entries in `A` and in `B`. Then
`e₁(u) = s + n₁` and `e₂(u) = s + n₂`, for `e₁(a, b) = (a, 0)` and `e₂(a, b) = (0, b)`, and since
`n₁ x n₂ = 0` for every scalar matrix `x`,

  `e₁(u) · s⁻¹ · e₂(u) = u`

(`TauCeti.units_map_starMap_mul_inv_mul`). The class of the invertible scalar matrix `s` is
trivial, because every `GLₙ(ℂ)` is connected, so `[u] = [e₁(u)] · [e₂(u)]` in `K₁`
(`TauCeti.UnitizationKOne.map_inl_comp_fst_mul_map_inr_comp_snd`).

## Main definitions

* `TauCeti.UnitizationKOne.prodEquiv`: `K₁(A × B) ≃* K₁(A) × K₁(B)`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, second edition, Mathematical Sciences Research
  Institute Publications 5, Cambridge University Press (1998), 8.1.5 and Corollary 8.3.7.
-/

public section

noncomputable section

namespace TauCeti

namespace UnitizationKOne

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **`K₁` is additive on direct sums**: for `x ∈ K₁(A × B)`, `x` is the product of the images of
`x` under the maps induced by `(a, b) ↦ (a, 0)` and `(a, b) ↦ (0, b)`. -/
theorem map_inl_comp_fst_mul_map_inr_comp_snd (x : UnitizationKOne ℂ (A × B)) :
    map ((NonUnitalStarAlgHom.inl ℂ A B).comp (NonUnitalStarAlgHom.fst ℂ A B)) x *
      map ((NonUnitalStarAlgHom.inr ℂ A B).comp (NonUnitalStarAlgHom.snd ℂ A B)) x = x := by
  apply Subtype.ext
  obtain ⟨n, u, hu⟩ :=
    StableComponentGroup.exists_mk (x : StableComponentGroup (Unitization ℂ (A × B)))
  have hs : StableComponentGroup.mk _ n
      (unitizationGLInl ℂ (A × B) (Fin n) (unitizationGLFst ℂ (A × B) (Fin n) u)) = 1 := by
    rw [← map_inlRingHom_mk, Subsingleton.elim (StableComponentGroup.mk ℂ n _) 1, map_one]
  rw [Subgroup.coe_mul, coe_map, coe_map, ← hu, StableComponentGroup.map_mk,
    StableComponentGroup.map_mk]
  conv_rhs => rw [← units_map_starMap_mul_inv_mul u]
  rw [map_mul, map_mul, map_inv, hs, inv_one, mul_one]

/-- **`K₁` of a direct sum**: the projections induce `K₁(A × B) ≃* K₁(A) × K₁(B)`, with inverse
`(x, y) ↦ inl_* x · inr_* y`. -/
def prodEquiv : UnitizationKOne ℂ (A × B) ≃* UnitizationKOne ℂ A × UnitizationKOne ℂ B where
  toFun x := (map (NonUnitalStarAlgHom.fst ℂ A B) x, map (NonUnitalStarAlgHom.snd ℂ A B) x)
  invFun y := map (NonUnitalStarAlgHom.inl ℂ A B) y.1 * map (NonUnitalStarAlgHom.inr ℂ A B) y.2
  left_inv x := by
    simp only [← MonoidHom.comp_apply, ← map_comp]
    exact map_inl_comp_fst_mul_map_inr_comp_snd x
  right_inv y := by
    have h₁ : (NonUnitalStarAlgHom.fst ℂ A B).comp (NonUnitalStarAlgHom.inl ℂ A B) =
        NonUnitalStarAlgHom.id ℂ A := by ext; rfl
    have h₂ : (NonUnitalStarAlgHom.fst ℂ A B).comp (NonUnitalStarAlgHom.inr ℂ A B) = 0 := by
      ext; rfl
    have h₃ : (NonUnitalStarAlgHom.snd ℂ A B).comp (NonUnitalStarAlgHom.inl ℂ A B) = 0 := by
      ext; rfl
    have h₄ : (NonUnitalStarAlgHom.snd ℂ A B).comp (NonUnitalStarAlgHom.inr ℂ A B) =
        NonUnitalStarAlgHom.id ℂ B := by ext; rfl
    simp only [map_mul, ← MonoidHom.comp_apply, ← map_comp, h₁, h₂, h₃, h₄, map_id,
      map_zero_eq_one, MonoidHom.id_apply, MonoidHom.one_apply, mul_one, one_mul]
  map_mul' x y := by simp

/-- The isomorphism `K₁(A × B) ≃* K₁(A) × K₁(B)` is induced by the two projections. -/
@[simp]
theorem prodEquiv_apply (x : UnitizationKOne ℂ (A × B)) :
    prodEquiv x =
      (map (NonUnitalStarAlgHom.fst ℂ A B) x, map (NonUnitalStarAlgHom.snd ℂ A B) x) :=
  (rfl)

/-- The inverse of `K₁(A × B) ≃* K₁(A) × K₁(B)` is `(x, y) ↦ inl_* x · inr_* y`. -/
@[simp]
theorem prodEquiv_symm_apply (y : UnitizationKOne ℂ A × UnitizationKOne ℂ B) :
    prodEquiv.symm y =
      map (NonUnitalStarAlgHom.inl ℂ A B) y.1 * map (NonUnitalStarAlgHom.inr ℂ A B) y.2 :=
  (rfl)

end UnitizationKOne

end TauCeti
