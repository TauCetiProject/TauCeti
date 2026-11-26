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
(`TauCeti.UnitizationKOne.prodEquiv`), the finite direct sums of OperatorKTheory K2.2.

The composite `K₁(A) → K₁(A × B) → K₁(A)` is the identity and `K₁(B) → K₁(A × B) → K₁(A)` is
induced by the zero star homomorphism, so trivial (`TauCeti.UnitizationKOne.map_zero_eq_one`).
The other composite rests on the decomposition of an invertible matrix `u` over `(A × B)⁺`: write
`u = s + n₁ + n₂`, with `s` its scalar part and `n₁`, `n₂` with entries in `A` and in `B`. Then
`e₁(u) = s + n₁` and `e₂(u) = s + n₂`, for `e₁(a, b) = (a, 0)` and `e₂(a, b) = (0, b)`, and since
`n₁ x n₂ = 0` for every scalar matrix `x`,

  `e₁(u) · s⁻¹ · e₂(u) = u`

(`TauCeti.UnitizationKOne.units_map_starMap_mul_inv_mul`). The class of the invertible scalar
matrix `s` is trivial, because every `GLₙ(ℂ)` is connected, so `[u] = [e₁(u)] · [e₂(u)]` in `K₁`
(`TauCeti.UnitizationKOne.map_inl_comp_fst_mul_map_inr_comp_snd`).

## Main definitions

* `TauCeti.UnitizationKOne.prodEquiv`: `K₁(A × B) ≃* K₁(A) × K₁(B)`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, second edition, Mathematical Sciences Research
  Institute Publications 5, Cambridge University Press (1998), 8.1.5 and Corollary 8.3.7.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

namespace UnitizationKOne

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Decomposition of an invertible matrix over `(A × B)⁺`.** With `e₁(a, b) = (a, 0)`,
`e₂(a, b) = (0, b)` and `s` the scalar part of `u`, `e₁(u) · s⁻¹ · e₂(u) = u`. -/
theorem units_map_starMap_mul_inv_mul {n : Type*} [Fintype n] [DecidableEq n]
    (u : GL n (Unitization ℂ (A × B))) :
    Units.map ((Unitization.starMap ((NonUnitalStarAlgHom.inl ℂ A B).comp
        (NonUnitalStarAlgHom.fst ℂ A B)) : Unitization ℂ (A × B) →+* Unitization ℂ (A × B)
          ).mapMatrix (m := n)).toMonoidHom u *
      (unitizationGLInl ℂ (A × B) n (unitizationGLFst ℂ (A × B) n u))⁻¹ *
      Units.map ((Unitization.starMap ((NonUnitalStarAlgHom.inr ℂ A B).comp
        (NonUnitalStarAlgHom.snd ℂ A B)) : Unitization ℂ (A × B) →+* Unitization ℂ (A × B)
          ).mapMatrix (m := n)).toMonoidHom u = u := by
  -- The scalar part `σ`, and the parts `N₁`, `N₂` of `u` with entries in `A` and in `B`.
  let σ : Unitization ℂ (A × B) →+* Unitization ℂ (A × B) :=
    (Unitization.inlRingHom ℂ (A × B)).comp (Unitization.fstHom ℂ (A × B) : _ →+* ℂ)
  let M : Matrix n n (Unitization ℂ (A × B)) := u
  let M' : Matrix n n (Unitization ℂ (A × B)) := (u⁻¹ : GL n _)
  let N₁ : Matrix n n (Unitization ℂ (A × B)) := M.map fun x ↦ (((x.snd.1, 0) : A × B) : _)
  let N₂ : Matrix n n (Unitization ℂ (A × B)) := M.map fun x ↦ (((0, x.snd.2) : A × B) : _)
  have hσ : M'.map σ * M.map σ = 1 := by
    rw [← Matrix.map_mul, show M' * M = 1 from Units.inv_mul u]
    exact Matrix.map_one _ (map_zero σ) (map_one σ)
  have hσ' : M.map σ * M'.map σ = 1 := by
    rw [← Matrix.map_mul, show M * M' = 1 from Units.mul_inv u]
    exact Matrix.map_one _ (map_zero σ) (map_one σ)
  have hN : N₁ * M'.map σ * N₂ = 0 := by
    refine Matrix.ext fun i j ↦ ?_
    simp only [Matrix.mul_apply, Finset.sum_mul, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ ↦ Finset.sum_eq_zero fun l _ ↦ ?_
    simp only [N₁, N₂, σ, Matrix.map_apply, RingHom.comp_apply, Unitization.inlRingHom_apply,
      Unitization.inr_mul_inl, ← Unitization.inr_mul]
    simp [Prod.mk_zero_zero]
  have hM : M = M.map σ + N₁ + N₂ := by
    ext i j <;> simp [σ, N₁, N₂]
  refine Units.ext ?_
  simp only [Units.val_mul, Units.coe_map, unitizationGLInl_def, unitizationGLFst_def,
    Units.coe_map_inv]
  have h₁ : M.map (Unitization.starMap ((NonUnitalStarAlgHom.inl ℂ A B).comp
      (NonUnitalStarAlgHom.fst ℂ A B)) : Unitization ℂ (A × B) →+* Unitization ℂ (A × B)) =
        M.map σ + N₁ := by
    ext i j <;> simp [σ, N₁]
  have h₂ : M.map (Unitization.starMap ((NonUnitalStarAlgHom.inr ℂ A B).comp
      (NonUnitalStarAlgHom.snd ℂ A B)) : Unitization ℂ (A × B) →+* Unitization ℂ (A × B)) =
        M.map σ + N₂ := by
    ext i j <;> simp [σ, N₂]
  have h₃ : ((M'.map (Unitization.fstHom ℂ (A × B) : _ →+* ℂ)).map
      (Unitization.inlRingHom ℂ (A × B))) = M'.map σ := by
    rw [Matrix.map_map]
    rfl
  change M.map _ * ((M'.map _).map _) * M.map _ = M
  rw [h₁, h₂, h₃]
  calc (M.map σ + N₁) * M'.map σ * (M.map σ + N₂)
      = M.map σ * M'.map σ * M.map σ + M.map σ * M'.map σ * N₂ + N₁ * M'.map σ * M.map σ +
          N₁ * M'.map σ * N₂ := by
        simp only [add_mul, mul_add]
        abel
    _ = M.map σ + N₁ + N₂ := by
        rw [hσ', hN, Matrix.mul_assoc N₁, hσ, one_mul, one_mul, Matrix.mul_one, add_zero]
        abel
    _ = M := hM.symm

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
