/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CompletelyBounded.Basic
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Algebra.Order.Star.Unitization
import TauCeti.Analysis.CStarAlgebra.CompletelyBounded.Isometry
import Mathlib.Analysis.CStarAlgebra.Unitization

/-!
# Completely bounded maps into commutative C⋆-algebras

A bounded linear map `u : A → B` from a C⋆-algebra into a commutative C⋆-algebra is completely
bounded, and its cb norm equals its norm: `‖u‖_cb = ‖u‖`. This extends the scalar case
`ContinuousLinearMap.cbNorm_toLinearMap`.

## Main declarations

* `ContinuousLinearMap.isCompletelyBounded_toLinearMap_of_comm`,
  `ContinuousLinearMap.cbNorm_toLinearMap_of_comm`: a bounded map into a commutative C⋆-algebra
  is completely bounded with `‖u‖_cb = ‖u‖`.

## Implementation notes

For a commutative unital target `B`, the Gelfand transform reduces the norm of
`⟪w, uₘ(x) v⟫ ∈ B` to its values under characters `χ`, and `χ ∘ u` is a bounded functional, whose
cb norm is its norm by `ContinuousLinearMap.cbNorm_toLinearMap`. A nonunital target embeds
isometrically in its unitization, which is commutative and unital.

## References

* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Chapter 3.
-/

public section

open scoped ComplexOrder InnerProductSpace
open WithCStarModule CStarModule

namespace ContinuousLinearMap

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The amplifications of a bounded map into a commutative unital C⋆-algebra are bounded by its
norm. -/
private theorem norm_map_le_opNorm_mul_of_unital {B : Type*} [CommCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] (u : A →L[ℂ] B) {κ : Type*} [Fintype κ]
    (x : CStarMatrix κ κ A) : ‖x.map (u : A →ₗ[ℂ] B)‖ ≤ ‖u‖ * ‖x‖ := by
  refine (CStarMatrix.norm_le_of_forall_inner_le (M := x.map (u : A →ₗ[ℂ] B))
    (C := ‖u‖₊ * ‖x‖₊) fun v w => ?_).trans_eq (by rw [NNReal.coe_mul, coe_nnNorm, coe_nnNorm])
  rw [← (AddMonoidHomClass.isometry_iff_norm _).mp (gelfandTransform_isometry B),
    ContinuousMap.norm_le _ (by positivity)]
  intro χ
  rw [WeakDual.gelfandTransform_apply_apply]
  let ψ : A →L[ℂ] ℂ := (WeakDual.toStrongDual (χ : WeakDual ℂ B)).comp u
  have hψ : ‖ψ‖ ≤ ‖u‖ := (opNorm_comp_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (WeakDual.CharacterSpace.norm_toStrongDual_le_one χ))
  have hvec (v : C⋆ᵐᵒᵈ(B, κ → B)) : ‖(equiv ℂ (κ → ℂ)).symm fun i => χ (v i)‖ ≤ ‖v‖ := by
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, pi_norm_sq,
      pi_norm_sq]
    simp only [equiv_symm_pi_apply, inner_def, ← map_star χ, ← map_mul, ← map_sum]
    exact NonUnitalAlgHom.norm_apply_le_self χ _
  have key : χ ⟪w, CStarMatrix.toCLM (x.map (u : A →ₗ[ℂ] B)) v⟫_B =
      ⟪(equiv ℂ (κ → ℂ)).symm fun i => χ (w i),
        CStarMatrix.toCLM (x.map (ψ : A →ₗ[ℂ] ℂ)) ((equiv ℂ (κ → ℂ)).symm fun i => χ (v i))⟫_ℂ := by
    simp [pi_inner, CStarMatrix.toCLM_apply_eq_sum, inner_def, map_sum, map_mul, map_star, ψ]
  rw [key]
  refine (norm_inner_le _).trans ?_
  calc _ ≤ ‖w‖ * (‖x.map (ψ : A →ₗ[ℂ] ℂ)‖ * ‖v‖) := by
        gcongr
        · exact hvec w
        · exact ((CStarMatrix.toCLM (x.map (ψ : A →ₗ[ℂ] ℂ))).le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (hvec v) (norm_nonneg _))
    _ ≤ ‖w‖ * ((‖u‖ * ‖x‖) * ‖v‖) := by
        gcongr
        refine (LinearMap.norm_map_le_cbNorm_mul (isCompletelyBounded_toLinearMap ψ) x).trans ?_
        rw [cbNorm_toLinearMap]
        gcongr
    _ = _ := by rw [NNReal.coe_mul, coe_nnNorm, coe_nnNorm]; ring

variable {B : Type*} [NonUnitalCommCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- The amplifications of a bounded map into a commutative C⋆-algebra are bounded by its norm:
compose with the isometric inclusion into the unitization. -/
private theorem norm_map_le_opNorm_mul_of_comm (u : A →L[ℂ] B) {κ : Type*} [Fintype κ]
    (x : CStarMatrix κ κ A) : ‖x.map (u : A →ₗ[ℂ] B)‖ ≤ ‖u‖ * ‖x‖ := by
  let ι := Unitization.inrNonUnitalStarAlgHom ℂ B
  have hbound (a : A) : ‖((ι : B →ₗ[ℂ] Unitization ℂ B) ∘ₗ u) a‖ ≤ ‖u‖ * ‖a‖ := by
    simpa [ι, Unitization.norm_inr] using u.le_opNorm a
  have hι := NonUnitalStarAlgHom.isCompleteIsometry ι Unitization.inr_injective
  rw [← hι.norm_map (x.map (u : A →ₗ[ℂ] B)), CStarMatrix.map_map, ← LinearMap.coe_comp,
    ← LinearMap.mkContinuous_coe _ _ hbound]
  exact (norm_map_le_opNorm_mul_of_unital (LinearMap.mkContinuous _ _ hbound) x).trans (by
    gcongr
    exact LinearMap.mkContinuous_norm_le _ (norm_nonneg u) _)

/-- A bounded linear map into a commutative C⋆-algebra is completely bounded. -/
theorem isCompletelyBounded_toLinearMap_of_comm (u : A →L[ℂ] B) :
    (u : A →ₗ[ℂ] B).IsCompletelyBounded :=
  LinearMap.isCompletelyBounded_iff_exists_bound.mpr
    ⟨‖u‖, fun _ x => norm_map_le_opNorm_mul_of_comm u x⟩

/-- **A bounded linear map into a commutative C⋆-algebra has cb norm equal to its norm.** -/
theorem cbNorm_toLinearMap_of_comm (u : A →L[ℂ] B) : (u : A →ₗ[ℂ] B).cbNorm = ‖u‖ :=
  le_antisymm
    (LinearMap.cbNorm_le_of_bound (norm_nonneg u) fun _ x => norm_map_le_opNorm_mul_of_comm u x) <|
    u.opNorm_le_bound (LinearMap.cbNorm_nonneg _) fun a =>
      LinearMap.norm_apply_le_cbNorm_mul (isCompletelyBounded_toLinearMap_of_comm u) a

end ContinuousLinearMap
