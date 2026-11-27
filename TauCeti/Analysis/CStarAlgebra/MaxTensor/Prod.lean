/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Map
import Mathlib.Algebra.Star.Orthogonal
import Mathlib.Analysis.CStarAlgebra.GelfandDuality

/-!
# The maximal C*-norm distributes over direct sums

For C*-algebras `A`, `A'` and `B`, an element `x` of `(A × A') ⊗[ℂ] B` has the components
`x₁ = (fst ⊗ id) x ∈ A ⊗[ℂ] B` and `x₂ = (snd ⊗ id) x ∈ A' ⊗[ℂ] B`, and its maximal norm is
`‖x‖_max = max ‖x₁‖_max ‖x₂‖_max` (`TauCeti.maxTensorNorm_prod`).

The inequality `≥` is functoriality (`TauCeti.maxTensorNorm_mapNonUnitalStarAlgHom_le`). For `≤`,
`x = (inl ⊗ id) x₁ + (inr ⊗ id) x₂` in `(A × A') ⊗[ℂ] B`, and the two summands are
star-orthogonal there, since `(a, 0) (0, a') = 0`
(`TauCeti.isStarOrtho_mapNonUnitalStarAlgHom_inl_inr`). The integrated form of a commuting pair
of `A × A'` and `B` keeps them star-orthogonal, so the norm of its value at `x` is the maximum of
the norms of the two summands, which are the values of the pulled-back commuting pairs of `A`
and `B` and of `A'` and `B` at `x₁` and `x₂`.

## Main declarations

* `TauCeti.isStarOrtho_mapNonUnitalStarAlgHom_inl_inr`: `(inl ⊗ id) y ⋆⟂ (inr ⊗ id) z`.
* `TauCeti.maxTensorNorm_prod`: `‖x‖_max = max ‖x₁‖_max ‖x₂‖_max`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.5–II.9.2.6 (functoriality of C*-tensor products).
-/

public section

noncomputable section

open TensorProduct Algebra.TensorProduct
open scoped StarRing

universe u v

namespace TauCeti

variable {A A' : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
  [NonUnitalCStarAlgebra B]

/-- The images of `A ⊗[ℂ] B` and `A' ⊗[ℂ] B` in `(A × A') ⊗[ℂ] B` are star-orthogonal. -/
theorem isStarOrtho_mapNonUnitalStarAlgHom_inl_inr (y : A ⊗[ℂ] B) (z : A' ⊗[ℂ] B) :
    mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inl ℂ A A') (NonUnitalStarAlgHom.id ℂ B) y ⋆⟂
      mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inr ℂ A A') (NonUnitalStarAlgHom.id ℂ B) z := by
  set f := mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inl ℂ A A') (NonUnitalStarAlgHom.id ℂ B)
  set g := mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inr ℂ A A') (NonUnitalStarAlgHom.id ℂ B)
  have h₁ (a : A) (a' : A') : (a, (0 : A')) * star ((0 : A), a') = 0 := Prod.ext (by simp) (by simp)
  have h₂ (a : A) (a' : A') : star ((0 : A), a') * (a, (0 : A')) = 0 := Prod.ext (by simp) (by simp)
  rw [isStarOrtho_iff]
  constructor
  · induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => rw [map_add, add_mul, h₁, h₂, add_zero]
    | tmul a b =>
      induction z using TensorProduct.inductionOn with
      | add z₁ z₂ h₁ h₂ => rw [map_add, star_add, mul_add, h₁, h₂, add_zero]
      | tmul a' b' => simp [f, g, TensorProduct.star_tmul, h₁]
  · induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => rw [map_add, mul_add, h₁, h₂, add_zero]
    | tmul a b =>
      induction z using TensorProduct.inductionOn with
      | add z₁ z₂ h₁ h₂ => rw [map_add, star_add, add_mul, h₁, h₂, add_zero]
      | tmul a' b' => simp [f, g, TensorProduct.star_tmul, h₂]

/-- Every `x ∈ (A × A') ⊗[ℂ] B` is `(inl ⊗ id)(fst ⊗ id) x + (inr ⊗ id)(snd ⊗ id) x`. -/
theorem mapNonUnitalStarAlgHom_inl_fst_add_inr_snd (x : (A × A') ⊗[ℂ] B) :
    mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inl ℂ A A') (NonUnitalStarAlgHom.id ℂ B)
        (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.fst ℂ A A') (NonUnitalStarAlgHom.id ℂ B) x) +
      mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inr ℂ A A') (NonUnitalStarAlgHom.id ℂ B)
        (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.snd ℂ A A') (NonUnitalStarAlgHom.id ℂ B) x) =
      x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, add_add_add_comm, hx, hy]
  | tmul a b =>
    simp only [mapNonUnitalStarAlgHom_tmul, NonUnitalStarAlgHom.inl_apply,
      NonUnitalStarAlgHom.inr_apply, NonUnitalStarAlgHom.fst_apply, NonUnitalStarAlgHom.snd_apply,
      NonUnitalStarAlgHom.coe_id, id_eq, ← TensorProduct.add_tmul, Prod.mk_add_mk, add_zero,
      zero_add]

/-- **Distributivity of the maximal norm over direct sums**: for `x ∈ (A × A') ⊗[ℂ] B`,
`‖x‖_max = max ‖(fst ⊗ id) x‖_max ‖(snd ⊗ id) x‖_max`. -/
theorem maxTensorNorm_prod (x : (A × A') ⊗[ℂ] B) :
    maxTensorNorm (A × A') B x =
      max (maxTensorNorm A B
          (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.fst ℂ A A') (NonUnitalStarAlgHom.id ℂ B) x))
        (maxTensorNorm A' B
          (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.snd ℂ A A') (NonUnitalStarAlgHom.id ℂ B)
            x)) := by
  refine le_antisymm (maxTensorNorm_le_of_forall fun p ↦ ?_)
    (max_le (maxTensorNorm_mapNonUnitalStarAlgHom_le _ _ x)
      (maxTensorNorm_mapNonUnitalStarAlgHom_le _ _ x))
  conv_lhs => rw [← mapNonUnitalStarAlgHom_inl_fst_add_inr_snd x, map_add]
  rw [((isStarOrtho_mapNonUnitalStarAlgHom_inl_inr _ _).map p.tensorHom).norm_add,
    ← p.tensorHom_comp (NonUnitalStarAlgHom.inl ℂ A A') (NonUnitalStarAlgHom.id ℂ B),
    ← p.tensorHom_comp (NonUnitalStarAlgHom.inr ℂ A A') (NonUnitalStarAlgHom.id ℂ B)]
  exact max_le_max (norm_tensorHom_le_maxTensorNorm _ _) (norm_tensorHom_le_maxTensorNorm _ _)

end TauCeti
