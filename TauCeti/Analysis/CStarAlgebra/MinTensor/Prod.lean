/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MinTensor.Product
import Mathlib.Algebra.Star.Orthogonal
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import TauCeti.Analysis.CStarAlgebra.Quotient
import TauCeti.Analysis.CStarAlgebra.SpatialNorm.Map

/-!
# The minimal C*-tensor product distributes over direct sums

For C*-algebras `A`, `A'` and `B`, an element `x` of `(A × A') ⊗[ℂ] B` has the components
`x₁ = (fst ⊗ id) x ∈ A ⊗[ℂ] B` and `x₂ = (snd ⊗ id) x ∈ A' ⊗[ℂ] B`, and its minimal norm is
`‖x‖_min = max ‖x₁‖_min ‖x₂‖_min` (`TauCeti.minTensorNorm_prod`). Consequently the star
homomorphism `(fst ⊗ id, snd ⊗ id)` is a star isomorphism
`TauCeti.MinTensorProduct.prodEquiv : (A × A') ⊗min B ≃ (A ⊗min B) × (A' ⊗min B)`.

The inequality `≥` is functoriality (`TauCeti.minTensorNorm_mapNonUnitalStarAlgHom_le`). For `≤`,
`x = (inl ⊗ id) x₁ + (inr ⊗ id) x₂` in `(A × A') ⊗[ℂ] B`, and the two summands are
star-orthogonal there (`Algebra.TensorProduct.isStarOrtho_mapNonUnitalStarAlgHom_inl_inr`). A
spatial tensor homomorphism `σ ⊗ τ` keeps them star-orthogonal, so the norm of its value at `x` is
the maximum of the norms of the two summands, which are the values of `(σ ∘ inl) ⊗ τ` at `x₁` and
of `(σ ∘ inr) ⊗ τ` at `x₂`. The isomorphism is isometric by the norm formula, and surjective since
its range is closed and contains the dense set of pairs of elements of `A ⊗[ℂ] B` and
`A' ⊗[ℂ] B`.

## Main declarations

* `TauCeti.minTensorNorm_prod`: `‖x‖_min = max ‖x₁‖_min ‖x₂‖_min`.
* `TauCeti.MinTensorProduct.prodEquiv`: `(A × A') ⊗min B ≃⋆ₐ[ℂ] (A ⊗min B) × (A' ⊗min B)`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.5–II.9.2.6 (functoriality of C*-tensor products).
-/

public section

noncomputable section

open TensorProduct Algebra.TensorProduct
open scoped CStarAlgebra

namespace TauCeti

variable {A A' B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
  [NonUnitalCStarAlgebra B]

/-- **Distributivity of the minimal norm over direct sums**: for `x ∈ (A × A') ⊗[ℂ] B`,
`‖x‖_min = max ‖(fst ⊗ id) x‖_min ‖(snd ⊗ id) x‖_min`. -/
theorem minTensorNorm_prod (x : (A × A') ⊗[ℂ] B) :
    minTensorNorm (A × A') B x =
      max (minTensorNorm A B
          (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.fst ℂ A A') (NonUnitalStarAlgHom.id ℂ B) x))
        (minTensorNorm A' B
          (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.snd ℂ A A') (NonUnitalStarAlgHom.id ℂ B)
            x)) := by
  refine le_antisymm (minTensorNorm_le_of_forall fun p ↦ ?_)
    (max_le (minTensorNorm_mapNonUnitalStarAlgHom_le _ _ x)
      (minTensorNorm_mapNonUnitalStarAlgHom_le _ _ x))
  conv_lhs => rw [← mapNonUnitalStarAlgHom_inl_fst_add_inr_snd x, map_add]
  rw [((isStarOrtho_mapNonUnitalStarAlgHom_inl_inr _ _).map
      (p.left.spatialTensorHom p.right)).norm_add,
    NonUnitalStarAlgHom.spatialTensorHom_mapNonUnitalStarAlgHom p.left p.right
      (NonUnitalStarAlgHom.inl ℂ A A'),
    NonUnitalStarAlgHom.spatialTensorHom_mapNonUnitalStarAlgHom p.left p.right
      (NonUnitalStarAlgHom.inr ℂ A A')]
  exact max_le_max (norm_spatialTensorHom_le_minTensorNorm _ _ _)
    (norm_spatialTensorHom_le_minTensorNorm _ _ _)

namespace MinTensorProduct

open CStarTensorProduct

variable (A A' B) in
/-- The star homomorphism `(A × A') ⊗min B → (A ⊗min B) × (A' ⊗min B)` with components
`fst ⊗ id` and `snd ⊗ id`. -/
def prodHom : MinTensorProduct (A × A') B →⋆ₙₐ[ℂ] MinTensorProduct A B × MinTensorProduct A' B :=
  (map (NonUnitalStarAlgHom.fst ℂ A A') (NonUnitalStarAlgHom.id ℂ B)).prod
    (map (NonUnitalStarAlgHom.snd ℂ A A') (NonUnitalStarAlgHom.id ℂ B))

@[simp]
theorem prodHom_of_tmul (a : A × A') (b : B) :
    prodHom A A' B (of (minCStarTensorNorm (A × A') B) (a ⊗ₜ b)) =
      (of (minCStarTensorNorm A B) (a.1 ⊗ₜ b), of (minCStarTensorNorm A' B) (a.2 ⊗ₜ b)) := by
  simp [prodHom]

/-- `TauCeti.MinTensorProduct.prodHom` is isometric. -/
theorem norm_prodHom (u : MinTensorProduct (A × A') B) : ‖prodHom A A' B u‖ = ‖u‖ := by
  refine induction_on u (isClosed_eq (continuous_norm.comp (map_continuous _)) continuous_norm)
    fun x ↦ ?_
  simp only [prodHom, NonUnitalStarAlgHom.prod_apply, Prod.norm_mk, map_of, norm_of,
    minCStarTensorNorm_apply]
  exact (minTensorNorm_prod x).symm

/-- `TauCeti.MinTensorProduct.prodHom` is bijective: isometric, with closed dense range. -/
theorem prodHom_bijective : Function.Bijective (prodHom A A' B) := by
  refine ⟨(AddMonoidHomClass.isometry_of_norm _ norm_prodHom).injective,
    NonUnitalStarAlgHom.surjective_of_denseRange ?_⟩
  refine ((denseRange_of (N := minCStarTensorNorm A B)).prodMap
    (denseRange_of (N := minCStarTensorNorm A' B))).mono ?_
  rintro _ ⟨⟨y, z⟩, rfl⟩
  refine ⟨of _ (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inl ℂ A A')
    (NonUnitalStarAlgHom.id ℂ B) y + mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inr ℂ A A')
    (NonUnitalStarAlgHom.id ℂ B) z), ?_⟩
  have h₁ : ∀ y : A ⊗[ℂ] B, mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.fst ℂ A A')
      (NonUnitalStarAlgHom.id ℂ B) (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inl ℂ A A')
        (NonUnitalStarAlgHom.id ℂ B) y) = y := fun y ↦ by
    induction y using TensorProduct.inductionOn with
    | tmul a b => simp [mapNonUnitalStarAlgHom_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have h₂ : ∀ z : A' ⊗[ℂ] B, mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.snd ℂ A A')
      (NonUnitalStarAlgHom.id ℂ B) (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inr ℂ A A')
        (NonUnitalStarAlgHom.id ℂ B) z) = z := fun z ↦ by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [mapNonUnitalStarAlgHom_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have h₃ : ∀ z : A' ⊗[ℂ] B, mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.fst ℂ A A')
      (NonUnitalStarAlgHom.id ℂ B) (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inr ℂ A A')
        (NonUnitalStarAlgHom.id ℂ B) z) = 0 := fun z ↦ by
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [mapNonUnitalStarAlgHom_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  have h₄ : ∀ y : A ⊗[ℂ] B, mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.snd ℂ A A')
      (NonUnitalStarAlgHom.id ℂ B) (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inl ℂ A A')
        (NonUnitalStarAlgHom.id ℂ B) y) = 0 := fun y ↦ by
    induction y using TensorProduct.inductionOn with
    | tmul a b => simp [mapNonUnitalStarAlgHom_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  simp only [prodHom, NonUnitalStarAlgHom.prod_apply, map_of, map_add, h₁, h₂, h₃, h₄, map_zero,
    Prod.map_apply, Prod.mk_add_mk, add_zero, zero_add]

variable (A A' B) in
/-- **Distributivity of the minimal tensor product over direct sums**: the star isomorphism
`(A × A') ⊗min B ≃ (A ⊗min B) × (A' ⊗min B)` sending `(a, a') ⊗ b` to `(a ⊗ b, a' ⊗ b)`. -/
def prodEquiv : MinTensorProduct (A × A') B ≃⋆ₐ[ℂ] MinTensorProduct A B × MinTensorProduct A' B :=
  StarAlgEquiv.ofBijective (prodHom A A' B) prodHom_bijective

@[simp]
theorem prodEquiv_apply (u : MinTensorProduct (A × A') B) :
    prodEquiv A A' B u = prodHom A A' B u :=
  (rfl)

/-- The isomorphism sends `(a, a') ⊗ b` to `(a ⊗ b, a' ⊗ b)`. -/
theorem prodEquiv_of_tmul (a : A × A') (b : B) :
    prodEquiv A A' B (of (minCStarTensorNorm (A × A') B) (a ⊗ₜ b)) =
      (of (minCStarTensorNorm A B) (a.1 ⊗ₜ b), of (minCStarTensorNorm A' B) (a.2 ⊗ₜ b)) :=
  prodHom_of_tmul a b

end MinTensorProduct

end TauCeti
