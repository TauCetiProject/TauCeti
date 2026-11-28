/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MinTensor.Product
public import TauCeti.Analysis.CStarAlgebra.TensorProduct.Prod
import Mathlib.Algebra.Star.Orthogonal
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import TauCeti.Analysis.CStarAlgebra.SpatialNorm.Map

/-!
# The minimal C*-tensor product distributes over direct sums

For C*-algebras `A`, `A'` and `B`, an element `x` of `(A × A') ⊗[ℂ] B` has the components
`x₁ = (fst ⊗ id) x ∈ A ⊗[ℂ] B` and `x₂ = (snd ⊗ id) x ∈ A' ⊗[ℂ] B`, and its minimal norm is
`‖x‖_min = max ‖x₁‖_min ‖x₂‖_min` (`TauCeti.minTensorNorm_prod`). Consequently the star
homomorphism `(fst ⊗ id, snd ⊗ id)` is a star isomorphism
`TauCeti.MinTensorProduct.prodLeft : (A × A') ⊗min B ≃ (A ⊗min B) × (A' ⊗min B)`.

The inequality `≥` is functoriality (`TauCeti.minTensorNorm_mapNonUnitalStarAlgHom_le`). For `≤`,
`x = (inl ⊗ id) x₁ + (inr ⊗ id) x₂` in `(A × A') ⊗[ℂ] B`, and the two summands are
star-orthogonal there (`Algebra.TensorProduct.isStarOrtho_mapNonUnitalStarAlgHom_inl_inr`). A
spatial tensor homomorphism `σ ⊗ τ` keeps them star-orthogonal, so the norm of its value at `x` is
the maximum of the norms of the two summands, which are the values of `(σ ∘ inl) ⊗ τ` at `x₁` and
of `(σ ∘ inr) ⊗ τ` at `x₂`. The isomorphism is the instance of
`TauCeti.CStarTensorProduct.prodLeft` for this norm formula.

## Main declarations

* `TauCeti.minTensorNorm_prod`: `‖x‖_min = max ‖x₁‖_min ‖x₂‖_min`.
* `TauCeti.MinTensorProduct.prodLeft`: `(A × A') ⊗min B ≃⋆ₐ[ℂ] (A ⊗min B) × (A' ⊗min B)`, with
  inverse `TauCeti.MinTensorProduct.prodLeft_symm_apply`.

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
def prodLeftHom :
    MinTensorProduct (A × A') B →⋆ₙₐ[ℂ] MinTensorProduct A B × MinTensorProduct A' B :=
  (map (NonUnitalStarAlgHom.fst ℂ A A') (NonUnitalStarAlgHom.id ℂ B)).prod
    (map (NonUnitalStarAlgHom.snd ℂ A A') (NonUnitalStarAlgHom.id ℂ B))

/-- The components of `TauCeti.MinTensorProduct.prodLeftHom` are `fst ⊗ id` and `snd ⊗ id`. -/
@[simp]
theorem prodLeftHom_apply (u : MinTensorProduct (A × A') B) :
    prodLeftHom A A' B u =
      (map (NonUnitalStarAlgHom.fst ℂ A A') (NonUnitalStarAlgHom.id ℂ B) u,
        map (NonUnitalStarAlgHom.snd ℂ A A') (NonUnitalStarAlgHom.id ℂ B) u) :=
  (rfl)

theorem prodLeftHom_of_tmul (a : A × A') (b : B) :
    prodLeftHom A A' B (of (minCStarTensorNorm (A × A') B) (a ⊗ₜ b)) =
      (of (minCStarTensorNorm A B) (a.1 ⊗ₜ b), of (minCStarTensorNorm A' B) (a.2 ⊗ₜ b)) := by
  simp

variable (A A' B) in
/-- **Distributivity of the minimal tensor product over direct sums**: the star isomorphism
`(A × A') ⊗min B ≃ (A ⊗min B) × (A' ⊗min B)` sending `(a, a') ⊗ b` to `(a ⊗ b, a' ⊗ b)`, the
instance of `TauCeti.CStarTensorProduct.prodLeft` for the norm formula
`TauCeti.minTensorNorm_prod`. -/
def prodLeft : MinTensorProduct (A × A') B ≃⋆ₐ[ℂ] MinTensorProduct A B × MinTensorProduct A' B :=
  CStarTensorProduct.prodLeft fun x ↦ by simpa using minTensorNorm_prod x

@[simp]
theorem prodLeft_apply (u : MinTensorProduct (A × A') B) :
    prodLeft A A' B u = prodLeftHom A A' B u :=
  congrFun (prodLeft_eq_of_of (F := prodLeftHom A A' B) _ (map_continuous _) fun x ↦ by
    simp [map_of]) u

/-- `TauCeti.MinTensorProduct.prodLeftHom` is bijective. -/
theorem prodLeftHom_bijective : Function.Bijective (prodLeftHom A A' B) :=
  (funext prodLeft_apply : ⇑(prodLeft A A' B) = prodLeftHom A A' B) ▸ (prodLeft A A' B).bijective

/-- `TauCeti.MinTensorProduct.prodLeftHom` is isometric. -/
theorem norm_prodLeftHom (u : MinTensorProduct (A × A') B) : ‖prodLeftHom A A' B u‖ = ‖u‖ :=
  NonUnitalStarAlgHom.norm_map _ prodLeftHom_bijective.injective u

/-- The isomorphism sends `(a, a') ⊗ b` to `(a ⊗ b, a' ⊗ b)`. -/
theorem prodLeft_of_tmul (a : A × A') (b : B) :
    prodLeft A A' B (of (minCStarTensorNorm (A × A') B) (a ⊗ₜ b)) =
      (of (minCStarTensorNorm A B) (a.1 ⊗ₜ b), of (minCStarTensorNorm A' B) (a.2 ⊗ₜ b)) := by
  rw [prodLeft_apply, prodLeftHom_of_tmul]

/-- On the algebraic tensor products, the inverse isomorphism sends `(y, z)` to
`(inl ⊗ id) y + (inr ⊗ id) z`. -/
theorem prodLeft_symm_of (y : A ⊗[ℂ] B) (z : A' ⊗[ℂ] B) :
    (prodLeft A A' B).symm (of (minCStarTensorNorm A B) y, of (minCStarTensorNorm A' B) z) =
      of (minCStarTensorNorm (A × A') B)
        (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inl ℂ A A') (NonUnitalStarAlgHom.id ℂ B) y +
          mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inr ℂ A A') (NonUnitalStarAlgHom.id ℂ B)
            z) :=
  CStarTensorProduct.prodLeft_symm_of _ y z

/-- The inverse isomorphism sends `(y, z)` to `(inl ⊗ id) y + (inr ⊗ id) z`. -/
@[simp]
theorem prodLeft_symm_apply (y : MinTensorProduct A B) (z : MinTensorProduct A' B) :
    (prodLeft A A' B).symm (y, z) =
      map (NonUnitalStarAlgHom.inl ℂ A A') (NonUnitalStarAlgHom.id ℂ B) y +
        map (NonUnitalStarAlgHom.inr ℂ A A') (NonUnitalStarAlgHom.id ℂ B) z :=
  prodLeft_symm_eq (A := A) (A' := A') (B := B) _ (map_continuous _) (map_continuous _)
    (map_of _ _) (map_of _ _) y z

/-- The inverse isomorphism sends `(a ⊗ b, a' ⊗ b')` to `(a, 0) ⊗ b + (0, a') ⊗ b'`. -/
theorem prodLeft_symm_of_tmul (a : A) (b : B) (a' : A') (b' : B) :
    (prodLeft A A' B).symm
        (of (minCStarTensorNorm A B) (a ⊗ₜ b), of (minCStarTensorNorm A' B) (a' ⊗ₜ b')) =
      of (minCStarTensorNorm (A × A') B) ((a, 0) ⊗ₜ b + (0, a') ⊗ₜ b') := by
  simp

end MinTensorProduct

end TauCeti
