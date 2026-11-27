/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Prod
public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Product.Map
import TauCeti.Analysis.CStarAlgebra.Quotient

/-!
# The maximal C*-tensor product distributes over direct sums

For C*-algebras `A`, `A'` and `B`, the star homomorphism `(fst ⊗ id, snd ⊗ id)` is a star
isomorphism `TauCeti.MaxTensorProduct.prodLeft : (A × A') ⊗max B ≃ (A ⊗max B) × (A' ⊗max B)`.
It is isometric by the norm formula `‖x‖_max = max ‖x₁‖_max ‖x₂‖_max`
(`TauCeti.maxTensorNorm_prod`), and surjective since its range is closed and contains the dense
set of pairs of elements of `A ⊗[ℂ] B` and `A' ⊗[ℂ] B`.

## Main declarations

* `TauCeti.MaxTensorProduct.prodLeft`: `(A × A') ⊗max B ≃⋆ₐ[ℂ] (A ⊗max B) × (A' ⊗max B)`, with
  inverse `TauCeti.MaxTensorProduct.prodLeft_symm_apply`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.5–II.9.2.6 (functoriality of C*-tensor products).
-/

public section

noncomputable section

open TensorProduct Algebra.TensorProduct
open scoped CStarAlgebra

universe u v

namespace TauCeti

namespace MaxTensorProduct

open CStarTensorProduct

variable {A A' : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
  [NonUnitalCStarAlgebra B]

variable (A A' B) in
/-- The star homomorphism `(A × A') ⊗max B → (A ⊗max B) × (A' ⊗max B)` with components
`fst ⊗ id` and `snd ⊗ id`. -/
def prodLeftHom :
    MaxTensorProduct (A × A') B →⋆ₙₐ[ℂ] MaxTensorProduct A B × MaxTensorProduct A' B :=
  (map (NonUnitalStarAlgHom.fst ℂ A A') (NonUnitalStarAlgHom.id ℂ B)).prod
    (map (NonUnitalStarAlgHom.snd ℂ A A') (NonUnitalStarAlgHom.id ℂ B))

/-- The components of `TauCeti.MaxTensorProduct.prodLeftHom` are `fst ⊗ id` and `snd ⊗ id`. -/
@[simp]
theorem prodLeftHom_apply (u : MaxTensorProduct (A × A') B) :
    prodLeftHom A A' B u =
      (map (NonUnitalStarAlgHom.fst ℂ A A') (NonUnitalStarAlgHom.id ℂ B) u,
        map (NonUnitalStarAlgHom.snd ℂ A A') (NonUnitalStarAlgHom.id ℂ B) u) :=
  (rfl)

theorem prodLeftHom_of_tmul (a : A × A') (b : B) :
    prodLeftHom A A' B (of (maxCStarTensorNorm (A × A') B) (a ⊗ₜ b)) =
      (of (maxCStarTensorNorm A B) (a.1 ⊗ₜ b), of (maxCStarTensorNorm A' B) (a.2 ⊗ₜ b)) := by
  simp

/-- `TauCeti.MaxTensorProduct.prodLeftHom` is isometric. -/
theorem norm_prodLeftHom (u : MaxTensorProduct (A × A') B) : ‖prodLeftHom A A' B u‖ = ‖u‖ := by
  refine induction_on u (isClosed_eq (continuous_norm.comp (map_continuous _)) continuous_norm)
    fun x ↦ ?_
  simp only [prodLeftHom_apply, Prod.norm_mk, map_of, norm_of, maxCStarTensorNorm_apply]
  exact (maxTensorNorm_prod x).symm

/-- `TauCeti.MaxTensorProduct.prodLeftHom` is bijective: isometric, with closed dense range. -/
theorem prodLeftHom_bijective : Function.Bijective (prodLeftHom A A' B) := by
  refine ⟨(AddMonoidHomClass.isometry_of_norm _ norm_prodLeftHom).injective,
    NonUnitalStarAlgHom.surjective_of_denseRange ?_⟩
  refine ((denseRange_of (N := maxCStarTensorNorm A B)).prodMap
    (denseRange_of (N := maxCStarTensorNorm A' B))).mono ?_
  rintro _ ⟨⟨y, z⟩, rfl⟩
  refine ⟨of _ (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inl ℂ A A')
    (NonUnitalStarAlgHom.id ℂ B) y + mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inr ℂ A A')
    (NonUnitalStarAlgHom.id ℂ B) z), ?_⟩
  simp [map_of]

variable (A A' B) in
/-- **Distributivity of the maximal tensor product over direct sums**: the star isomorphism
`(A × A') ⊗max B ≃ (A ⊗max B) × (A' ⊗max B)` sending `(a, a') ⊗ b` to `(a ⊗ b, a' ⊗ b)`. -/
def prodLeft : MaxTensorProduct (A × A') B ≃⋆ₐ[ℂ] MaxTensorProduct A B × MaxTensorProduct A' B :=
  StarAlgEquiv.ofBijective (prodLeftHom A A' B) prodLeftHom_bijective

@[simp]
theorem prodLeft_apply (u : MaxTensorProduct (A × A') B) :
    prodLeft A A' B u = prodLeftHom A A' B u :=
  (rfl)

/-- The isomorphism sends `(a, a') ⊗ b` to `(a ⊗ b, a' ⊗ b)`. -/
theorem prodLeft_of_tmul (a : A × A') (b : B) :
    prodLeft A A' B (of (maxCStarTensorNorm (A × A') B) (a ⊗ₜ b)) =
      (of (maxCStarTensorNorm A B) (a.1 ⊗ₜ b), of (maxCStarTensorNorm A' B) (a.2 ⊗ₜ b)) :=
  prodLeftHom_of_tmul a b

/-- On the algebraic tensor products, the inverse isomorphism sends `(y, z)` to
`(inl ⊗ id) y + (inr ⊗ id) z`. -/
theorem prodLeft_symm_of (y : A ⊗[ℂ] B) (z : A' ⊗[ℂ] B) :
    (prodLeft A A' B).symm (of (maxCStarTensorNorm A B) y, of (maxCStarTensorNorm A' B) z) =
      of (maxCStarTensorNorm (A × A') B)
        (mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inl ℂ A A') (NonUnitalStarAlgHom.id ℂ B) y +
          mapNonUnitalStarAlgHom (NonUnitalStarAlgHom.inr ℂ A A') (NonUnitalStarAlgHom.id ℂ B)
            z) :=
  (prodLeft A A' B).symm_apply_eq.2 (by simp [map_of])

/-- The inverse isomorphism sends `(y, z)` to `(inl ⊗ id) y + (inr ⊗ id) z`. -/
@[simp]
theorem prodLeft_symm_apply (y : MaxTensorProduct A B) (z : MaxTensorProduct A' B) :
    (prodLeft A A' B).symm (y, z) =
      map (NonUnitalStarAlgHom.inl ℂ A A') (NonUnitalStarAlgHom.id ℂ B) y +
        map (NonUnitalStarAlgHom.inr ℂ A A') (NonUnitalStarAlgHom.id ℂ B) z := by
  refine induction_on y (isClosed_eq ((map_continuous _).comp (.prodMk_left z))
    ((map_continuous _).add continuous_const)) fun y ↦ ?_
  refine induction_on z (isClosed_eq ((map_continuous _).comp (.prodMk_right _))
    (continuous_const.add (map_continuous _))) fun z ↦ ?_
  rw [prodLeft_symm_of, map_add, map_of, map_of]

/-- The inverse isomorphism sends `(a ⊗ b, a' ⊗ b')` to `(a, 0) ⊗ b + (0, a') ⊗ b'`. -/
theorem prodLeft_symm_of_tmul (a : A) (b : B) (a' : A') (b' : B) :
    (prodLeft A A' B).symm
        (of (maxCStarTensorNorm A B) (a ⊗ₜ b), of (maxCStarTensorNorm A' B) (a' ⊗ₜ b')) =
      of (maxCStarTensorNorm (A × A') B) ((a, 0) ⊗ₜ b + (0, a') ⊗ₜ b') := by
  simp [map_of]

end MaxTensorProduct

end TauCeti
