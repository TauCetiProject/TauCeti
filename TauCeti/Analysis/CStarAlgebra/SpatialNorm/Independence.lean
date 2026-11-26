/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import TauCeti.Analysis.CStarAlgebra.SpatialNorm
public import TauCeti.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Spectrum
import TauCeti.Analysis.CStarAlgebra.Matrix.Slice

/-!
# Representation independence of the spatial C*-norm

Let `A` and `B` be C*-algebras, and let `π₁ : A → B(H₁)`, `π₂ : B → B(H₂)` be star homomorphisms
into the bounded operators on complex Hilbert spaces. They give the operator
`(π₁ ⊗ π₂)(x) = spatialTensorLinearMap (TensorProduct.map π₁ π₂ x)` on the completed Hilbert
tensor product `H₁ ⊗₂ H₂` for each `x ∈ A ⊗[ℂ] B`. This file proves that the norm of this operator
does not depend on the choice of **faithful** (injective) representations
(`TauCeti.norm_spatialTensorLinearMap_map_eq`), and that faithful representations give the
largest such norm (`TauCeti.norm_spatialTensorLinearMap_map_le`). For closed concrete
C*-algebras `A ⊆ B(E)` and `B ⊆ B(F)`, the spatial norm `‖x‖_min` of
`TauCeti.Analysis.CStarAlgebra.SpatialNorm` is therefore the norm of `(π₁ ⊗ π₂)(x)` for every pair
of faithful representations
(`NonUnitalStarSubalgebra.norm_spatialTensorLinearMap_map_eq_spatialNorm`, Takesaki I,
Theorem IV.4.9), and it bounds that norm for every pair of representations
(`NonUnitalStarSubalgebra.norm_spatialTensorLinearMap_map_le_spatialNorm`).

The proof treats one factor at a time. For `y ∈ A ⊗ B(F)` and a finite orthonormal family
`e₁, …, eₙ` in `F`, contracting the second factor against the vector functionals `b ↦ ⟪eₖ, b eₗ⟫`
(`LinearMap.tensorComponent`) gives a matrix `S ∈ Mₙ(A)`, and `π(S) ∈ Mₙ(B(H))` is the matrix of
right slices `TensorProduct.sliceRight (eₗ) (eₖ)` of the operator `(π ⊗ 1)(y)`
(`TauCeti.sliceRight_spatialTensorLinearMap`,
`TauCeti.sliceRight_spatialTensorLinearMap_rTensor`). The norm of an operator on `H ⊗₂ F` is the
supremum of the norms of these slice matrices over all finite orthonormal families
(`TensorProduct.norm_ofMatrix_sliceRight_le`,
`TensorProduct.opNorm_le_of_forall_norm_ofMatrix_sliceRight_le`). The matrix amplification of a
star homomorphism of C*-algebras is contractive, and isometric when the homomorphism is injective,
so `‖π(S)‖ ≤ ‖S‖ = ‖σ(S)‖ ≤ ‖(σ ⊗ 1)(y)‖` for faithful `σ`. The second factor reduces to the first
through the flip `H ⊗₂ K ≃ K ⊗₂ H` (`TauCeti.norm_spatialTensorLinearMap_comm`).

## Main declarations

* `TauCeti.norm_spatialTensorLinearMap_map_le`: `‖(π₁ ⊗ π₂)(x)‖ ≤ ‖(σ₁ ⊗ σ₂)(x)‖` when `σ₁` and
  `σ₂` are injective.
* `TauCeti.norm_spatialTensorLinearMap_map_eq`: **representation independence**, the norms agree
  for any two pairs of faithful representations.
* `NonUnitalStarSubalgebra.norm_spatialTensorLinearMap_map_eq_spatialNorm`: for closed concrete
  operator algebras, `‖(π₁ ⊗ π₂)(x)‖ = ‖x‖_min` for faithful `π₁`, `π₂`.
* `NonUnitalStarSubalgebra.norm_spatialTensorLinearMap_map_le_spatialNorm`:
  `‖(π₁ ⊗ π₂)(x)‖ ≤ ‖x‖_min` for arbitrary star homomorphisms `π₁`, `π₂`.

## References

* M. Takesaki, *Theory of Operator Algebras I*, Chapter IV, §4 (Theorem IV.4.9 is the
  representation independence of the spatial norm).
-/

public section

noncomputable section

open UniformSpace TensorProduct ContinuousLinearMap
open scoped InnerProductSpace ComplexOrder

/-! ### Right slices as contractions against vector functionals -/

namespace TauCeti

variable {𝕜 A E E' F F' : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [AddCommGroup A] [Module 𝕜 A]

/-- The right slice of `(π ⊗ 1)(y)` at `(g, f)` is `π` applied to the contraction of `y` against
the vector functional `b ↦ ⟪f, b g⟫` on its second factor. -/
theorem sliceRight_spatialTensorLinearMap_rTensor [CompleteSpace E'] (π : A →ₗ[𝕜] E →L[𝕜] E')
    (y : A ⊗[𝕜] (F →L[𝕜] F')) (g : F) (f : F') :
    sliceRight g f (spatialTensorLinearMap 𝕜 E F E' F' (π.rTensor _ y)) =
      π (LinearMap.tensorComponent
        (vectorFunctional g f : (F →L[𝕜] F') →L[𝕜] 𝕜).toLinearMap y) := by
  rw [sliceRight_spatialTensorLinearMap, LinearMap.rTensor, LinearMap.tensorComponent_map,
    LinearMap.comp_id]

/-! ### Representation independence -/

variable {A B H K F : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- **One-sided comparison**: for a star homomorphism `π` and an injective star homomorphism `σ`
of a C*-algebra `A`, `‖(π ⊗ 1)(y)‖ ≤ ‖(σ ⊗ 1)(y)‖` for all `y ∈ A ⊗ B(F)`. -/
theorem norm_spatialTensorLinearMap_rTensor_le (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (σ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hσ : Function.Injective σ) (y : A ⊗[ℂ] (F →L[ℂ] F)) :
    ‖spatialTensorLinearMap ℂ H F H F ((π : A →ₗ[ℂ] H →L[ℂ] H).rTensor _ y)‖ ≤
      ‖spatialTensorLinearMap ℂ K F K F ((σ : A →ₗ[ℂ] K →L[ℂ] K).rTensor _ y)‖ := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  refine opNorm_le_of_forall_norm_ofMatrix_sliceRight_le _ fun n e he ↦ ?_
  let S : CStarMatrix (Fin n) (Fin n) A :=
    CStarMatrix.ofMatrix fun k l ↦
      LinearMap.tensorComponent (vectorFunctional (e l) (e k) : (F →L[ℂ] F) →L[ℂ] ℂ).toLinearMap y
  simp only [sliceRight_spatialTensorLinearMap_rTensor]
  calc ‖CStarMatrix.mapₙₐ π S‖ ≤ ‖S‖ := NonUnitalStarAlgHom.norm_apply_le _ _
    _ = ‖CStarMatrix.mapₙₐ σ S‖ :=
        (NonUnitalStarAlgHom.norm_map _ (CStarMatrix.map_injective hσ) S).symm
    _ ≤ _ := by
        have := norm_ofMatrix_sliceRight_le he
          (spatialTensorLinearMap ℂ K F K F ((σ : A →ₗ[ℂ] K →L[ℂ] K).rTensor _ y))
        simp only [sliceRight_spatialTensorLinearMap_rTensor] at this
        exact this

/-- **One-sided comparison in the second factor**: for a star homomorphism `π` and an injective
star homomorphism `σ` of a C*-algebra `B`, `‖(1 ⊗ π)(y)‖ ≤ ‖(1 ⊗ σ)(y)‖` for all
`y ∈ B(E) ⊗ B`. -/
theorem norm_spatialTensorLinearMap_lTensor_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (π : B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (σ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hσ : Function.Injective σ) (y : (E →L[ℂ] E) ⊗[ℂ] B) :
    ‖spatialTensorLinearMap ℂ E H E H ((π : B →ₗ[ℂ] H →L[ℂ] H).lTensor _ y)‖ ≤
      ‖spatialTensorLinearMap ℂ E K E K ((σ : B →ₗ[ℂ] K →L[ℂ] K).lTensor _ y)‖ := by
  calc _ = ‖spatialTensorLinearMap ℂ H E H E
        ((π : B →ₗ[ℂ] H →L[ℂ] H).rTensor _ (TensorProduct.comm ℂ _ _ y))‖ := by
        rw [LinearMap.rTensor_comm, norm_spatialTensorLinearMap_comm]
    _ ≤ ‖spatialTensorLinearMap ℂ K E K E
        ((σ : B →ₗ[ℂ] K →L[ℂ] K).rTensor _ (TensorProduct.comm ℂ _ _ y))‖ :=
        norm_spatialTensorLinearMap_rTensor_le π σ hσ _
    _ = _ := by rw [LinearMap.rTensor_comm, norm_spatialTensorLinearMap_comm]

variable {H₁ H₂ K₁ K₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
  [NormedAddCommGroup K₂] [InnerProductSpace ℂ K₂] [CompleteSpace K₂]

/-- Faithful representations give the **largest** spatial operator norm: for star homomorphisms
`π₁`, `π₂` and injective star homomorphisms `σ₁`, `σ₂` of C*-algebras `A`, `B`,
`‖(π₁ ⊗ π₂)(x)‖ ≤ ‖(σ₁ ⊗ σ₂)(x)‖` for all `x ∈ A ⊗ B`. -/
theorem norm_spatialTensorLinearMap_map_le (π₁ : A →⋆ₙₐ[ℂ] (H₁ →L[ℂ] H₁))
    (π₂ : B →⋆ₙₐ[ℂ] (H₂ →L[ℂ] H₂)) (σ₁ : A →⋆ₙₐ[ℂ] (K₁ →L[ℂ] K₁))
    (σ₂ : B →⋆ₙₐ[ℂ] (K₂ →L[ℂ] K₂)) (hσ₁ : Function.Injective σ₁)
    (hσ₂ : Function.Injective σ₂) (x : A ⊗[ℂ] B) :
    ‖spatialTensorLinearMap ℂ H₁ H₂ H₁ H₂ (map (π₁ : A →ₗ[ℂ] H₁ →L[ℂ] H₁)
        (π₂ : B →ₗ[ℂ] H₂ →L[ℂ] H₂) x)‖ ≤
      ‖spatialTensorLinearMap ℂ K₁ K₂ K₁ K₂ (map (σ₁ : A →ₗ[ℂ] K₁ →L[ℂ] K₁)
        (σ₂ : B →ₗ[ℂ] K₂ →L[ℂ] K₂) x)‖ := by
  rw [← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply,
    ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply]
  calc _ ≤ ‖spatialTensorLinearMap ℂ K₁ H₂ K₁ H₂ ((σ₁ : A →ₗ[ℂ] K₁ →L[ℂ] K₁).rTensor _
          ((π₂ : B →ₗ[ℂ] H₂ →L[ℂ] H₂).lTensor _ x))‖ :=
        norm_spatialTensorLinearMap_rTensor_le π₁ σ₁ hσ₁ _
    _ = ‖spatialTensorLinearMap ℂ K₁ H₂ K₁ H₂ ((π₂ : B →ₗ[ℂ] H₂ →L[ℂ] H₂).lTensor _
          ((σ₁ : A →ₗ[ℂ] K₁ →L[ℂ] K₁).rTensor _ x))‖ := by
        congr 2
        rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.comp_apply,
          LinearMap.lTensor_comp_rTensor]
    _ ≤ _ := norm_spatialTensorLinearMap_lTensor_le π₂ σ₂ hσ₂ _

/-- **Representation independence of the spatial norm** (Takesaki I, Theorem IV.4.9): for
faithful representations `π₁`, `σ₁` of `A` and `π₂`, `σ₂` of `B`,
`‖(π₁ ⊗ π₂)(x)‖ = ‖(σ₁ ⊗ σ₂)(x)‖` for all `x ∈ A ⊗ B`. -/
theorem norm_spatialTensorLinearMap_map_eq (π₁ : A →⋆ₙₐ[ℂ] (H₁ →L[ℂ] H₁))
    (π₂ : B →⋆ₙₐ[ℂ] (H₂ →L[ℂ] H₂)) (σ₁ : A →⋆ₙₐ[ℂ] (K₁ →L[ℂ] K₁))
    (σ₂ : B →⋆ₙₐ[ℂ] (K₂ →L[ℂ] K₂)) (hπ₁ : Function.Injective π₁)
    (hπ₂ : Function.Injective π₂) (hσ₁ : Function.Injective σ₁)
    (hσ₂ : Function.Injective σ₂) (x : A ⊗[ℂ] B) :
    ‖spatialTensorLinearMap ℂ H₁ H₂ H₁ H₂ (map (π₁ : A →ₗ[ℂ] H₁ →L[ℂ] H₁)
        (π₂ : B →ₗ[ℂ] H₂ →L[ℂ] H₂) x)‖ =
      ‖spatialTensorLinearMap ℂ K₁ K₂ K₁ K₂ (map (σ₁ : A →ₗ[ℂ] K₁ →L[ℂ] K₁)
        (σ₂ : B →ₗ[ℂ] K₂ →L[ℂ] K₂) x)‖ :=
  (norm_spatialTensorLinearMap_map_le π₁ π₂ σ₁ σ₂ hσ₁ hσ₂ x).antisymm
    (norm_spatialTensorLinearMap_map_le σ₁ σ₂ π₁ π₂ hπ₁ hπ₂ x)

end TauCeti

namespace NonUnitalStarSubalgebra

open TauCeti

variable {E F H₁ H₂ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  (A : NonUnitalStarSubalgebra ℂ (E →L[ℂ] E)) (B : NonUnitalStarSubalgebra ℂ (F →L[ℂ] F))
  [IsClosed (A : Set (E →L[ℂ] E))] [IsClosed (B : Set (F →L[ℂ] F))]

/-- The spatial norm of closed concrete operator algebras bounds `‖(π₁ ⊗ π₂)(x)‖` for all star
homomorphisms `π₁`, `π₂`. -/
theorem norm_spatialTensorLinearMap_map_le_spatialNorm (π₁ : A →⋆ₙₐ[ℂ] (H₁ →L[ℂ] H₁))
    (π₂ : B →⋆ₙₐ[ℂ] (H₂ →L[ℂ] H₂)) (x : A ⊗[ℂ] B) :
    ‖spatialTensorLinearMap ℂ H₁ H₂ H₁ H₂ (TensorProduct.map (π₁ : A →ₗ[ℂ] H₁ →L[ℂ] H₁)
        (π₂ : B →ₗ[ℂ] H₂ →L[ℂ] H₂) x)‖ ≤ spatialNorm A B x := by
  rw [spatialNorm_def, spatialTensorHom_apply]
  exact norm_spatialTensorLinearMap_map_le π₁ π₂ (NonUnitalStarSubalgebraClass.subtype A)
    (NonUnitalStarSubalgebraClass.subtype B) Subtype.val_injective Subtype.val_injective x

/-- **Representation independence of the spatial norm** (Takesaki I, Theorem IV.4.9): for closed
concrete operator algebras `A ⊆ B(E)`, `B ⊆ B(F)` and faithful representations `π₁` of `A` and
`π₂` of `B`, `‖(π₁ ⊗ π₂)(x)‖ = ‖x‖_min`. -/
theorem norm_spatialTensorLinearMap_map_eq_spatialNorm (π₁ : A →⋆ₙₐ[ℂ] (H₁ →L[ℂ] H₁))
    (π₂ : B →⋆ₙₐ[ℂ] (H₂ →L[ℂ] H₂)) (hπ₁ : Function.Injective π₁)
    (hπ₂ : Function.Injective π₂) (x : A ⊗[ℂ] B) :
    ‖spatialTensorLinearMap ℂ H₁ H₂ H₁ H₂ (TensorProduct.map (π₁ : A →ₗ[ℂ] H₁ →L[ℂ] H₁)
        (π₂ : B →ₗ[ℂ] H₂ →L[ℂ] H₂) x)‖ = spatialNorm A B x := by
  rw [spatialNorm_def, spatialTensorHom_apply]
  exact norm_spatialTensorLinearMap_map_eq π₁ π₂ (NonUnitalStarSubalgebraClass.subtype A)
    (NonUnitalStarSubalgebraClass.subtype B) hπ₁ hπ₂ Subtype.val_injective
    Subtype.val_injective x

end NonUnitalStarSubalgebra
