/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MinTensor.Norm
public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Product
import TauCeti.Analysis.CStarAlgebra.Quotient

/-!
# The minimal C*-tensor product

Let `A` and `B` be (possibly non-unital) C*-algebras. The minimal C*-norm `TauCeti.minTensorNorm`
is a C*-norm on `A ⊗[ℂ] B` (`TauCeti.minCStarTensorNorm A B`). The completion of `A ⊗[ℂ] B` in it
is the **minimal tensor product** `TauCeti.MinTensorProduct A B` (written A ⊗min B in the
literature; this file declares no notation for it), the C*-tensor product
`TauCeti.CStarTensorProduct` of the minimal norm, with the star homomorphism
`TauCeti.CStarTensorProduct.of (TauCeti.minCStarTensorNorm A B)` from `A ⊗[ℂ] B`, which is
injective, isometric for the minimal norm and has dense range.

**Spatial realization.** Representations `π : A → B(E)` and `ρ : B → B(F)` give the spatial
tensor homomorphism `a ⊗ b ↦ π a ⊗ ρ b` into `B(E ⊗₂ F)`, which is bounded by the minimal norm
and so extends to `TauCeti.MinTensorProduct.spatialTensorHom π ρ`. For faithful `π` and `ρ` it is
isometric (`TauCeti.MinTensorProduct.norm_spatialTensorHom`), by representation independence of
the spatial norm (`TauCeti.minTensorNorm_eq_norm_spatialTensorHom`). For closed concrete operator
algebras `A ⊆ B(E)` and `B ⊆ B(F)`, the minimal tensor product is isomorphic to the spatial
tensor product `NonUnitalStarSubalgebra.minTensor A B`, the closure of the image of `A ⊗[ℂ] B` in
`B(E ⊗₂ F)` (`NonUnitalStarSubalgebra.minTensorProductEquiv`).

**Functoriality.** Star homomorphisms `φ : A → A'` and `ψ : B → B'` give the star homomorphism
`TauCeti.MinTensorProduct.map φ ψ` extending `φ ⊗ ψ`, which is isometric, hence injective, when
`φ` and `ψ` are injective (`TauCeti.MinTensorProduct.norm_map`,
`TauCeti.MinTensorProduct.map_injective`).

**Comparison with the maximal tensor product.** Since `‖·‖_min ≤ ‖·‖_max`, the identity of
`A ⊗[ℂ] B` extends to the canonical star homomorphism
`TauCeti.MaxTensorProduct.toMin : TauCeti.MaxTensorProduct A B → TauCeti.MinTensorProduct A B`,
which is surjective (`TauCeti.MaxTensorProduct.toMin_surjective`): its range is closed, as for
every star homomorphism of C*-algebras, and dense.

## Main declarations

* `TauCeti.minCStarTensorNorm A B`: the minimal norm as a C*-norm.
* `TauCeti.MinTensorProduct A B`: the completion of `A ⊗[ℂ] B` in it, a C*-algebra.
* `TauCeti.MinTensorProduct.spatialTensorHom`: the spatial realization, isometric for faithful
  representations.
* `NonUnitalStarSubalgebra.minTensorProductEquiv`: `A ⊗min B ≃ A ⊗_min B` for closed concrete
  operator algebras.
* `TauCeti.MinTensorProduct.map`: functoriality.
* `TauCeti.MaxTensorProduct.toMin`: the canonical surjection `A ⊗max B → A ⊗min B`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.1–II.9.2.6.
* M. Takesaki, *Theory of Operator Algebras I*, Chapter IV, §4.
-/

public section

noncomputable section

open UniformSpace TensorProduct

universe u v

namespace TauCeti

variable (A : Type u) (B : Type v) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The minimal norm `TauCeti.minTensorNorm` as a C*-norm on `A ⊗[ℂ] B`. -/
def minCStarTensorNorm : CStarTensorNorm A B where
  toFun := minTensorNorm A B
  map_zero' := minTensorNorm_zero
  add_le' := minTensorNorm_add_le
  neg' := minTensorNorm_neg
  eq_zero_of_map_eq_zero' _ := minTensorNorm_eq_zero_iff.1
  smul' := minTensorNorm_smul
  mul_le' := minTensorNorm_mul_le
  star' := minTensorNorm_star
  star_mul_self' := minTensorNorm_star_mul_self

@[simp]
theorem minCStarTensorNorm_apply (x : A ⊗[ℂ] B) : minCStarTensorNorm A B x = minTensorNorm A B x :=
  (rfl)

/-- The **minimal tensor product** of C*-algebras `A` and `B`: the completion of the
algebraic tensor product `A ⊗[ℂ] B` in the minimal C*-norm. It is a C*-algebra, and the
canonical map `TauCeti.CStarTensorProduct.of (TauCeti.minCStarTensorNorm A B)` from `A ⊗[ℂ] B` is
injective and isometric with dense range. -/
abbrev MinTensorProduct : Type (max u v) :=
  CStarTensorProduct (minCStarTensorNorm A B)

namespace MinTensorProduct

open CStarTensorProduct

variable {A B}

/-! ### The spatial realization -/

section Spatial

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The **spatial realization** of `MinTensorProduct A B` by representations `π : A → B(E)` and
`ρ : B → B(F)`: the extension of the spatial tensor homomorphism `a ⊗ b ↦ π a ⊗ ρ b` into
`B(E ⊗₂ F)`. It is isometric when `π` and `ρ` are faithful
(`TauCeti.MinTensorProduct.norm_spatialTensorHom`). -/
def spatialTensorHom (π : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)) (ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F)) :
    MinTensorProduct A B →⋆ₙₐ[ℂ] (Completion (E ⊗[ℂ] F) →L[ℂ] Completion (E ⊗[ℂ] F)) :=
  extend (π.spatialTensorHom ρ) (norm_spatialTensorHom_le_minTensorNorm π ρ)

@[simp]
theorem spatialTensorHom_of (π : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)) (ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F))
    (x : A ⊗[ℂ] B) :
    spatialTensorHom π ρ (of (minCStarTensorNorm A B) x) = π.spatialTensorHom ρ x :=
  extend_of _ _ x

/-- For faithful representations the spatial realization of `MinTensorProduct A B` is
isometric. -/
theorem norm_spatialTensorHom {π : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)} {ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F)}
    (hπ : Function.Injective π) (hρ : Function.Injective ρ) (u : MinTensorProduct A B) :
    ‖spatialTensorHom π ρ u‖ = ‖u‖ :=
  norm_extend _ (fun x ↦ (minTensorNorm_eq_norm_spatialTensorHom hπ hρ x).symm) u

/-- For faithful representations the spatial realization of `MinTensorProduct A B` is
injective. -/
theorem spatialTensorHom_injective {π : A →⋆ₙₐ[ℂ] (E →L[ℂ] E)} {ρ : B →⋆ₙₐ[ℂ] (F →L[ℂ] F)}
    (hπ : Function.Injective π) (hρ : Function.Injective ρ) :
    Function.Injective (spatialTensorHom π ρ) :=
  (injective_iff_map_eq_zero _).2 fun u hu ↦
    norm_eq_zero.1 (by rw [← norm_spatialTensorHom hπ hρ u, hu]; simp)

end Spatial

/-! ### Functoriality -/

section Map

variable {A' B' A'' B'' : Type*} [NonUnitalCStarAlgebra A'] [NonUnitalCStarAlgebra B']
  [NonUnitalCStarAlgebra A''] [NonUnitalCStarAlgebra B'']

open Algebra.TensorProduct (mapNonUnitalStarAlgHom mapNonUnitalStarAlgHom_tmul)

/-- **Functoriality of the minimal tensor product**: star homomorphisms `φ : A → A'` and
`ψ : B → B'` extend `φ ⊗ ψ` to a star homomorphism
`MinTensorProduct A B → MinTensorProduct A' B'`. -/
def map (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') :
    MinTensorProduct A B →⋆ₙₐ[ℂ] MinTensorProduct A' B' :=
  extend ((of (minCStarTensorNorm A' B')).comp (mapNonUnitalStarAlgHom φ ψ)) fun x ↦ by
    rw [NonUnitalStarAlgHom.comp_apply, norm_of]
    exact minTensorNorm_mapNonUnitalStarAlgHom_le φ ψ x

@[simp]
theorem map_of (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') (x : A ⊗[ℂ] B) :
    map φ ψ (of (minCStarTensorNorm A B) x) =
      of (minCStarTensorNorm A' B') (mapNonUnitalStarAlgHom φ ψ x) :=
  extend_of _ _ x

theorem map_of_tmul (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') (a : A) (b : B) :
    map φ ψ (of (minCStarTensorNorm A B) (a ⊗ₜ b)) =
      of (minCStarTensorNorm A' B') (φ a ⊗ₜ ψ b) := by
  rw [map_of, mapNonUnitalStarAlgHom_tmul]

/-- For injective `φ` and `ψ`, `map φ ψ` is isometric. -/
theorem norm_map {φ : A →⋆ₙₐ[ℂ] A'} {ψ : B →⋆ₙₐ[ℂ] B'} (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) (u : MinTensorProduct A B) : ‖map φ ψ u‖ = ‖u‖ :=
  norm_extend _ (fun x ↦ by
    rw [NonUnitalStarAlgHom.comp_apply, norm_of, minCStarTensorNorm_apply,
      minCStarTensorNorm_apply, minTensorNorm_mapNonUnitalStarAlgHom hφ hψ]) u

/-- **The minimal tensor product preserves injectivity**: for injective `φ` and `ψ`, `map φ ψ` is
injective. -/
theorem map_injective {φ : A →⋆ₙₐ[ℂ] A'} {ψ : B →⋆ₙₐ[ℂ] B'} (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) : Function.Injective (map φ ψ) :=
  (AddMonoidHomClass.isometry_of_norm _ (norm_map hφ hψ)).injective

@[simp]
theorem map_id :
    map (NonUnitalStarAlgHom.id ℂ A) (NonUnitalStarAlgHom.id ℂ B) =
      NonUnitalStarAlgHom.id ℂ (MinTensorProduct A B) :=
  starAlgHom_ext fun a b ↦ by simp

theorem map_comp (φ' : A' →⋆ₙₐ[ℂ] A'') (ψ' : B' →⋆ₙₐ[ℂ] B'') (φ : A →⋆ₙₐ[ℂ] A')
    (ψ : B →⋆ₙₐ[ℂ] B') : map (φ'.comp φ) (ψ'.comp ψ) = (map φ' ψ').comp (map φ ψ) :=
  starAlgHom_ext fun a b ↦ by simp

end Map

end MinTensorProduct

/-! ### The canonical surjection from the maximal tensor product -/

namespace MaxTensorProduct

open CStarTensorProduct

variable {A B}

/-- The canonical star homomorphism `MaxTensorProduct A B → MinTensorProduct A B`, extending the
identity of `A ⊗[ℂ] B`; it is bounded because `‖·‖_min ≤ ‖·‖_max`. -/
def toMin : MaxTensorProduct A B →⋆ₙₐ[ℂ] MinTensorProduct A B :=
  extend (of (minCStarTensorNorm A B)) fun x ↦ by
    rw [norm_of, minCStarTensorNorm_apply, maxCStarTensorNorm_apply]
    exact minTensorNorm_le_maxTensorNorm x

@[simp]
theorem toMin_of (x : A ⊗[ℂ] B) :
    toMin (of (maxCStarTensorNorm A B) x) = of (minCStarTensorNorm A B) x :=
  extend_of _ _ x

/-- **The canonical map `A ⊗max B → A ⊗min B` is surjective.** -/
theorem toMin_surjective : Function.Surjective (toMin (A := A) (B := B)) := by
  refine NonUnitalStarAlgHom.surjective_of_denseRange ?_
  refine (denseRange_of (N := minCStarTensorNorm A B)).mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨of (maxCStarTensorNorm A B) x, toMin_of x⟩

end MaxTensorProduct

end TauCeti

/-! ### Closed concrete operator algebras -/

namespace NonUnitalStarSubalgebra

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (A : NonUnitalStarSubalgebra ℂ (E →L[ℂ] E)) (B : NonUnitalStarSubalgebra ℂ (F →L[ℂ] F))

variable [IsClosed (A : Set (E →L[ℂ] E))] [IsClosed (B : Set (F →L[ℂ] F))]

/-- For closed concrete operator algebras, the norm of `x` in the spatial tensor product
`A ⊗_min B` is its minimal norm. -/
theorem norm_toMinTensor_eq_minTensorNorm (x : A ⊗[ℂ] B) :
    ‖toMinTensor A B x‖ = minTensorNorm A B x := by
  rw [norm_toMinTensor, minTensorNorm_eq_spatialNorm]

/-- The star homomorphism `MinTensorProduct A B → A ⊗_min B` extending the identity of
`A ⊗[ℂ] B`, for closed concrete operator algebras. -/
def minTensorProductToMinTensor : MinTensorProduct A B →⋆ₙₐ[ℂ] minTensor A B :=
  CStarTensorProduct.extend (toMinTensor A B) fun x ↦ (norm_toMinTensor_eq_minTensorNorm A B x).le

@[simp]
theorem minTensorProductToMinTensor_of (x : A ⊗[ℂ] B) :
    minTensorProductToMinTensor A B (CStarTensorProduct.of (minCStarTensorNorm A B) x) =
      toMinTensor A B x :=
  CStarTensorProduct.extend_of _ _ x

/-- The map `MinTensorProduct A B → A ⊗_min B` is isometric. -/
theorem norm_minTensorProductToMinTensor (u : MinTensorProduct A B) :
    ‖minTensorProductToMinTensor A B u‖ = ‖u‖ :=
  CStarTensorProduct.norm_extend _ (norm_toMinTensor_eq_minTensorNorm A B) u

theorem minTensorProductToMinTensor_bijective :
    Function.Bijective (minTensorProductToMinTensor A B) := by
  refine ⟨(AddMonoidHomClass.isometry_of_norm _
      (norm_minTensorProductToMinTensor A B)).injective,
    NonUnitalStarAlgHom.surjective_of_denseRange ?_⟩
  refine (denseRange_toMinTensor A B).mono ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨CStarTensorProduct.of (minCStarTensorNorm A B) x, minTensorProductToMinTensor_of A B x⟩

/-- For closed concrete operator algebras `A ⊆ B(E)` and `B ⊆ B(F)`, the minimal tensor product
`A ⊗min B` is isomorphic to the spatial tensor product `A ⊗_min B ⊆ B(E ⊗₂ F)`, compatibly with
the maps from `A ⊗[ℂ] B`. -/
def minTensorProductEquiv : MinTensorProduct A B ≃⋆ₐ[ℂ] minTensor A B :=
  StarAlgEquiv.ofBijective (minTensorProductToMinTensor A B)
    (minTensorProductToMinTensor_bijective A B)

@[simp]
theorem minTensorProductEquiv_of (x : A ⊗[ℂ] B) :
    minTensorProductEquiv A B (CStarTensorProduct.of (minCStarTensorNorm A B) x) =
      toMinTensor A B x :=
  minTensorProductToMinTensor_of A B x

end NonUnitalStarSubalgebra
