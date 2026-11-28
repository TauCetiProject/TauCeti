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
`TauCeti.MinTensorProduct.map_injective`), and surjective when `φ` and `ψ` are surjective
(`TauCeti.MinTensorProduct.map_surjective`). Its range is the closure of the image of the
algebraic tensor product (`TauCeti.MinTensorProduct.range_map`), and star isomorphisms induce
star isomorphisms (`TauCeti.MinTensorProduct.congr`).

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
* `TauCeti.MinTensorProduct.congr`: the star isomorphism induced by star isomorphisms.
* `TauCeti.MaxTensorProduct.toMin`: the canonical surjection `A ⊗max B → A ⊗min B`.

## Main statements

* `TauCeti.MinTensorProduct.map_injective`: `map φ ψ` is injective for injective `φ`, `ψ`.
* `TauCeti.MinTensorProduct.map_surjective`: `map φ ψ` is surjective for surjective `φ`, `ψ`.
* `TauCeti.MinTensorProduct.range_map`: the range of `map φ ψ` is the closure of the image of
  the algebraic tensor product.

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
  star_mul_self_le' x := (minTensorNorm_star_mul_self x).ge

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

/-- `‖a ⊗ b‖ = ‖a‖ ‖b‖` in `MinTensorProduct A B`. -/
theorem norm_of_tmul (a : A) (b : B) :
    ‖of (minCStarTensorNorm A B) (a ⊗ₜ b)‖ = ‖a‖ * ‖b‖ := by
  rw [norm_of, minCStarTensorNorm_apply, minTensorNorm_tmul]

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
  extend_injective _ fun x ↦ (minTensorNorm_eq_norm_spatialTensorHom hπ hρ x).symm

end Spatial

/-! ### Functoriality -/

section Map

variable {A' B' A'' B'' : Type*} [NonUnitalCStarAlgebra A'] [NonUnitalCStarAlgebra B']
  [NonUnitalCStarAlgebra A''] [NonUnitalCStarAlgebra B'']

open Algebra.TensorProduct (mapNonUnitalStarAlgHom mapNonUnitalStarAlgHom_tmul)
open scoped _root_.CStarAlgebra

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
  extend_injective _ fun x ↦ by simpa using norm_map hφ hψ (of _ x)

@[simp]
theorem map_id :
    map (NonUnitalStarAlgHom.id ℂ A) (NonUnitalStarAlgHom.id ℂ B) =
      NonUnitalStarAlgHom.id ℂ (MinTensorProduct A B) :=
  starAlgHom_ext fun a b ↦ by simp

theorem map_comp (φ' : A' →⋆ₙₐ[ℂ] A'') (ψ' : B' →⋆ₙₐ[ℂ] B'') (φ : A →⋆ₙₐ[ℂ] A')
    (ψ : B →⋆ₙₐ[ℂ] B') : map (φ'.comp φ) (ψ'.comp ψ) = (map φ' ψ').comp (map φ ψ) :=
  starAlgHom_ext fun a b ↦ by simp

/-- Composition of the maps of minimal tensor products, elementwise. -/
theorem map_map (φ' : A' →⋆ₙₐ[ℂ] A'') (ψ' : B' →⋆ₙₐ[ℂ] B'') (φ : A →⋆ₙₐ[ℂ] A')
    (ψ : B →⋆ₙₐ[ℂ] B') (u : MinTensorProduct A B) :
    map φ' ψ' (map φ ψ u) = map (φ'.comp φ) (ψ'.comp ψ) u := by
  rw [map_comp, NonUnitalStarAlgHom.comp_apply]

/-- Star isomorphisms `e : A ≃ A'` and `f : B ≃ B'` induce a star isomorphism
`A ⊗min B ≃ A' ⊗min B'`, sending `a ⊗ b` to `e a ⊗ f b`. -/
def congr (e : A ≃⋆ₐ[ℂ] A') (f : B ≃⋆ₐ[ℂ] B') :
    MinTensorProduct A B ≃⋆ₐ[ℂ] MinTensorProduct A' B' :=
  .ofNonUnitalStarAlgHom (map e.toNonUnitalStarAlgHom f.toNonUnitalStarAlgHom)
    (map e.symm.toNonUnitalStarAlgHom f.symm.toNonUnitalStarAlgHom)
    (starAlgHom_ext fun a b ↦ by simp) (starAlgHom_ext fun a b ↦ by simp)

/-- The induced isomorphism is the map induced by the underlying star homomorphisms. -/
@[simp]
theorem congr_apply (e : A ≃⋆ₐ[ℂ] A') (f : B ≃⋆ₐ[ℂ] B') (x : MinTensorProduct A B) :
    congr e f x = map e.toNonUnitalStarAlgHom f.toNonUnitalStarAlgHom x :=
  (rfl)

/-- The inverse of the induced isomorphism is induced by the inverses. -/
@[simp]
theorem congr_symm (e : A ≃⋆ₐ[ℂ] A') (f : B ≃⋆ₐ[ℂ] B') :
    (congr e f).symm = congr e.symm f.symm :=
  StarAlgEquiv.symm_ofNonUnitalStarAlgHom _ _ _ _

/-- The identities induce the identity. -/
@[simp]
theorem congr_refl :
    congr (.refl ℂ A) (.refl ℂ B) = StarAlgEquiv.refl ℂ (MinTensorProduct A B) :=
  StarAlgEquiv.ext fun x ↦ by simp

/-- The isomorphism induced by composites is the composite of the induced isomorphisms. -/
theorem congr_trans (e : A ≃⋆ₐ[ℂ] A') (f : B ≃⋆ₐ[ℂ] B') (e' : A' ≃⋆ₐ[ℂ] A'')
    (f' : B' ≃⋆ₐ[ℂ] B'') : (congr e f).trans (congr e' f') = congr (e.trans e') (f.trans f') :=
  StarAlgEquiv.ext fun x ↦ by simp [map_map]

/-- `map 0 ψ = 0`. -/
@[simp]
theorem map_zero_left (ψ : B →⋆ₙₐ[ℂ] B') :
    map (0 : A →⋆ₙₐ[ℂ] A') ψ = 0 :=
  starAlgHom_ext fun a b ↦ by simp

/-- `map φ 0 = 0`. -/
@[simp]
theorem map_zero_right (φ : A →⋆ₙₐ[ℂ] A') :
    map φ (0 : B →⋆ₙₐ[ℂ] B') = 0 :=
  starAlgHom_ext fun a b ↦ by simp

/-- The range of `map φ ψ` is the closure of the image of `A ⊗[ℂ] B`, that is, of
`φ(A) ⊗ ψ(B)`. -/
theorem range_map (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') :
    Set.range (map φ ψ) =
      closure (Set.range fun x ↦ of (minCStarTensorNorm A' B') (mapNonUnitalStarAlgHom φ ψ x)) := by
  refine subset_antisymm ?_ <| closure_minimal ?_ (map φ ψ).isClosed_setRange
  · have hc : Continuous (map φ ψ) := map_continuous _
    refine (hc.range_subset_closure_image_dense denseRange_of).trans ?_
    rw [← Set.range_comp]
    exact closure_mono fun _ ⟨x, hx⟩ ↦ ⟨x, (map_of φ ψ x).symm.trans hx⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨of _ x, map_of φ ψ x⟩

/-- For surjective `φ` and `ψ`, `map φ ψ` is surjective. -/
theorem map_surjective {φ : A →⋆ₙₐ[ℂ] A'} {ψ : B →⋆ₙₐ[ℂ] B'} (hφ : Function.Surjective φ)
    (hψ : Function.Surjective ψ) : Function.Surjective (map φ ψ) := by
  have h : Function.Surjective (mapNonUnitalStarAlgHom φ ψ) := by
    rw [Algebra.TensorProduct.coe_mapNonUnitalStarAlgHom]
    exact TensorProduct.map_surjective hφ hψ
  exact extend_surjective _ _ <| by
    rw [DenseRange, NonUnitalStarAlgHom.coe_comp, h.range_comp]
    exact denseRange_of

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
theorem toMin_surjective : Function.Surjective (toMin (A := A) (B := B)) :=
  extend_surjective _ _ denseRange_of

end MaxTensorProduct

end TauCeti

/-! ### Closed concrete operator algebras -/

namespace NonUnitalStarSubalgebra

open TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  (A : NonUnitalStarSubalgebra ℂ (E →L[ℂ] E)) (B : NonUnitalStarSubalgebra ℂ (F →L[ℂ] F))

variable [IsClosed (A : Set (E →L[ℂ] E))] [IsClosed (B : Set (F →L[ℂ] F))]

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
    Function.Bijective (minTensorProductToMinTensor A B) :=
  ⟨CStarTensorProduct.extend_injective _ (norm_toMinTensor_eq_minTensorNorm A B),
    CStarTensorProduct.extend_surjective _ _ (denseRange_toMinTensor A B)⟩

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
