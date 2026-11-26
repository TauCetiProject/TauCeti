/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.Analysis.Normed.Module.NonUnitalSubalgebra
public import TauCeti.Analysis.CStarAlgebra.SpatialNorm.Independence

/-!
# Functoriality of the spatial tensor product

Let `A ⊆ B(E)`, `B ⊆ B(F)` be closed concrete C*-algebras and `A' ⊆ B(E')`, `B' ⊆ B(F')` concrete
operator algebras on complex Hilbert spaces. Star homomorphisms `φ : A → A'` and `ψ : B → B'`
induce the star homomorphism `φ ⊗ ψ : A ⊗[ℂ] B → A' ⊗[ℂ] B'`
(`Algebra.TensorProduct.mapNonUnitalStarAlgHom`). This file proves that it is **contractive for
the spatial norms**, `‖(φ ⊗ ψ)(x)‖_min ≤ ‖x‖_min`
(`NonUnitalStarSubalgebra.spatialNorm_mapNonUnitalStarAlgHom_le`), and **isometric** when `φ` and
`ψ` are injective (`NonUnitalStarSubalgebra.spatialNorm_mapNonUnitalStarAlgHom`). Both follow from
the representation independence of the spatial norm: the spatial operator of `(φ ⊗ ψ)(x)` is that of
`x` in the representations `A → A' ⊆ B(E')` and `B → B' ⊆ B(F')`, whose norm is at most `‖x‖_min`,
with equality for faithful representations.

So `φ ⊗ ψ` extends by continuity to a star homomorphism of spatial tensor products
`A ⊗_min B → A' ⊗_min B'` (`NonUnitalStarSubalgebra.minTensorMap`), contractive, isometric for
injective `φ` and `ψ`, and compatible with identities and composition. The extension itself is
constructed over `𝕜 = ℝ` or `ℂ` for any `φ`, `ψ` whose tensor product is contractive for the
spatial norms (`NonUnitalStarSubalgebra.minTensorMapOfLE`); only the contractivity uses
representation independence, which is proved over `ℂ`. For inclusions `A ≤ A₁` and `B ≤ B₁`,
`minTensorMap` is the inclusion `A ⊗_min B ⊆ A₁ ⊗_min B₁`.

## Main declarations

* `NonUnitalStarSubalgebra.spatialNorm_mapNonUnitalStarAlgHom_le`: `‖(φ ⊗ ψ)(x)‖_min ≤ ‖x‖_min`.
* `NonUnitalStarSubalgebra.spatialNorm_mapNonUnitalStarAlgHom`: equality for injective `φ`, `ψ`.
* `NonUnitalStarSubalgebra.minTensorMapOfLE φ ψ h`: the extension of a contractive `φ ⊗ ψ`.
* `NonUnitalStarSubalgebra.minTensorMap φ ψ`: the star homomorphism
  `A ⊗_min B → A' ⊗_min B'`, with `NonUnitalStarSubalgebra.minTensorMap_toMinTensor`,
  `NonUnitalStarSubalgebra.norm_minTensorMap_le`, `NonUnitalStarSubalgebra.norm_minTensorMap`,
  `NonUnitalStarSubalgebra.minTensorMap_injective`, `NonUnitalStarSubalgebra.minTensorMap_id`,
  `NonUnitalStarSubalgebra.minTensorMap_comp` and `NonUnitalStarSubalgebra.minTensorMap_inclusion`.
* `NonUnitalStarSubalgebra.minTensor_nonUnitalStarAlgHom_ext`: star homomorphisms from
  `A ⊗_min B` to a C*-algebra are determined on pure tensors `a ⊗ₜ b`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.5–II.9.2.6 (functoriality of C*-tensor products).
* M. Takesaki, *Theory of Operator Algebras I*, Chapter IV, §4 (Theorem IV.4.9 is the
  representation independence of the spatial norm).
-/

public section

noncomputable section

open UniformSpace TensorProduct ContinuousLinearMap

namespace NonUnitalStarSubalgebra

open TauCeti
open Algebra.TensorProduct (mapNonUnitalStarAlgHom coe_mapNonUnitalStarAlgHom
  mapNonUnitalStarAlgHom_tmul mapNonUnitalStarAlgHom_id mapNonUnitalStarAlgHom_comp)

section RCLike

variable {𝕜 E F E' F' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [CompleteSpace F']
  {A : NonUnitalStarSubalgebra 𝕜 (E →L[𝕜] E)} {B : NonUnitalStarSubalgebra 𝕜 (F →L[𝕜] F)}
  {A' : NonUnitalStarSubalgebra 𝕜 (E' →L[𝕜] E')} {B' : NonUnitalStarSubalgebra 𝕜 (F' →L[𝕜] F')}

/-! ### Tensor products of star homomorphisms -/

/-- The spatial operator of `(φ ⊗ ψ)(x)` is that of `x` in the representations
`A → A' ⊆ B(E')` and `B → B' ⊆ B(F')`. -/
theorem spatialTensorHom_mapNonUnitalStarAlgHom (φ : A →⋆ₙₐ[𝕜] A') (ψ : B →⋆ₙₐ[𝕜] B')
    (x : A ⊗[𝕜] B) :
    spatialTensorHom A' B' (mapNonUnitalStarAlgHom φ ψ x) =
      ((NonUnitalStarSubalgebraClass.subtype A').comp φ).spatialTensorHom
        ((NonUnitalStarSubalgebraClass.subtype B').comp ψ) x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    -- `map_add` on the bundled star homomorphism times out synthesizing `AddHomClass` for
    -- `A ⊗[𝕜] B →⋆ₙₐ[𝕜] A' ⊗[𝕜] B'`, so unfold it to the linear map `TensorProduct.map`.
    rw [coe_mapNonUnitalStarAlgHom] at hx hy ⊢
    rw [map_add, map_add, map_add, hx, hy]
  | tmul a b => simp

/-! ### Extension to the spatial tensor products -/

section OfLE

variable (φ : A →⋆ₙₐ[𝕜] A') (ψ : B →⋆ₙₐ[𝕜] B')
  (h : ∀ x, spatialNorm A' B' (mapNonUnitalStarAlgHom φ ψ x) ≤ spatialNorm A B x)

/-- The linear map `A ⊗[𝕜] B → B(E' ⊗₂ F')`, `x ↦ (φ ⊗ ψ)(x)`. -/
private def minTensorMapAux :
    A ⊗[𝕜] B →ₗ[𝕜] (Completion (E' ⊗[𝕜] F') →L[𝕜] Completion (E' ⊗[𝕜] F')) :=
  (LinearMap.ofClass (spatialTensorHom A' B') :
      A' ⊗[𝕜] B' →ₗ[𝕜] (Completion (E' ⊗[𝕜] F') →L[𝕜] Completion (E' ⊗[𝕜] F'))) ∘ₗ
    (LinearMap.ofClass (mapNonUnitalStarAlgHom φ ψ) : A ⊗[𝕜] B →ₗ[𝕜] A' ⊗[𝕜] B')

private theorem minTensorMapAux_apply (x : A ⊗[𝕜] B) :
    minTensorMapAux φ ψ x = spatialTensorHom A' B' (mapNonUnitalStarAlgHom φ ψ x) :=
  (rfl)

include h in
private theorem norm_minTensorMapAux_le (x : A ⊗[𝕜] B) :
    ‖minTensorMapAux φ ψ x‖ ≤
      1 * ‖(LinearMap.ofClass (toMinTensor A B) : A ⊗[𝕜] B →ₗ[𝕜] minTensor A B) x‖ := by
  rw [minTensorMapAux_apply, LinearMap.coe_ofClass, one_mul, norm_toMinTensor, ← spatialNorm_def]
  exact h x

/-- The bounded linear extension `A ⊗_min B → B(E' ⊗₂ F')` of `x ↦ (φ ⊗ ψ)(x)`. -/
private def minTensorMapCLM :
    minTensor A B →L[𝕜] (Completion (E' ⊗[𝕜] F') →L[𝕜] Completion (E' ⊗[𝕜] F')) :=
  (minTensorMapAux φ ψ).extendOfNorm (E := A ⊗[𝕜] B) (LinearMap.ofClass (toMinTensor A B))

include h in
private theorem minTensorMapCLM_toMinTensor (x : A ⊗[𝕜] B) :
    minTensorMapCLM φ ψ (toMinTensor A B x) =
      spatialTensorHom A' B' (mapNonUnitalStarAlgHom φ ψ x) :=
  LinearMap.extendOfNorm_eq (E := A ⊗[𝕜] B) (denseRange_toMinTensor A B)
    ⟨1, norm_minTensorMapAux_le φ ψ h⟩ x

include h in
private theorem minTensorMapCLM_toMinTensor' (x : A ⊗[𝕜] B) :
    minTensorMapCLM φ ψ (toMinTensor A B x) =
      ((NonUnitalStarSubalgebraClass.subtype A').comp φ).spatialTensorHom
        ((NonUnitalStarSubalgebraClass.subtype B').comp ψ) x := by
  rw [minTensorMapCLM_toMinTensor φ ψ h, spatialTensorHom_mapNonUnitalStarAlgHom]

include h in
private theorem minTensorMapCLM_mem (u : minTensor A B) :
    minTensorMapCLM φ ψ u ∈ minTensor A' B' := by
  refine (denseRange_toMinTensor A B).induction_on u
    ((isClosed_minTensor A' B').preimage (minTensorMapCLM φ ψ).continuous) fun x ↦ ?_
  rw [minTensorMapCLM_toMinTensor φ ψ h]
  exact spatialTensorHom_mem_minTensor A' B' _

include h in
private theorem minTensorMapCLM_mul (u v : minTensor A B) :
    minTensorMapCLM φ ψ (u * v) = minTensorMapCLM φ ψ u * minTensorMapCLM φ ψ v := by
  -- Both sides are jointly continuous in `(u, v)` and agree on the dense algebraic tensor
  -- product.
  have hd := (denseRange_toMinTensor A B).prodMap (denseRange_toMinTensor A B)
  have hc := (minTensorMapCLM φ ψ).continuous
  refine congrFun (hd.equalizer
    (g := fun p : minTensor A B × minTensor A B ↦ minTensorMapCLM φ ψ (p.1 * p.2))
    (h := fun p : minTensor A B × minTensor A B ↦
      minTensorMapCLM φ ψ p.1 * minTensorMapCLM φ ψ p.2)
    (hc.comp (continuous_fst.mul continuous_snd))
    ((hc.comp continuous_fst).mul (hc.comp continuous_snd)) (funext fun p ↦ ?_)) (u, v)
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd]
  rw [← map_mul (toMinTensor A B), minTensorMapCLM_toMinTensor' φ ψ h,
    minTensorMapCLM_toMinTensor' φ ψ h, minTensorMapCLM_toMinTensor' φ ψ h,
    map_mul (NonUnitalStarAlgHom.spatialTensorHom _ _)]

include h in
private theorem minTensorMapCLM_star (u : minTensor A B) :
    minTensorMapCLM φ ψ (star u) = star (minTensorMapCLM φ ψ u) := by
  have hc := (minTensorMapCLM φ ψ).continuous
  have hs : Continuous (star : minTensor A B → minTensor A B) :=
    continuous_induced_rng.2 continuous_subtypeVal.star
  refine congrFun (minTensor_funext (f := fun u ↦ minTensorMapCLM φ ψ (star u))
    (g := fun u ↦ star (minTensorMapCLM φ ψ u)) (hc.comp hs) hc.star
    fun x ↦ ?_) u
  rw [← map_star (toMinTensor A B), minTensorMapCLM_toMinTensor' φ ψ h,
    minTensorMapCLM_toMinTensor' φ ψ h, map_star (NonUnitalStarAlgHom.spatialTensorHom _ _)]

/-- The extension `A ⊗_min B → A' ⊗_min B'` of the tensor product `φ ⊗ ψ` of star homomorphisms,
when `φ ⊗ ψ` is contractive for the spatial norms. Over `ℂ`, with `A` and `B` closed, this always
holds (`NonUnitalStarSubalgebra.spatialNorm_mapNonUnitalStarAlgHom_le`), and
`NonUnitalStarSubalgebra.minTensorMap` is this extension. -/
def minTensorMapOfLE : minTensor A B →⋆ₙₐ[𝕜] minTensor A' B' where
  toFun u := ⟨minTensorMapCLM φ ψ u, minTensorMapCLM_mem φ ψ h u⟩
  map_smul' c u := Subtype.ext <| (minTensorMapCLM φ ψ).map_smul c u
  map_zero' := Subtype.ext <| (minTensorMapCLM φ ψ).map_zero
  map_add' u v := Subtype.ext <| (minTensorMapCLM φ ψ).map_add u v
  map_mul' u v := Subtype.ext <| minTensorMapCLM_mul φ ψ h u v
  map_star' u := Subtype.ext <| minTensorMapCLM_star φ ψ h u

private theorem coe_minTensorMapOfLE (u : minTensor A B) :
    (minTensorMapOfLE φ ψ h u : Completion (E' ⊗[𝕜] F') →L[𝕜] Completion (E' ⊗[𝕜] F')) =
      minTensorMapCLM φ ψ u :=
  (rfl)

/-- `minTensorMapOfLE φ ψ h` extends `φ ⊗ ψ`. -/
@[simp]
theorem minTensorMapOfLE_toMinTensor (x : A ⊗[𝕜] B) :
    minTensorMapOfLE φ ψ h (toMinTensor A B x) =
      toMinTensor A' B' (mapNonUnitalStarAlgHom φ ψ x) :=
  Subtype.ext <| (minTensorMapCLM_toMinTensor φ ψ h x).trans (coe_toMinTensor A' B' _).symm

/-- `minTensorMapOfLE φ ψ h` is continuous. -/
@[fun_prop]
theorem continuous_minTensorMapOfLE : Continuous (minTensorMapOfLE φ ψ h) :=
  (minTensorMapCLM φ ψ).continuous.subtype_mk _

/-- `minTensorMapOfLE φ ψ h` is contractive. -/
theorem norm_minTensorMapOfLE_le (u : minTensor A B) : ‖minTensorMapOfLE φ ψ h u‖ ≤ ‖u‖ := by
  rw [AddSubgroupClass.coe_norm, coe_minTensorMapOfLE]
  exact (LinearMap.norm_extendOfNorm_apply_le (E := A ⊗[𝕜] B) (denseRange_toMinTensor A B) 1
    (norm_minTensorMapAux_le φ ψ h) u).trans_eq (one_mul _)

/-- `minTensorMapOfLE φ ψ h` is the unique continuous map `A ⊗_min B → A' ⊗_min B'` extending
`φ ⊗ ψ`. -/
theorem eq_minTensorMapOfLE_iff {T : minTensor A B → minTensor A' B'} (hT : Continuous T) :
    T = ⇑(minTensorMapOfLE φ ψ h) ↔
      ∀ x, T (toMinTensor A B x) = toMinTensor A' B' (mapNonUnitalStarAlgHom φ ψ x) :=
  ⟨by rintro rfl x; exact minTensorMapOfLE_toMinTensor φ ψ h x, fun h' ↦
    minTensor_funext hT (continuous_minTensorMapOfLE φ ψ h) fun x ↦ by
      rw [h', minTensorMapOfLE_toMinTensor]⟩

end OfLE

end RCLike

/-! ### Functoriality over `ℂ` -/

section Complex

variable {E F E' F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [CompleteSpace E']
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F'] [CompleteSpace F']
  {A : NonUnitalStarSubalgebra ℂ (E →L[ℂ] E)} {B : NonUnitalStarSubalgebra ℂ (F →L[ℂ] F)}
  {A' : NonUnitalStarSubalgebra ℂ (E' →L[ℂ] E')} {B' : NonUnitalStarSubalgebra ℂ (F' →L[ℂ] F')}
  [IsClosed (A : Set (E →L[ℂ] E))] [IsClosed (B : Set (F →L[ℂ] F))]

/-- **The spatial norm is functorial**: star homomorphisms `φ : A → A'` and `ψ : B → B'` of
concrete operator algebras, with `A` and `B` closed, give `‖(φ ⊗ ψ)(x)‖_min ≤ ‖x‖_min`. -/
theorem spatialNorm_mapNonUnitalStarAlgHom_le (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B')
    (x : A ⊗[ℂ] B) :
    spatialNorm A' B' (mapNonUnitalStarAlgHom φ ψ x) ≤ spatialNorm A B x := by
  rw [spatialNorm_def, spatialTensorHom_mapNonUnitalStarAlgHom,
    NonUnitalStarAlgHom.spatialTensorHom_apply]
  exact norm_spatialTensorLinearMap_map_le_spatialNorm A B _ _ x

/-- **Injective star homomorphisms are isometric for the spatial norms**: for injective
`φ : A → A'` and `ψ : B → B'`, with `A` and `B` closed, `‖(φ ⊗ ψ)(x)‖_min = ‖x‖_min`. -/
theorem spatialNorm_mapNonUnitalStarAlgHom {φ : A →⋆ₙₐ[ℂ] A'} {ψ : B →⋆ₙₐ[ℂ] B'}
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) (x : A ⊗[ℂ] B) :
    spatialNorm A' B' (mapNonUnitalStarAlgHom φ ψ x) = spatialNorm A B x := by
  rw [spatialNorm_def, spatialTensorHom_mapNonUnitalStarAlgHom,
    NonUnitalStarAlgHom.spatialTensorHom_apply]
  exact norm_spatialTensorLinearMap_map_eq_spatialNorm A B _ _
    (Subtype.val_injective.comp hφ) (Subtype.val_injective.comp hψ) x

/-- **Functoriality of the spatial tensor product**: star homomorphisms `φ : A → A'` and
`ψ : B → B'`, with `A` and `B` closed, induce the star homomorphism
`A ⊗_min B → A' ⊗_min B'` extending `φ ⊗ ψ` on the algebraic tensor product. -/
def minTensorMap (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') : minTensor A B →⋆ₙₐ[ℂ] minTensor A' B' :=
  minTensorMapOfLE φ ψ (spatialNorm_mapNonUnitalStarAlgHom_le φ ψ)

/-- Unfolding `NonUnitalStarSubalgebra.minTensorMap`. -/
theorem minTensorMap_def (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') :
    minTensorMap φ ψ = minTensorMapOfLE φ ψ (spatialNorm_mapNonUnitalStarAlgHom_le φ ψ) :=
  (rfl)

/-- `minTensorMap φ ψ` extends `φ ⊗ ψ`: it sends `x ∈ A ⊗[ℂ] B` to `(φ ⊗ ψ)(x)`. -/
@[simp]
theorem minTensorMap_toMinTensor (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') (x : A ⊗[ℂ] B) :
    minTensorMap φ ψ (toMinTensor A B x) = toMinTensor A' B' (mapNonUnitalStarAlgHom φ ψ x) :=
  minTensorMapOfLE_toMinTensor φ ψ _ x

/-- `minTensorMap φ ψ` sends `a ⊗ b` to `φ a ⊗ ψ b`. -/
theorem minTensorMap_toMinTensor_tmul (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') (a : A) (b : B) :
    minTensorMap φ ψ (toMinTensor A B (a ⊗ₜ b)) = toMinTensor A' B' (φ a ⊗ₜ ψ b) := by
  rw [minTensorMap_toMinTensor, Algebra.TensorProduct.mapNonUnitalStarAlgHom_tmul]

/-- `minTensorMap φ ψ` is continuous. -/
@[fun_prop]
theorem continuous_minTensorMap (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') :
    Continuous (minTensorMap φ ψ) :=
  continuous_minTensorMapOfLE φ ψ _

/-- `minTensorMap φ ψ` is the unique continuous map `A ⊗_min B → A' ⊗_min B'` extending
`φ ⊗ ψ`. -/
theorem eq_minTensorMap_iff (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B')
    {T : minTensor A B → minTensor A' B'} (hT : Continuous T) :
    T = ⇑(minTensorMap φ ψ) ↔
      ∀ x, T (toMinTensor A B x) = toMinTensor A' B' (mapNonUnitalStarAlgHom φ ψ x) :=
  eq_minTensorMapOfLE_iff φ ψ _ hT

/-- **`minTensorMap` is contractive**: `‖(φ ⊗ ψ)(u)‖ ≤ ‖u‖` on `A ⊗_min B`. -/
theorem norm_minTensorMap_le (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') (u : minTensor A B) :
    ‖minTensorMap φ ψ u‖ ≤ ‖u‖ :=
  norm_minTensorMapOfLE_le φ ψ _ u

/-- **`minTensorMap` is isometric for injective star homomorphisms**: for injective `φ` and
`ψ`, `‖(φ ⊗ ψ)(u)‖ = ‖u‖` on `A ⊗_min B`. -/
theorem norm_minTensorMap {φ : A →⋆ₙₐ[ℂ] A'} {ψ : B →⋆ₙₐ[ℂ] B'} (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) (u : minTensor A B) : ‖minTensorMap φ ψ u‖ = ‖u‖ := by
  refine congrFun (minTensor_funext (f := fun u ↦ ‖minTensorMap φ ψ u‖) (g := fun u ↦ ‖u‖)
    (continuous_norm.comp (continuous_minTensorMap φ ψ)) continuous_norm fun x ↦ ?_) u
  rw [minTensorMap_toMinTensor, norm_toMinTensor, norm_toMinTensor,
    spatialNorm_mapNonUnitalStarAlgHom hφ hψ]

/-- For injective `φ` and `ψ`, `minTensorMap φ ψ` is injective. -/
theorem minTensorMap_injective {φ : A →⋆ₙₐ[ℂ] A'} {ψ : B →⋆ₙₐ[ℂ] B'}
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ) :
    Function.Injective (minTensorMap φ ψ) :=
  (injective_iff_map_eq_zero _).2 fun u hu ↦ by
    rwa [← norm_eq_zero, norm_minTensorMap hφ hψ, norm_eq_zero] at hu

/-- `minTensorMap` of the identities is the identity. -/
@[simp]
theorem minTensorMap_id :
    minTensorMap (NonUnitalStarAlgHom.id ℂ A) (NonUnitalStarAlgHom.id ℂ B) =
      NonUnitalStarAlgHom.id ℂ (minTensor A B) := by
  refine DFunLike.coe_injective <| minTensor_funext (continuous_minTensorMap _ _)
    continuous_id fun x ↦ ?_
  simp only [minTensorMap_toMinTensor, mapNonUnitalStarAlgHom_id, NonUnitalStarAlgHom.coe_id, id_eq]

/-- `minTensorMap` is compatible with composition. -/
theorem minTensorMap_comp {E'' F'' : Type*} [NormedAddCommGroup E''] [InnerProductSpace ℂ E'']
    [CompleteSpace E''] [NormedAddCommGroup F''] [InnerProductSpace ℂ F''] [CompleteSpace F'']
    {A'' : NonUnitalStarSubalgebra ℂ (E'' →L[ℂ] E'')}
    {B'' : NonUnitalStarSubalgebra ℂ (F'' →L[ℂ] F'')} [IsClosed (A' : Set (E' →L[ℂ] E'))]
    [IsClosed (B' : Set (F' →L[ℂ] F'))]
    (φ' : A' →⋆ₙₐ[ℂ] A'') (ψ' : B' →⋆ₙₐ[ℂ] B'') (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') :
    minTensorMap (φ'.comp φ) (ψ'.comp ψ) = (minTensorMap φ' ψ').comp (minTensorMap φ ψ) := by
  refine DFunLike.coe_injective <| minTensor_funext (continuous_minTensorMap _ _)
    ((continuous_minTensorMap _ _).comp (continuous_minTensorMap _ _)) fun x ↦ ?_
  simp [mapNonUnitalStarAlgHom_comp]

/-- For inclusions `A ≤ A₁` and `B ≤ B₁`, `minTensorMap` of the inclusions is the inclusion
`A ⊗_min B ⊆ A₁ ⊗_min B₁` (`NonUnitalStarSubalgebra.minTensor_mono`). -/
theorem minTensorMap_inclusion {A₁ : NonUnitalStarSubalgebra ℂ (E →L[ℂ] E)}
    {B₁ : NonUnitalStarSubalgebra ℂ (F →L[ℂ] F)} (hA : A ≤ A₁) (hB : B ≤ B₁) :
    minTensorMap (inclusion hA) (inclusion hB) = inclusion (minTensor_mono hA hB) := by
  refine DFunLike.coe_injective ((eq_minTensorMap_iff _ _ (T := inclusion (minTensor_mono hA hB))
    (continuous_induced_rng.2 continuous_subtypeVal)).2 fun x ↦ Subtype.ext ?_).symm
  have hA' : (NonUnitalStarSubalgebraClass.subtype A₁).comp (inclusion hA) =
      NonUnitalStarSubalgebraClass.subtype A :=
    NonUnitalStarAlgHom.ext (val_inclusion hA)
  have hB' : (NonUnitalStarSubalgebraClass.subtype B₁).comp (inclusion hB) =
      NonUnitalStarSubalgebraClass.subtype B :=
    NonUnitalStarAlgHom.ext (val_inclusion hB)
  rw [val_inclusion, coe_toMinTensor, coe_toMinTensor, spatialTensorHom_mapNonUnitalStarAlgHom,
    hA', hB', spatialTensorHom_def]

omit [IsClosed (A : Set (E →L[ℂ] E))] [IsClosed (B : Set (F →L[ℂ] F))] in
open scoped CStarAlgebra in
/-- Two star homomorphisms from `A ⊗_min B` to a C*-algebra agree when they agree on pure tensors
`a ⊗ₜ b`: such star homomorphisms are continuous, and `A ⊗_min B` is a C*-algebra. -/
@[ext]
theorem minTensor_nonUnitalStarAlgHom_ext {G : Type*} [NonUnitalCStarAlgebra G]
    {f g : minTensor A B →⋆ₙₐ[ℂ] G}
    (h : ∀ a b, f (toMinTensor A B (a ⊗ₜ b)) = g (toMinTensor A B (a ⊗ₜ b))) : f = g := by
  have hc (f : minTensor A B →⋆ₙₐ[ℂ] G) : Continuous f := by
    have := isClosed_minTensor A B
    exact map_continuous f
  exact DFunLike.coe_injective congr(⇑$(minTensor_continuousLinearMap_ext
    (f := ⟨LinearMap.ofClass f, hc f⟩) (g := ⟨LinearMap.ofClass g, hc g⟩) h))

end Complex

end NonUnitalStarSubalgebra
