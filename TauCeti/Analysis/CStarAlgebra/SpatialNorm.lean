/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
public import TauCeti.Algebra.Star.TensorProductLift
public import TauCeti.Analysis.InnerProductSpace.TensorProduct.Completion
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic

/-!
# The spatial C*-norm on an algebraic tensor product of operator algebras

Let `E` and `F` be Hilbert spaces over `𝕜 = ℝ` or `ℂ`, with completed Hilbert tensor product
`E ⊗₂ F = Completion (E ⊗[𝕜] F)`. A bounded operator `a` on `E` and a bounded operator `b` on `F`
give the bounded operator `a ⊗ b = TensorProduct.mapLCompletion a b` on `E ⊗₂ F`. For concrete
operator algebras `A ⊆ B(E)` and `B ⊆ B(F)` (star subalgebras), these operators form the star
homomorphism `A ⊗[𝕜] B → B(E ⊗₂ F)`, `a ⊗ b ↦ a ⊗ b` (`TauCeti.spatialTensorHom A B`): it is the
product of the amplifications `a ⊗ 1` and `1 ⊗ b`, which commute.

This homomorphism is **injective** (`TauCeti.spatialTensorHom_injective`). For the full operator
algebras, write `x = Σᵢ aᵢ ⊗ cᵢ` along a basis `(cᵢ)` of `B(F)`; testing `x` on vectors
`ξ ⊗ η` against `ξ' ⊗ η'` gives `⟪η', (Σᵢ ⟪ξ', aᵢ ξ⟫ cᵢ) η⟫ = 0`, so every `⟪ξ', aᵢ ξ⟫` vanishes
and so does every `aᵢ`. For subalgebras, the inclusion `A ⊗[𝕜] B → B(E) ⊗[𝕜] B(F)` is injective
because vector spaces are flat.

So `‖x‖_min = ‖(spatialTensorHom A B) x‖` is a norm on `A ⊗[𝕜] B` (`TauCeti.spatialNorm`), the
**spatial** (or minimal) C*-norm: it is submultiplicative, satisfies the C*-identity
`‖x⋆ x‖_min = ‖x‖_min ^ 2`, and `‖a ⊗ b‖_min = ‖a‖ ‖b‖`. The **spatial tensor product**
`A ⊗_min B` (`TauCeti.minTensor A B`) is the norm closure of the image, a closed star subalgebra of
`B(E ⊗₂ F)`.

## Main declarations

* `TauCeti.spatialTensorHom A B`: the star homomorphism `A ⊗[𝕜] B → B(E ⊗₂ F)`, with
  `TauCeti.spatialTensorHom_tmul` and `TauCeti.spatialTensorHom_injective`.
* `TauCeti.spatialNorm A B`: the spatial norm, with `TauCeti.spatialNorm_eq_zero_iff`,
  `TauCeti.spatialNorm_add_le`, `TauCeti.spatialNorm_smul`, `TauCeti.spatialNorm_mul_le`,
  `TauCeti.spatialNorm_star_mul_self` and `TauCeti.spatialNorm_tmul`.
* `TauCeti.minTensor A B`: the spatial tensor product `A ⊗_min B`, with
  `TauCeti.isClosed_minTensor` and `TauCeti.mapLCompletion_mem_minTensor`.

## References

* M. Takesaki, *Theory of Operator Algebras I*, Springer, 1979, Chapter IV, §4.
-/

public section

noncomputable section

open UniformSpace TensorProduct ContinuousLinearMap
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-! ### The full operator algebras -/

variable (𝕜 E F) in
/-- The linear map `B(E) ⊗[𝕜] B(F) → B(E ⊗₂ F)`, `a ⊗ b ↦ a ⊗ b`. -/
def spatialTensorLinearMap :
    (E →L[𝕜] E) ⊗[𝕜] (F →L[𝕜] F) →ₗ[𝕜] Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F) :=
  TensorProduct.lift <| LinearMap.mk₂ 𝕜 mapLCompletion mapLCompletion_add_left
    mapLCompletion_smul_left mapLCompletion_add_right mapLCompletion_smul_right

@[simp]
theorem spatialTensorLinearMap_tmul (a : E →L[𝕜] E) (b : F →L[𝕜] F) :
    spatialTensorLinearMap 𝕜 E F (a ⊗ₜ b) = mapLCompletion a b :=
  (rfl)

/-- Testing `a ⊗ b` on `ξ ⊗ η` against `ξ' ⊗ η'` gives `⟪ξ', a ξ⟫ ⟪η', b η⟫`: for every `x`, the
matrix coefficient of `spatialTensorLinearMap x` is that of the operator on `F` obtained by
applying the vector functional `a ↦ ⟪ξ', a ξ⟫` to the first factor of `x`. -/
private theorem inner_spatialTensorLinearMap (ξ ξ' : E) (η η' : F)
    (x : (E →L[𝕜] E) ⊗[𝕜] (F →L[𝕜] F)) :
    ⟪((ξ' ⊗ₜ η' : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)),
        spatialTensorLinearMap 𝕜 E F x ((ξ ⊗ₜ η : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F))⟫_𝕜 =
      ⟪η', TensorProduct.lid 𝕜 (F →L[𝕜] F)
        (LinearMap.rTensor (F →L[𝕜] F)
          ((innerₛₗ 𝕜 ξ').comp (LinearMap.applyₗ (R := 𝕜) ξ ∘ₗ
            (ContinuousLinearMap.coeLM 𝕜 : (E →L[𝕜] E) →ₗ[𝕜] E →ₗ[𝕜] E))) x) η⟫_𝕜 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, add_apply, inner_add_right, hx, hy]
  | tmul a b =>
    simp [UniformSpace.Completion.inner_coe, inner_smul_right]

/-- **Injectivity of the spatial tensor map** on the full operator algebras. -/
theorem spatialTensorLinearMap_injective :
    Function.Injective (spatialTensorLinearMap 𝕜 E F) := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  let c := Module.Free.chooseBasis 𝕜 (F →L[𝕜] F)
  set m := TensorProduct.equivFinsuppOfBasisRight c x with hm
  have hxm : x = m.sum fun i a ↦ a ⊗ₜ c i := by
    rw [hm, ← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  suffices m = 0 by
    rw [hxm, this, Finsupp.sum_zero_index]
  refine Finsupp.ext fun i ↦ ContinuousLinearMap.ext fun ξ ↦ ext_inner_left 𝕜 fun ξ' ↦ ?_
  let ω : (E →L[𝕜] E) →ₗ[𝕜] 𝕜 := (innerₛₗ 𝕜 ξ').comp (LinearMap.applyₗ (R := 𝕜) ξ ∘ₗ
    (ContinuousLinearMap.coeLM 𝕜 : (E →L[𝕜] E) →ₗ[𝕜] E →ₗ[𝕜] E))
  have hω : TensorProduct.lid 𝕜 (F →L[𝕜] F) (LinearMap.rTensor (F →L[𝕜] F) ω x) = 0 := by
    refine ContinuousLinearMap.ext fun η ↦ ext_inner_left 𝕜 (E := F) fun η' ↦ ?_
    rw [← inner_spatialTensorLinearMap, hx]
    simp
  rw [hxm, map_finsuppSum, map_finsuppSum] at hω
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at hω
  have hrepr := congrArg (fun y ↦ c.repr y i) hω
  simp [map_finsuppSum, Finsupp.sum_apply, Finsupp.single_apply] at hrepr
  by_cases hi : m i = 0
  · simp [hi]
  · simpa [ω] using hrepr hi

/-! ### Concrete operator algebras -/

variable [CompleteSpace E] [CompleteSpace F]
  (A : StarSubalgebra 𝕜 (E →L[𝕜] E)) (B : StarSubalgebra 𝕜 (F →L[𝕜] F))

/-- The **spatial tensor homomorphism** of concrete operator algebras `A ⊆ B(E)` and
`B ⊆ B(F)`: the star homomorphism `A ⊗[𝕜] B → B(E ⊗₂ F)`, `a ⊗ b ↦ a ⊗ b`, the product of the
commuting amplifications `a ⊗ 1` and `1 ⊗ b`. -/
def spatialTensorHom :
    A ⊗[𝕜] B →⋆ₙₐ[𝕜] (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F)) :=
  Algebra.TensorProduct.liftNonUnitalStarAlgHom
    ((rTensorCompletionStarAlgHom 𝕜 E F).comp A.subtype).toNonUnitalStarAlgHom
    ((lTensorCompletionStarAlgHom 𝕜 E F).comp B.subtype).toNonUnitalStarAlgHom
    fun a b ↦ by
      simpa using commute_rTensorCompletion_lTensorCompletion (a : E →L[𝕜] E) (b : F →L[𝕜] F)

/-- The spatial tensor homomorphism sends `a ⊗ b` to the operator `a ⊗ b`. -/
@[simp]
theorem spatialTensorHom_tmul (a : A) (b : B) :
    spatialTensorHom A B (a ⊗ₜ b) = mapLCompletion (a : E →L[𝕜] E) (b : F →L[𝕜] F) := by
  simp [spatialTensorHom, ContinuousLinearMap.mul_def, rTensorCompletion_comp_lTensorCompletion]

/-- The spatial tensor homomorphism factors through the full operator algebras. -/
theorem spatialTensorHom_apply (x : A ⊗[𝕜] B) :
    spatialTensorHom A B x =
      spatialTensorLinearMap 𝕜 E F
        (TensorProduct.map A.subtype.toLinearMap B.subtype.toLinearMap x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul a b => simp

/-- **The spatial tensor homomorphism is injective.** -/
theorem spatialTensorHom_injective : Function.Injective (spatialTensorHom A B) := by
  have h := spatialTensorLinearMap_injective.comp (TensorProduct.map_injective_of_flat_flat
    A.subtype.toLinearMap B.subtype.toLinearMap Subtype.val_injective Subtype.val_injective)
  intro x y hxy
  rw [spatialTensorHom_apply, spatialTensorHom_apply] at hxy
  exact h hxy

/-! ### The spatial norm -/

/-- The **spatial norm** `‖x‖_min = ‖(spatialTensorHom A B) x‖` on `A ⊗[𝕜] B`, the norm of the
operator on `E ⊗₂ F`. -/
def spatialNorm (x : A ⊗[𝕜] B) : ℝ :=
  ‖spatialTensorHom A B x‖

/-- Unfolding `TauCeti.spatialNorm`. -/
theorem spatialNorm_def (x : A ⊗[𝕜] B) : spatialNorm A B x = ‖spatialTensorHom A B x‖ :=
  (rfl)

/-- The spatial norm is nonnegative. -/
theorem spatialNorm_nonneg (x : A ⊗[𝕜] B) : 0 ≤ spatialNorm A B x :=
  norm_nonneg _

/-- **The spatial norm is definite**, by injectivity of the spatial tensor homomorphism. -/
@[simp]
theorem spatialNorm_eq_zero_iff {x : A ⊗[𝕜] B} : spatialNorm A B x = 0 ↔ x = 0 := by
  rw [spatialNorm_def, norm_eq_zero,
    (injective_iff_map_eq_zero' _).1 (spatialTensorHom_injective A B)]

/-- The triangle inequality for the spatial norm. -/
theorem spatialNorm_add_le (x y : A ⊗[𝕜] B) :
    spatialNorm A B (x + y) ≤ spatialNorm A B x + spatialNorm A B y := by
  simpa only [spatialNorm_def, map_add] using norm_add_le _ _

/-- Homogeneity of the spatial norm. -/
theorem spatialNorm_smul (c : 𝕜) (x : A ⊗[𝕜] B) :
    spatialNorm A B (c • x) = ‖c‖ * spatialNorm A B x := by
  simp only [spatialNorm_def, map_smul, norm_smul]

/-- **The spatial norm is submultiplicative.** -/
theorem spatialNorm_mul_le (x y : A ⊗[𝕜] B) :
    spatialNorm A B (x * y) ≤ spatialNorm A B x * spatialNorm A B y := by
  simpa only [spatialNorm_def, map_mul] using norm_mul_le _ _

/-- **The C*-identity for the spatial norm**: `‖x⋆ x‖_min = ‖x‖_min ^ 2`. -/
theorem spatialNorm_star_mul_self (x : A ⊗[𝕜] B) :
    spatialNorm A B (star x * x) = spatialNorm A B x ^ 2 := by
  rw [spatialNorm_def, spatialNorm_def, map_mul, map_star, sq]
  exact CStarRing.norm_star_mul_self

/-- **The spatial norm is a cross norm**: `‖a ⊗ b‖_min = ‖a‖ ‖b‖`. -/
@[simp]
theorem spatialNorm_tmul (a : A) (b : B) : spatialNorm A B (a ⊗ₜ b) = ‖a‖ * ‖b‖ := by
  rw [spatialNorm_def, spatialTensorHom_tmul, norm_mapLCompletion]
  rfl

/-! ### The spatial tensor product -/

/-- The **spatial tensor product** `A ⊗_min B`: the norm closure in `B(E ⊗₂ F)` of the image of the
algebraic tensor product `A ⊗[𝕜] B`, a closed star subalgebra. -/
def minTensor : NonUnitalStarSubalgebra 𝕜 (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F)) :=
  (NonUnitalStarAlgHom.range (spatialTensorHom A B)).topologicalClosure

/-- The spatial tensor product is closed. -/
theorem isClosed_minTensor :
    IsClosed (minTensor A B : Set (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F))) :=
  NonUnitalStarSubalgebra.isClosed_topologicalClosure _

/-- The spatial tensor product contains the image of the algebraic tensor product. -/
theorem spatialTensorHom_mem_minTensor (x : A ⊗[𝕜] B) : spatialTensorHom A B x ∈ minTensor A B :=
  NonUnitalStarSubalgebra.le_topologicalClosure _ ⟨x, rfl⟩

/-- The spatial tensor product contains the operators `a ⊗ b` for `a ∈ A` and `b ∈ B`. -/
theorem mapLCompletion_mem_minTensor {a : E →L[𝕜] E} {b : F →L[𝕜] F} (ha : a ∈ A) (hb : b ∈ B) :
    mapLCompletion a b ∈ minTensor A B := by
  simpa using spatialTensorHom_mem_minTensor A B (⟨a, ha⟩ ⊗ₜ ⟨b, hb⟩)

end TauCeti
