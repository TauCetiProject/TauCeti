/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.Analysis.CStarAlgebra.SpatialNorm
public import TauCeti.Analysis.InnerProductSpace.LinearMap
public import TauCeti.Analysis.Normed.Module.NonUnitalSubalgebra
public import TauCeti.LinearAlgebra.TensorProduct.Basic

/-!
# Slice maps of the spatial tensor product

Let `A ⊆ B(E)` and `B ⊆ B(F)` be concrete operator algebras with spatial tensor product
`A ⊗_min B`. For a bounded linear functional `ψ` on `B`, the **right slice map** `R_ψ` sends
`a ⊗ b` to `ψ(b) a`; on the algebraic tensor product it is the right tensor component
`LinearMap.tensorComponent ψ`. It satisfies `‖R_ψ x‖ ≤ ‖ψ‖ ‖x‖_min`
(`NonUnitalStarSubalgebra.norm_tensorComponent_le`). For vectors `ξ`, `η` of `E` the matrix
coefficient `⟪η, R_ψ(x) ξ⟫` is `ψ` applied to the left slice of `x` by the vector functional
`a ↦ ⟪η, a ξ⟫` of `A`, and that slice is the operator `TensorProduct.sliceLeft ξ η` applied to
the image of `x` in `B(E ⊗₂ F)`, whose norm is at most `‖ξ‖ ‖η‖ ‖x‖_min`. So the bound holds for
every bounded functional, with no positivity or decomposition into positive functionals.

When `A` is complete (a C*-subalgebra), `R_ψ` therefore extends to a bounded operator
`A ⊗_min B → A` (`NonUnitalStarSubalgebra.minSliceRight`) of norm at most `‖ψ‖`, with equality
when `A ≠ 0` (`NonUnitalStarSubalgebra.norm_minSliceRight`), tested on `a ⊗ b` for a nonzero
`a`; when `A = 0` its norm is `0`. Symmetrically, a bounded functional `φ` on `A` gives the left
slice map `L_φ : A ⊗_min B → B`, `a ⊗ b ↦ φ(a) b` (`NonUnitalStarSubalgebra.minSliceLeft`),
which on the algebraic tensor product is `LinearMap.tensorComponent φ` after
`TensorProduct.comm`.

## Main declarations

* `NonUnitalStarSubalgebra.norm_tensorComponent_le`,
  `NonUnitalStarSubalgebra.norm_tensorComponent_comm_le`: `‖R_ψ x‖ ≤ ‖ψ‖ ‖x‖_min` and
  `‖L_φ x‖ ≤ ‖φ‖ ‖x‖_min` on the algebraic tensor product.
* `NonUnitalStarSubalgebra.minSliceRight`, `NonUnitalStarSubalgebra.minSliceLeft`: their bounded
  extensions to `A ⊗_min B`, with `NonUnitalStarSubalgebra.norm_minSliceRight` and
  `NonUnitalStarSubalgebra.norm_minSliceLeft`, and characterized as the unique such extensions
  by `NonUnitalStarSubalgebra.eq_minSliceRight_iff` and
  `NonUnitalStarSubalgebra.eq_minSliceLeft_iff`. They are linear in the functional
  (`NonUnitalStarSubalgebra.minSliceRight_zero`, `_add`, `_smul`, and the `minSliceLeft`
  versions).

## References

* M. Takesaki, *Theory of Operator Algebras I*, Chapter IV, §4.
-/

public section

noncomputable section

open UniformSpace TensorProduct
open LinearMap (tensorComponent tensorComponent_tmul)
open scoped InnerProductSpace

namespace NonUnitalStarSubalgebra

open TauCeti

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
  (A : NonUnitalStarSubalgebra 𝕜 (E →L[𝕜] E)) (B : NonUnitalStarSubalgebra 𝕜 (F →L[𝕜] F))

/-! ### Slice maps on the algebraic tensor product

The right slice map `a ⊗ b ↦ ψ(b) a` of a linear functional `ψ` on `B` is the right tensor
component `LinearMap.tensorComponent ψ : A ⊗[𝕜] B →ₗ[𝕜] A`, and the left slice map
`a ⊗ b ↦ φ(a) b` of a linear functional `φ` on `A` is `LinearMap.tensorComponent φ` after
`TensorProduct.comm 𝕜 A B`. -/

variable {A B}

/-- The vector functional `a ↦ ⟪η, a ξ⟫` on a concrete operator algebra. -/
private def vectorFunctionalₗ (C : NonUnitalStarSubalgebra 𝕜 (E →L[𝕜] E)) (ξ η : E) :
    C →ₗ[𝕜] 𝕜 :=
  (vectorFunctional ξ η : (E →L[𝕜] E) →L[𝕜] 𝕜).toLinearMap ∘ₗ
    (NonUnitalStarSubalgebraClass.subtype C : C →ₗ[𝕜] E →L[𝕜] E)

private theorem vectorFunctionalₗ_apply (C : NonUnitalStarSubalgebra 𝕜 (E →L[𝕜] E)) (ξ η : E)
    (c : C) : vectorFunctionalₗ C ξ η c = ⟪η, (c : E →L[𝕜] E) ξ⟫_𝕜 := by
  simp [vectorFunctionalₗ, vectorFunctional_apply]

/-- The left slice by a vector functional of `A` is the operator slice
`TensorProduct.sliceLeft ξ η` of the spatial tensor operator. -/
private theorem coe_tensorComponent_comm_vectorFunctionalₗ (ξ η : E) (x : A ⊗[𝕜] B) :
    ((tensorComponent (vectorFunctionalₗ A ξ η) (TensorProduct.comm 𝕜 A B x) : B) :
        F →L[𝕜] F) =
      TensorProduct.sliceLeft ξ η (spatialTensorHom A B x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [vectorFunctionalₗ_apply]
  | add x y hx hy => simp only [map_add, AddMemClass.coe_add, hx, hy]

/-- The right slice by a vector functional of `B` is the operator slice
`TensorProduct.sliceRight ξ η` of the spatial tensor operator. -/
private theorem coe_tensorComponent_vectorFunctionalₗ (ξ η : F) (x : A ⊗[𝕜] B) :
    ((tensorComponent (vectorFunctionalₗ B ξ η) x : A) : E →L[𝕜] E) =
      TensorProduct.sliceRight ξ η (spatialTensorHom A B x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [vectorFunctionalₗ_apply]
  | add x y hx hy => simp only [map_add, AddMemClass.coe_add, hx, hy]

/-- Matrix coefficients of a right slice are values of `ψ` on left vector slices. -/
private theorem inner_tensorComponent (ψ : B →ₗ[𝕜] 𝕜) (ξ η : E) (x : A ⊗[𝕜] B) :
    ⟪η, ((tensorComponent ψ x : A) : E →L[𝕜] E) ξ⟫_𝕜 =
      ψ (tensorComponent (vectorFunctionalₗ A ξ η) (TensorProduct.comm 𝕜 A B x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [vectorFunctionalₗ_apply, inner_smul_right, mul_comm]
  | add x y hx hy =>
    simp only [map_add, AddMemClass.coe_add, _root_.add_apply, inner_add_right, hx, hy]

/-- Matrix coefficients of a left slice are values of `φ` on right vector slices. -/
private theorem inner_tensorComponent_comm (φ : A →ₗ[𝕜] 𝕜) (ξ η : F) (x : A ⊗[𝕜] B) :
    ⟪η, ((tensorComponent φ (TensorProduct.comm 𝕜 A B x) : B) : F →L[𝕜] F) ξ⟫_𝕜 =
      φ (tensorComponent (vectorFunctionalₗ B ξ η) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [vectorFunctionalₗ_apply, inner_smul_right, mul_comm]
  | add x y hx hy =>
    simp only [map_add, AddMemClass.coe_add, _root_.add_apply, inner_add_right, hx, hy]

/-- **The right slice map is bounded by the spatial norm**: `‖R_ψ x‖ ≤ ‖ψ‖ ‖x‖_min` for every
bounded linear functional `ψ` on `B`. -/
theorem norm_tensorComponent_le (ψ : StrongDual 𝕜 B) (x : A ⊗[𝕜] B) :
    ‖tensorComponent (ψ : B →ₗ[𝕜] 𝕜) x‖ ≤ ‖ψ‖ * spatialNorm A B x := by
  rw [AddSubgroupClass.coe_norm]
  refine ContinuousLinearMap.opNorm_le_of_norm_inner_le
    (by positivity [spatialNorm_nonneg A B x]) fun ξ η ↦ ?_
  have hL : ‖tensorComponent (vectorFunctionalₗ A ξ η) (TensorProduct.comm 𝕜 A B x)‖ ≤
      spatialNorm A B x * ‖ξ‖ * ‖η‖ := by
    rw [AddSubgroupClass.coe_norm, coe_tensorComponent_comm_vectorFunctionalₗ, spatialNorm_def]
    exact TensorProduct.norm_sliceLeft_apply_le _ ξ η
  rw [inner_tensorComponent]
  calc _ ≤ ‖ψ‖ * ‖tensorComponent (vectorFunctionalₗ A ξ η) (TensorProduct.comm 𝕜 A B x)‖ :=
        ψ.le_opNorm _
    _ ≤ ‖ψ‖ * (spatialNorm A B x * ‖ξ‖ * ‖η‖) := by gcongr
    _ = _ := by ring

/-- **The left slice map is bounded by the spatial norm**: `‖L_φ x‖ ≤ ‖φ‖ ‖x‖_min` for every
bounded linear functional `φ` on `A`. -/
theorem norm_tensorComponent_comm_le (φ : StrongDual 𝕜 A) (x : A ⊗[𝕜] B) :
    ‖tensorComponent (φ : A →ₗ[𝕜] 𝕜) (TensorProduct.comm 𝕜 A B x)‖ ≤
      ‖φ‖ * spatialNorm A B x := by
  rw [AddSubgroupClass.coe_norm]
  refine ContinuousLinearMap.opNorm_le_of_norm_inner_le
    (by positivity [spatialNorm_nonneg A B x]) fun ξ η ↦ ?_
  have hR : ‖tensorComponent (vectorFunctionalₗ B ξ η) x‖ ≤
      spatialNorm A B x * ‖ξ‖ * ‖η‖ := by
    rw [AddSubgroupClass.coe_norm, coe_tensorComponent_vectorFunctionalₗ, spatialNorm_def]
    exact TensorProduct.norm_sliceRight_apply_le _ ξ η
  rw [inner_tensorComponent_comm]
  calc _ ≤ ‖φ‖ * ‖tensorComponent (vectorFunctionalₗ B ξ η) x‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * (spatialNorm A B x * ‖ξ‖ * ‖η‖) := by gcongr
    _ = _ := by ring

/-! ### Slice maps on the spatial tensor product -/

variable (A B)

/-- The **right slice map** `R_ψ : A ⊗_min B → A` of a bounded linear functional `ψ` on `B`, for
complete `A`: the bounded extension of `a ⊗ b ↦ ψ(b) a`. -/
def minSliceRight [CompleteSpace A] (ψ : StrongDual 𝕜 B) : minTensor A B →L[𝕜] A :=
  (tensorComponent (M := A) (ψ : B →ₗ[𝕜] 𝕜)).extendOfNorm (E := A ⊗[𝕜] B)
    (LinearMap.ofClass (toMinTensor A B))

/-- The **left slice map** `L_φ : A ⊗_min B → B` of a bounded linear functional `φ` on `A`, for
complete `B`: the bounded extension of `a ⊗ b ↦ φ(a) b`. -/
def minSliceLeft [CompleteSpace B] (φ : StrongDual 𝕜 A) : minTensor A B →L[𝕜] B :=
  (tensorComponent (M := B) (φ : A →ₗ[𝕜] 𝕜) ∘ₗ
    (TensorProduct.comm 𝕜 A B).toLinearMap).extendOfNorm (E := A ⊗[𝕜] B)
      (LinearMap.ofClass (toMinTensor A B))

variable {A B}

/-- Unfolding `NonUnitalStarSubalgebra.minSliceRight`. -/
theorem minSliceRight_def [CompleteSpace A] (ψ : StrongDual 𝕜 B) :
    minSliceRight A B ψ =
      (tensorComponent (M := A) (ψ : B →ₗ[𝕜] 𝕜)).extendOfNorm (E := A ⊗[𝕜] B)
        (LinearMap.ofClass (toMinTensor A B) : A ⊗[𝕜] B →ₗ[𝕜] minTensor A B) :=
  (rfl)

/-- Unfolding `NonUnitalStarSubalgebra.minSliceLeft`. -/
theorem minSliceLeft_def [CompleteSpace B] (φ : StrongDual 𝕜 A) :
    minSliceLeft A B φ =
      (tensorComponent (M := B) (φ : A →ₗ[𝕜] 𝕜) ∘ₗ
        (TensorProduct.comm 𝕜 A B).toLinearMap).extendOfNorm (E := A ⊗[𝕜] B)
          (LinearMap.ofClass (toMinTensor A B) : A ⊗[𝕜] B →ₗ[𝕜] minTensor A B) :=
  (rfl)

private theorem norm_tensorComponent_le' (ψ : StrongDual 𝕜 B) (x : A ⊗[𝕜] B) :
    ‖tensorComponent (ψ : B →ₗ[𝕜] 𝕜) x‖ ≤
      ‖ψ‖ * ‖(LinearMap.ofClass (toMinTensor A B) : A ⊗[𝕜] B →ₗ[𝕜] minTensor A B) x‖ :=
  (norm_tensorComponent_le ψ x).trans_eq (by rw [LinearMap.coe_ofClass, norm_toMinTensor])

private theorem norm_tensorComponent_comm_le' (φ : StrongDual 𝕜 A) (x : A ⊗[𝕜] B) :
    ‖tensorComponent (φ : A →ₗ[𝕜] 𝕜) (TensorProduct.comm 𝕜 A B x)‖ ≤
      ‖φ‖ * ‖(LinearMap.ofClass (toMinTensor A B) : A ⊗[𝕜] B →ₗ[𝕜] minTensor A B) x‖ :=
  (norm_tensorComponent_comm_le φ x).trans_eq (by rw [LinearMap.coe_ofClass, norm_toMinTensor])

/-- On the algebraic tensor product, `minSliceRight` is the right slice map. -/
@[simp]
theorem minSliceRight_toMinTensor [CompleteSpace A] (ψ : StrongDual 𝕜 B) (x : A ⊗[𝕜] B) :
    minSliceRight A B ψ (toMinTensor A B x) = tensorComponent (ψ : B →ₗ[𝕜] 𝕜) x := by
  rw [minSliceRight_def]
  apply LinearMap.extendOfNorm_eq
  · exact denseRange_toMinTensor A B
  · exact ⟨_, norm_tensorComponent_le' ψ⟩

/-- On the algebraic tensor product, `minSliceLeft` is the left slice map. -/
@[simp]
theorem minSliceLeft_toMinTensor [CompleteSpace B] (φ : StrongDual 𝕜 A) (x : A ⊗[𝕜] B) :
    minSliceLeft A B φ (toMinTensor A B x) =
      tensorComponent (φ : A →ₗ[𝕜] 𝕜) (TensorProduct.comm 𝕜 A B x) := by
  rw [minSliceLeft_def]
  apply LinearMap.extendOfNorm_eq
  · exact denseRange_toMinTensor A B
  · exact ⟨_, norm_tensorComponent_comm_le' φ⟩

/-- `minSliceRight A B ψ` is the unique bounded linear map `A ⊗_min B → A` that restricts to the
right slice map on the algebraic tensor product. -/
theorem eq_minSliceRight_iff [CompleteSpace A] {ψ : StrongDual 𝕜 B}
    {T : minTensor A B →L[𝕜] A} :
    T = minSliceRight A B ψ ↔ ∀ x, T (toMinTensor A B x) = tensorComponent (ψ : B →ₗ[𝕜] 𝕜) x :=
  ⟨by rintro rfl x; exact minSliceRight_toMinTensor ψ x,
    fun h ↦ minTensor_continuousLinearMap_ext fun a b ↦ by rw [h, minSliceRight_toMinTensor]⟩

/-- `minSliceLeft A B φ` is the unique bounded linear map `A ⊗_min B → B` that restricts to the
left slice map on the algebraic tensor product. -/
theorem eq_minSliceLeft_iff [CompleteSpace B] {φ : StrongDual 𝕜 A}
    {T : minTensor A B →L[𝕜] B} :
    T = minSliceLeft A B φ ↔
      ∀ x, T (toMinTensor A B x) = tensorComponent (φ : A →ₗ[𝕜] 𝕜) (TensorProduct.comm 𝕜 A B x) :=
  ⟨by rintro rfl x; exact minSliceLeft_toMinTensor φ x,
    fun h ↦ minTensor_continuousLinearMap_ext fun a b ↦ by rw [h, minSliceLeft_toMinTensor]⟩

/-- The right slice map of the zero functional is zero. -/
@[simp]
theorem minSliceRight_zero [CompleteSpace A] : minSliceRight A B (0 : StrongDual 𝕜 B) = 0 :=
  minTensor_continuousLinearMap_ext fun a b ↦ by simp

/-- The left slice map of the zero functional is zero. -/
@[simp]
theorem minSliceLeft_zero [CompleteSpace B] : minSliceLeft A B (0 : StrongDual 𝕜 A) = 0 :=
  minTensor_continuousLinearMap_ext fun a b ↦ by simp

/-- The right slice map is additive in the functional. -/
@[simp]
theorem minSliceRight_add [CompleteSpace A] (ψ₁ ψ₂ : StrongDual 𝕜 B) :
    minSliceRight A B (ψ₁ + ψ₂) = minSliceRight A B ψ₁ + minSliceRight A B ψ₂ :=
  minTensor_continuousLinearMap_ext fun a b ↦ by simp

/-- The left slice map is additive in the functional. -/
@[simp]
theorem minSliceLeft_add [CompleteSpace B] (φ₁ φ₂ : StrongDual 𝕜 A) :
    minSliceLeft A B (φ₁ + φ₂) = minSliceLeft A B φ₁ + minSliceLeft A B φ₂ :=
  minTensor_continuousLinearMap_ext fun a b ↦ by simp

/-- The right slice map is homogeneous in the functional. -/
@[simp]
theorem minSliceRight_smul [CompleteSpace A] (c : 𝕜) (ψ : StrongDual 𝕜 B) :
    minSliceRight A B (c • ψ) = c • minSliceRight A B ψ :=
  minTensor_continuousLinearMap_ext fun a b ↦ by simp

/-- The left slice map is homogeneous in the functional. -/
@[simp]
theorem minSliceLeft_smul [CompleteSpace B] (c : 𝕜) (φ : StrongDual 𝕜 A) :
    minSliceLeft A B (c • φ) = c • minSliceLeft A B φ :=
  minTensor_continuousLinearMap_ext fun a b ↦ by simp

/-- The right slice map has norm at most `‖ψ‖`. -/
theorem norm_minSliceRight_le [CompleteSpace A] (ψ : StrongDual 𝕜 B) :
    ‖minSliceRight A B ψ‖ ≤ ‖ψ‖ := by
  rw [minSliceRight_def]
  apply LinearMap.opNorm_extendOfNorm_le
  · exact denseRange_toMinTensor A B
  · exact norm_nonneg ψ
  · exact norm_tensorComponent_le' ψ

/-- The left slice map has norm at most `‖φ‖`. -/
theorem norm_minSliceLeft_le [CompleteSpace B] (φ : StrongDual 𝕜 A) :
    ‖minSliceLeft A B φ‖ ≤ ‖φ‖ := by
  rw [minSliceLeft_def]
  apply LinearMap.opNorm_extendOfNorm_le
  · exact denseRange_toMinTensor A B
  · exact norm_nonneg φ
  · exact norm_tensorComponent_comm_le' φ

/-- **The right slice map has norm `‖ψ‖`** when `A ≠ 0`: test it on `a ⊗ b` for a nonzero
`a ∈ A`. -/
theorem norm_minSliceRight [CompleteSpace A] [Nontrivial A] (ψ : StrongDual 𝕜 B) :
    ‖minSliceRight A B ψ‖ = ‖ψ‖ := by
  refine (norm_minSliceRight_le ψ).antisymm
    (ψ.opNorm_le_bound (norm_nonneg (minSliceRight A B ψ)) fun b ↦ ?_)
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  have h := (minSliceRight A B ψ).le_opNorm (toMinTensor A B (a ⊗ₜ b))
  rw [minSliceRight_toMinTensor, tensorComponent_tmul, norm_smul, norm_toMinTensor,
    spatialNorm_tmul, mul_left_comm] at h
  exact le_of_mul_le_mul_right (by simpa [mul_comm] using h) (norm_pos_iff.2 ha)

/-- **The left slice map has norm `‖φ‖`** when `B ≠ 0`: test it on `a ⊗ b` for a nonzero
`b ∈ B`. -/
theorem norm_minSliceLeft [CompleteSpace B] [Nontrivial B] (φ : StrongDual 𝕜 A) :
    ‖minSliceLeft A B φ‖ = ‖φ‖ := by
  refine (norm_minSliceLeft_le φ).antisymm
    (φ.opNorm_le_bound (norm_nonneg (minSliceLeft A B φ)) fun a ↦ ?_)
  obtain ⟨b, hb⟩ := exists_ne (0 : B)
  have h := (minSliceLeft A B φ).le_opNorm (toMinTensor A B (a ⊗ₜ b))
  rw [minSliceLeft_toMinTensor, TensorProduct.comm_tmul, tensorComponent_tmul, norm_smul,
    norm_toMinTensor, spatialNorm_tmul, ← mul_assoc] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.2 hb)

/-- When `A = 0` every right slice map is zero. -/
theorem minSliceRight_of_subsingleton [CompleteSpace A] [Subsingleton A]
    (ψ : StrongDual 𝕜 B) :
    minSliceRight A B ψ = 0 :=
  Subsingleton.elim _ _

/-- When `B = 0` every left slice map is zero. -/
theorem minSliceLeft_of_subsingleton [CompleteSpace B] [Subsingleton B]
    (φ : StrongDual 𝕜 A) :
    minSliceLeft A B φ = 0 :=
  Subsingleton.elim _ _

end NonUnitalStarSubalgebra
