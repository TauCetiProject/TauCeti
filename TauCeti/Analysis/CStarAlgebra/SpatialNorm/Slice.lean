/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.Analysis.CStarAlgebra.SpatialNorm
public import TauCeti.Analysis.Normed.Module.NonUnitalSubalgebra
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Slice maps of the spatial tensor product

Let `A ⊆ B(E)` and `B ⊆ B(F)` be concrete operator algebras with spatial tensor product
`A ⊗_min B`. For a bounded linear functional `ψ` on `B`, the **right slice map** `R_ψ` sends
`a ⊗ b` to `ψ(b) a`. On the algebraic tensor product it satisfies `‖R_ψ x‖ ≤ ‖ψ‖ ‖x‖_min`
(`NonUnitalStarSubalgebra.norm_sliceRightₗ_le`). For vectors `ξ`, `η` of `E` the matrix
coefficient `⟪η, R_ψ(x) ξ⟫` is `ψ` applied to the left slice of `x` by the vector functional
`a ↦ ⟪η, a ξ⟫` of `A`, and that slice is the operator `TensorProduct.sliceLeft ξ η` applied to
the image of `x` in `B(E ⊗₂ F)`, whose norm is at most `‖ξ‖ ‖η‖ ‖x‖_min`. So the bound holds for
every bounded functional, with no positivity or decomposition into positive functionals.

When `A` is complete (a C*-subalgebra), `R_ψ` therefore extends to a bounded operator
`A ⊗_min B → A` (`NonUnitalStarSubalgebra.minSliceRight`) of norm at most `‖ψ‖`, with equality
when `A ≠ 0` (`NonUnitalStarSubalgebra.norm_minSliceRight`), tested on `a ⊗ b` for a nonzero
`a`; when `A = 0` its norm is `0`. Symmetrically, a bounded functional `φ` on `A` gives the left
slice map `L_φ : A ⊗_min B → B`, `a ⊗ b ↦ φ(a) b` (`NonUnitalStarSubalgebra.minSliceLeft`).

## Main declarations

* `NonUnitalStarSubalgebra.sliceRightₗ`, `NonUnitalStarSubalgebra.sliceLeftₗ`: the slice maps on
  the algebraic tensor product.
* `NonUnitalStarSubalgebra.norm_sliceRightₗ_le`, `NonUnitalStarSubalgebra.norm_sliceLeftₗ_le`:
  `‖R_ψ x‖ ≤ ‖ψ‖ ‖x‖_min` and `‖L_φ x‖ ≤ ‖φ‖ ‖x‖_min`.
* `NonUnitalStarSubalgebra.minSliceRight`, `NonUnitalStarSubalgebra.minSliceLeft`: their bounded
  extensions to `A ⊗_min B`, with `NonUnitalStarSubalgebra.norm_minSliceRight` and
  `NonUnitalStarSubalgebra.norm_minSliceLeft`.

## References

* M. Takesaki, *Theory of Operator Algebras I*, Chapter IV, §4.
-/

public section

noncomputable section

open UniformSpace TensorProduct
open scoped InnerProductSpace

namespace NonUnitalStarSubalgebra

open TauCeti

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
  (A : NonUnitalStarSubalgebra 𝕜 (E →L[𝕜] E)) (B : NonUnitalStarSubalgebra 𝕜 (F →L[𝕜] F))

/-! ### Slice maps on the algebraic tensor product -/

/-- The **right slice map** `R_ψ : A ⊗[𝕜] B → A`, `a ⊗ b ↦ ψ(b) a`, of a linear functional `ψ`
on `B`. -/
def sliceRightₗ (ψ : B →ₗ[𝕜] 𝕜) : A ⊗[𝕜] B →ₗ[𝕜] A :=
  (TensorProduct.rid 𝕜 A).toLinearMap ∘ₗ ψ.lTensor A

/-- The **left slice map** `L_φ : A ⊗[𝕜] B → B`, `a ⊗ b ↦ φ(a) b`, of a linear functional `φ`
on `A`. -/
def sliceLeftₗ (φ : A →ₗ[𝕜] 𝕜) : A ⊗[𝕜] B →ₗ[𝕜] B :=
  (TensorProduct.lid 𝕜 B).toLinearMap ∘ₗ φ.rTensor B

variable {A B}

/-- Unfolding `NonUnitalStarSubalgebra.sliceRightₗ`. -/
theorem sliceRightₗ_def (ψ : B →ₗ[𝕜] 𝕜) :
    sliceRightₗ A B ψ = (TensorProduct.rid 𝕜 A).toLinearMap ∘ₗ ψ.lTensor A :=
  (rfl)

/-- Unfolding `NonUnitalStarSubalgebra.sliceLeftₗ`. -/
theorem sliceLeftₗ_def (φ : A →ₗ[𝕜] 𝕜) :
    sliceLeftₗ A B φ = (TensorProduct.lid 𝕜 B).toLinearMap ∘ₗ φ.rTensor B :=
  (rfl)

/-- The right slice map sends `a ⊗ b` to `ψ(b) a`. -/
@[simp]
theorem sliceRightₗ_tmul (ψ : B →ₗ[𝕜] 𝕜) (a : A) (b : B) :
    sliceRightₗ A B ψ (a ⊗ₜ b) = ψ b • a := by
  simp [sliceRightₗ_def]

/-- The left slice map sends `a ⊗ b` to `φ(a) b`. -/
@[simp]
theorem sliceLeftₗ_tmul (φ : A →ₗ[𝕜] 𝕜) (a : A) (b : B) :
    sliceLeftₗ A B φ (a ⊗ₜ b) = φ a • b := by
  simp [sliceLeftₗ_def]

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
private theorem coe_sliceLeftₗ_vectorFunctionalₗ (ξ η : E) (x : A ⊗[𝕜] B) :
    ((sliceLeftₗ A B (vectorFunctionalₗ A ξ η) x : B) : F →L[𝕜] F) =
      TensorProduct.sliceLeft ξ η (spatialTensorHom A B x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [vectorFunctionalₗ_apply]
  | add x y hx hy => simp only [map_add, AddMemClass.coe_add, hx, hy]

/-- The right slice by a vector functional of `B` is the operator slice
`TensorProduct.sliceRight ξ η` of the spatial tensor operator. -/
private theorem coe_sliceRightₗ_vectorFunctionalₗ (ξ η : F) (x : A ⊗[𝕜] B) :
    ((sliceRightₗ A B (vectorFunctionalₗ B ξ η) x : A) : E →L[𝕜] E) =
      TensorProduct.sliceRight ξ η (spatialTensorHom A B x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [vectorFunctionalₗ_apply]
  | add x y hx hy => simp only [map_add, AddMemClass.coe_add, hx, hy]

/-- Matrix coefficients of a right slice are values of `ψ` on left vector slices. -/
private theorem inner_sliceRightₗ (ψ : B →ₗ[𝕜] 𝕜) (ξ η : E) (x : A ⊗[𝕜] B) :
    ⟪η, (sliceRightₗ A B ψ x : E →L[𝕜] E) ξ⟫_𝕜 =
      ψ (sliceLeftₗ A B (vectorFunctionalₗ A ξ η) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [vectorFunctionalₗ_apply, inner_smul_right, mul_comm]
  | add x y hx hy =>
    simp only [map_add, AddMemClass.coe_add, _root_.add_apply, inner_add_right, hx, hy]

/-- Matrix coefficients of a left slice are values of `φ` on right vector slices. -/
private theorem inner_sliceLeftₗ (φ : A →ₗ[𝕜] 𝕜) (ξ η : F) (x : A ⊗[𝕜] B) :
    ⟪η, (sliceLeftₗ A B φ x : F →L[𝕜] F) ξ⟫_𝕜 =
      φ (sliceRightₗ A B (vectorFunctionalₗ B ξ η) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a b => simp [vectorFunctionalₗ_apply, inner_smul_right, mul_comm]
  | add x y hx hy =>
    simp only [map_add, AddMemClass.coe_add, _root_.add_apply, inner_add_right, hx, hy]

/-- An operator whose matrix coefficients are bounded by `C ‖ξ‖ ‖η‖` has norm at most `C`. -/
private theorem norm_le_of_inner_le {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {T : G →L[𝕜] G} {C : ℝ} (hC : 0 ≤ C) (h : ∀ ξ η, ‖⟪η, T ξ⟫_𝕜‖ ≤ C * ‖ξ‖ * ‖η‖) :
    ‖T‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_of_re_inner_le hC fun ξ η hξ hη ↦ by
    rw [← inner_conj_symm, RCLike.conj_re]
    simpa [hξ, hη] using (RCLike.re_le_norm _).trans (h ξ η)

/-- **The right slice map is bounded by the spatial norm**: `‖R_ψ x‖ ≤ ‖ψ‖ ‖x‖_min` for every
bounded linear functional `ψ` on `B`. -/
theorem norm_sliceRightₗ_le (ψ : StrongDual 𝕜 B) (x : A ⊗[𝕜] B) :
    ‖sliceRightₗ A B (ψ : B →ₗ[𝕜] 𝕜) x‖ ≤ ‖ψ‖ * spatialNorm A B x := by
  change ‖((sliceRightₗ A B (ψ : B →ₗ[𝕜] 𝕜) x : A) : E →L[𝕜] E)‖ ≤ _
  refine norm_le_of_inner_le (by positivity [spatialNorm_nonneg A B x]) fun ξ η ↦ ?_
  have hL : ‖sliceLeftₗ A B (vectorFunctionalₗ A ξ η) x‖ ≤ spatialNorm A B x * ‖ξ‖ * ‖η‖ := by
    change ‖((sliceLeftₗ A B (vectorFunctionalₗ A ξ η) x : B) : F →L[𝕜] F)‖ ≤ _
    rw [coe_sliceLeftₗ_vectorFunctionalₗ, spatialNorm_def]
    exact TensorProduct.norm_sliceLeft_apply_le _ ξ η
  rw [inner_sliceRightₗ]
  calc _ ≤ ‖ψ‖ * ‖sliceLeftₗ A B (vectorFunctionalₗ A ξ η) x‖ := ψ.le_opNorm _
    _ ≤ ‖ψ‖ * (spatialNorm A B x * ‖ξ‖ * ‖η‖) := by gcongr
    _ = _ := by ring

/-- **The left slice map is bounded by the spatial norm**: `‖L_φ x‖ ≤ ‖φ‖ ‖x‖_min` for every
bounded linear functional `φ` on `A`. -/
theorem norm_sliceLeftₗ_le (φ : StrongDual 𝕜 A) (x : A ⊗[𝕜] B) :
    ‖sliceLeftₗ A B (φ : A →ₗ[𝕜] 𝕜) x‖ ≤ ‖φ‖ * spatialNorm A B x := by
  change ‖((sliceLeftₗ A B (φ : A →ₗ[𝕜] 𝕜) x : B) : F →L[𝕜] F)‖ ≤ _
  refine norm_le_of_inner_le (by positivity [spatialNorm_nonneg A B x]) fun ξ η ↦ ?_
  have hR : ‖sliceRightₗ A B (vectorFunctionalₗ B ξ η) x‖ ≤ spatialNorm A B x * ‖ξ‖ * ‖η‖ := by
    change ‖((sliceRightₗ A B (vectorFunctionalₗ B ξ η) x : A) : E →L[𝕜] E)‖ ≤ _
    rw [coe_sliceRightₗ_vectorFunctionalₗ, spatialNorm_def]
    exact TensorProduct.norm_sliceRight_apply_le _ ξ η
  rw [inner_sliceLeftₗ]
  calc _ ≤ ‖φ‖ * ‖sliceRightₗ A B (vectorFunctionalₗ B ξ η) x‖ := φ.le_opNorm _
    _ ≤ ‖φ‖ * (spatialNorm A B x * ‖ξ‖ * ‖η‖) := by gcongr
    _ = _ := by ring

/-! ### Slice maps on the spatial tensor product -/

variable (A B)

/-- The linear map `A ⊗[𝕜] B → A ⊗_min B` underlying `NonUnitalStarSubalgebra.toMinTensor`. -/
def toMinTensorₗ : A ⊗[𝕜] B →ₗ[𝕜] minTensor A B where
  toFun := toMinTensor A B
  map_add' := map_add _
  map_smul' := map_smul _

/-- The **right slice map** `R_ψ : A ⊗_min B → A` of a bounded linear functional `ψ` on `B`, for
complete `A`: the bounded extension of `a ⊗ b ↦ ψ(b) a`. -/
def minSliceRight [CompleteSpace A] (ψ : StrongDual 𝕜 B) : minTensor A B →L[𝕜] A :=
  (sliceRightₗ A B (ψ : B →ₗ[𝕜] 𝕜)).extendOfNorm (E := A ⊗[𝕜] B) (toMinTensorₗ A B)

/-- The **left slice map** `L_φ : A ⊗_min B → B` of a bounded linear functional `φ` on `A`, for
complete `B`: the bounded extension of `a ⊗ b ↦ φ(a) b`. -/
def minSliceLeft [CompleteSpace B] (φ : StrongDual 𝕜 A) : minTensor A B →L[𝕜] B :=
  (sliceLeftₗ A B (φ : A →ₗ[𝕜] 𝕜)).extendOfNorm (E := A ⊗[𝕜] B) (toMinTensorₗ A B)

variable {A B}

/-- Unfolding `NonUnitalStarSubalgebra.minSliceRight`. -/
theorem minSliceRight_def [CompleteSpace A] (ψ : StrongDual 𝕜 B) :
    minSliceRight A B ψ =
      (sliceRightₗ A B (ψ : B →ₗ[𝕜] 𝕜)).extendOfNorm (E := A ⊗[𝕜] B) (toMinTensorₗ A B) :=
  (rfl)

/-- Unfolding `NonUnitalStarSubalgebra.minSliceLeft`. -/
theorem minSliceLeft_def [CompleteSpace B] (φ : StrongDual 𝕜 A) :
    minSliceLeft A B φ =
      (sliceLeftₗ A B (φ : A →ₗ[𝕜] 𝕜)).extendOfNorm (E := A ⊗[𝕜] B) (toMinTensorₗ A B) :=
  (rfl)

/-- `toMinTensorₗ` is `toMinTensor`. -/
@[simp]
theorem toMinTensorₗ_apply (x : A ⊗[𝕜] B) : toMinTensorₗ A B x = toMinTensor A B x :=
  (rfl)

private theorem denseRange_toMinTensorₗ : DenseRange (toMinTensorₗ A B) :=
  denseRange_toMinTensor A B

private theorem norm_sliceRightₗ_le' (ψ : StrongDual 𝕜 B) (x : A ⊗[𝕜] B) :
    ‖sliceRightₗ A B (ψ : B →ₗ[𝕜] 𝕜) x‖ ≤ ‖ψ‖ * ‖toMinTensorₗ A B x‖ :=
  (norm_sliceRightₗ_le ψ x).trans_eq (by rw [toMinTensorₗ_apply, norm_toMinTensor])

private theorem norm_sliceLeftₗ_le' (φ : StrongDual 𝕜 A) (x : A ⊗[𝕜] B) :
    ‖sliceLeftₗ A B (φ : A →ₗ[𝕜] 𝕜) x‖ ≤ ‖φ‖ * ‖toMinTensorₗ A B x‖ :=
  (norm_sliceLeftₗ_le φ x).trans_eq (by rw [toMinTensorₗ_apply, norm_toMinTensor])

/-- `LinearMap.extendOfNorm_eq` for maps into and out of concrete operator algebras, stated for an
arbitrary subalgebra `S` so that applying it to `minTensor A B` needs no unfolding. -/
private theorem extendOfNorm_eq_of_le {G K : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace G]
    [CompleteSpace K] {S : NonUnitalStarSubalgebra 𝕜 (K →L[𝕜] K)}
    {D : NonUnitalStarSubalgebra 𝕜 (G →L[𝕜] G)} [CompleteSpace D] {f : A ⊗[𝕜] B →ₗ[𝕜] D}
    {e : A ⊗[𝕜] B →ₗ[𝕜] S} (he : DenseRange e) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C * ‖e x‖)
    (x : A ⊗[𝕜] B) : f.extendOfNorm (E := A ⊗[𝕜] B) e (e x) = f x :=
  LinearMap.extendOfNorm_eq (E := A ⊗[𝕜] B) he ⟨C, hC⟩ x

/-- `LinearMap.opNorm_extendOfNorm_le` in the setting of `extendOfNorm_eq_of_le`. -/
private theorem opNorm_extendOfNorm_le_of_le {G K : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace G]
    [CompleteSpace K] {S : NonUnitalStarSubalgebra 𝕜 (K →L[𝕜] K)}
    {D : NonUnitalStarSubalgebra 𝕜 (G →L[𝕜] G)} [CompleteSpace D] {f : A ⊗[𝕜] B →ₗ[𝕜] D}
    {e : A ⊗[𝕜] B →ₗ[𝕜] S} (he : DenseRange e) {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ∀ x, ‖f x‖ ≤ C * ‖e x‖) : ‖f.extendOfNorm (E := A ⊗[𝕜] B) e‖ ≤ C :=
  LinearMap.opNorm_extendOfNorm_le (E := A ⊗[𝕜] B) he hC₀ hC

/-- On the algebraic tensor product, `minSliceRight` is the right slice map. -/
@[simp]
theorem minSliceRight_toMinTensor [CompleteSpace A] (ψ : StrongDual 𝕜 B) (x : A ⊗[𝕜] B) :
    minSliceRight A B ψ (toMinTensor A B x) = sliceRightₗ A B (ψ : B →ₗ[𝕜] 𝕜) x := by
  rw [minSliceRight_def]
  exact extendOfNorm_eq_of_le denseRange_toMinTensorₗ (norm_sliceRightₗ_le' ψ) x

/-- On the algebraic tensor product, `minSliceLeft` is the left slice map. -/
@[simp]
theorem minSliceLeft_toMinTensor [CompleteSpace B] (φ : StrongDual 𝕜 A) (x : A ⊗[𝕜] B) :
    minSliceLeft A B φ (toMinTensor A B x) = sliceLeftₗ A B (φ : A →ₗ[𝕜] 𝕜) x := by
  rw [minSliceLeft_def]
  exact extendOfNorm_eq_of_le denseRange_toMinTensorₗ (norm_sliceLeftₗ_le' φ) x

/-- The right slice map has norm at most `‖ψ‖`. -/
theorem norm_minSliceRight_le [CompleteSpace A] (ψ : StrongDual 𝕜 B) :
    ‖minSliceRight A B ψ‖ ≤ ‖ψ‖ := by
  rw [minSliceRight_def]
  exact opNorm_extendOfNorm_le_of_le denseRange_toMinTensorₗ (norm_nonneg ψ)
    (norm_sliceRightₗ_le' ψ)

/-- The left slice map has norm at most `‖φ‖`. -/
theorem norm_minSliceLeft_le [CompleteSpace B] (φ : StrongDual 𝕜 A) :
    ‖minSliceLeft A B φ‖ ≤ ‖φ‖ := by
  rw [minSliceLeft_def]
  exact opNorm_extendOfNorm_le_of_le denseRange_toMinTensorₗ (norm_nonneg φ)
    (norm_sliceLeftₗ_le' φ)

/-- **The right slice map has norm `‖ψ‖`** when `A ≠ 0`: test it on `a ⊗ b` for a nonzero
`a ∈ A`. -/
theorem norm_minSliceRight [CompleteSpace A] [Nontrivial A] (ψ : StrongDual 𝕜 B) :
    ‖minSliceRight A B ψ‖ = ‖ψ‖ := by
  refine (norm_minSliceRight_le ψ).antisymm
    (ψ.opNorm_le_bound (norm_nonneg (minSliceRight A B ψ)) fun b ↦ ?_)
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  have h := (minSliceRight A B ψ).le_opNorm (toMinTensor A B (a ⊗ₜ b))
  rw [minSliceRight_toMinTensor, sliceRightₗ_tmul, norm_smul, norm_toMinTensor,
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
  rw [minSliceLeft_toMinTensor, sliceLeftₗ_tmul, norm_smul, norm_toMinTensor,
    spatialNorm_tmul, ← mul_assoc] at h
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
