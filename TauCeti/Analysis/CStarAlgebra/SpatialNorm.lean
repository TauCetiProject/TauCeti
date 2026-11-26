/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
public import TauCeti.Algebra.Star.TensorProductLift
public import TauCeti.Analysis.InnerProductSpace.Operator.VectorFunctional
public import TauCeti.Analysis.InnerProductSpace.TensorProduct.Completion
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic
import TauCeti.Topology.Algebra.NonUnitalStarAlgebra

/-!
# The spatial C*-norm on an algebraic tensor product of operator algebras

Let `E` and `F` be Hilbert spaces over `𝕜 = ℝ` or `ℂ`, with completed Hilbert tensor product
`E ⊗₂ F = Completion (E ⊗[𝕜] F)`. A bounded operator `a` on `E` and a bounded operator `b` on `F`
give the bounded operator `a ⊗ b = TensorProduct.mapLCompletion a b` on `E ⊗₂ F`. For concrete
operator algebras `A ⊆ B(E)` and `B ⊆ B(F)` (non-unital star subalgebras), these operators form
the star homomorphism `A ⊗[𝕜] B → B(E ⊗₂ F)`, `a ⊗ b ↦ a ⊗ b`
(`NonUnitalStarSubalgebra.spatialTensorHom A B`): it is the product of the amplifications `a ⊗ 1`
and `1 ⊗ b`, which commute.

This homomorphism is **injective** (`NonUnitalStarSubalgebra.spatialTensorHom_injective`). Already
the linear map `B(E, E') ⊗[𝕜] B(F, F') → B(E ⊗₂ F, E' ⊗₂ F')` is injective
(`TauCeti.spatialTensorLinearMap_injective`): write `x = Σᵢ aᵢ ⊗ cᵢ` along a basis `(cᵢ)` of
`B(F, F')`; testing `x` on vectors `ξ ⊗ η` against `ξ' ⊗ η'` gives
`⟪η', (Σᵢ ⟪ξ', aᵢ ξ⟫ cᵢ) η⟫ = 0`, so every `⟪ξ', aᵢ ξ⟫` vanishes and so does every `aᵢ`. For
subalgebras, the inclusion `A ⊗[𝕜] B → B(E) ⊗[𝕜] B(F)` is injective because vector spaces are
flat.

So `‖x‖_min = ‖(spatialTensorHom A B) x‖` is a norm on `A ⊗[𝕜] B`
(`NonUnitalStarSubalgebra.spatialNorm`), the **spatial** C*-norm relative to the given
representations `A ⊆ B(E)` and `B ⊆ B(F)`: it is submultiplicative, satisfies the C*-identity
`‖x⋆ x‖_min = ‖x‖_min ^ 2`, and `‖a ⊗ b‖_min = ‖a‖ ‖b‖`. The **spatial tensor product**
`A ⊗_min B` (`NonUnitalStarSubalgebra.minTensor A B`) is the norm closure of the image, a closed
star subalgebra of `B(E ⊗₂ F)`.

For inclusions `A₀ ≤ A` and `B₀ ≤ B` of concrete operator algebras on the same spaces, the
induced star homomorphism `A₀ ⊗[𝕜] B₀ → A ⊗[𝕜] B` (`NonUnitalStarSubalgebra.tensorInclusion`)
is injective and isometric for the spatial norms
(`NonUnitalStarSubalgebra.spatialNorm_tensorInclusion`), and `A₀ ⊗_min B₀ ⊆ A ⊗_min B`
(`NonUnitalStarSubalgebra.minTensor_mono`): the spatial tensor homomorphism of `A` and `B` extends
that of `A₀` and `B₀`.

Both are defined from the chosen concrete representations. This file does not prove that they are
independent of the representations (Takesaki I, Theorem IV.4.9), nor that the spatial norm is the
smallest C*-norm on `A ⊗[𝕜] B`; the subscript `min` is only the conventional name.

## Main declarations

* `TauCeti.spatialTensorLinearMap`: the linear map `B(E, E') ⊗[𝕜] B(F, F') → B(E ⊗₂ F, E' ⊗₂ F')`,
  with its matrix coefficients `TauCeti.inner_spatialTensorLinearMap` and
  `TauCeti.spatialTensorLinearMap_injective`.
* `NonUnitalStarSubalgebra.spatialTensorHom A B`: the star homomorphism `A ⊗[𝕜] B → B(E ⊗₂ F)`,
  with `NonUnitalStarSubalgebra.spatialTensorHom_tmul` and
  `NonUnitalStarSubalgebra.spatialTensorHom_injective`.
* `NonUnitalStarSubalgebra.spatialNorm A B`: the spatial norm, with
  `NonUnitalStarSubalgebra.spatialNorm_eq_zero_iff`, `NonUnitalStarSubalgebra.spatialNorm_add_le`,
  `NonUnitalStarSubalgebra.spatialNorm_smul`, `NonUnitalStarSubalgebra.spatialNorm_star`,
  `NonUnitalStarSubalgebra.spatialNorm_mul_le`,
  `NonUnitalStarSubalgebra.spatialNorm_star_mul_self` and
  `NonUnitalStarSubalgebra.spatialNorm_tmul`.
* `NonUnitalStarSubalgebra.minTensor A B`: the spatial tensor product `A ⊗_min B`, with
  `NonUnitalStarSubalgebra.mem_minTensor_iff`, `NonUnitalStarSubalgebra.isClosed_minTensor`,
  `NonUnitalStarSubalgebra.minTensor_le` and `NonUnitalStarSubalgebra.mapLCompletion_mem_minTensor`.
* `NonUnitalStarSubalgebra.toMinTensor A B`: the star homomorphism `A ⊗[𝕜] B → A ⊗_min B`, with
  `NonUnitalStarSubalgebra.norm_toMinTensor` and `NonUnitalStarSubalgebra.denseRange_toMinTensor`.
* `NonUnitalStarSubalgebra.tensorInclusion`, `NonUnitalStarSubalgebra.spatialNorm_tensorInclusion`,
  `NonUnitalStarSubalgebra.minTensor_mono`: functoriality for inclusions.

## References

* M. Takesaki, *Theory of Operator Algebras I*, Chapter IV, §4 (Theorem IV.4.9 is the
  representation independence of the spatial norm).
-/

public section

noncomputable section

open UniformSpace TensorProduct ContinuousLinearMap
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 E F E' F' : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']

/-! ### The linear map on operator spaces -/

variable (𝕜 E F E' F') in
/-- The linear map `B(E, E') ⊗[𝕜] B(F, F') → B(E ⊗₂ F, E' ⊗₂ F')`, `a ⊗ b ↦ a ⊗ b`. -/
def spatialTensorLinearMap :
    (E →L[𝕜] E') ⊗[𝕜] (F →L[𝕜] F') →ₗ[𝕜] Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F') :=
  TensorProduct.lift <| LinearMap.mk₂ 𝕜 mapLCompletion mapLCompletion_add_left
    mapLCompletion_smul_left mapLCompletion_add_right mapLCompletion_smul_right

@[simp]
theorem spatialTensorLinearMap_tmul (a : E →L[𝕜] E') (b : F →L[𝕜] F') :
    spatialTensorLinearMap 𝕜 E F E' F' (a ⊗ₜ b) = mapLCompletion a b :=
  (rfl)

/-- Testing `a ⊗ b` on `ξ ⊗ η` against `ξ' ⊗ η'` gives `⟪ξ', a ξ⟫ ⟪η', b η⟫`: for every `x`, the
matrix coefficient of `spatialTensorLinearMap x` is that of the operator in `B(F, F')` obtained by
applying the vector functional `a ↦ ⟪ξ', a ξ⟫` to the first factor of `x`. -/
theorem inner_spatialTensorLinearMap (ξ : E) (ξ' : E') (η : F) (η' : F')
    (x : (E →L[𝕜] E') ⊗[𝕜] (F →L[𝕜] F')) :
    ⟪((ξ' ⊗ₜ η' : E' ⊗[𝕜] F') : Completion (E' ⊗[𝕜] F')),
        spatialTensorLinearMap 𝕜 E F E' F' x ((ξ ⊗ₜ η : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F))⟫_𝕜 =
      ⟪η', TensorProduct.lid 𝕜 (F →L[𝕜] F')
        ((vectorFunctional (𝕜 := 𝕜) ξ ξ').toLinearMap.rTensor (F →L[𝕜] F') x) η⟫_𝕜 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    simp only [map_add, add_apply, inner_add_right, hx, hy]
  | tmul a b =>
    simp [UniformSpace.Completion.inner_coe, inner_smul_right]

/-- **Injectivity of the spatial tensor map** on the full operator spaces. -/
theorem spatialTensorLinearMap_injective :
    Function.Injective (spatialTensorLinearMap 𝕜 E F E' F') := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  let c := Module.Free.chooseBasis 𝕜 (F →L[𝕜] F')
  set m := TensorProduct.equivFinsuppOfBasisRight c x with hm
  have hxm : x = m.sum fun i a ↦ a ⊗ₜ c i := by
    rw [hm, ← TensorProduct.equivFinsuppOfBasisRight_symm_apply, LinearEquiv.symm_apply_apply]
  suffices m = 0 by
    rw [hxm, this, Finsupp.sum_zero_index]
  refine Finsupp.ext fun i ↦ ContinuousLinearMap.ext fun ξ ↦ ext_inner_left 𝕜 fun ξ' ↦ ?_
  -- The operator `Σⱼ ⟪ξ', m j ξ⟫ c j` vanishes: test `x` on `ξ ⊗ η` against `ξ' ⊗ η'`.
  have hω : (m.sum fun j a ↦ vectorFunctional ξ ξ' a • c j) = 0 := by
    refine ContinuousLinearMap.ext fun η ↦ ext_inner_left 𝕜 (E := F') fun η' ↦ ?_
    have := inner_spatialTensorLinearMap ξ ξ' η η' x
    rw [hx, hxm, map_finsuppSum, map_finsuppSum] at this
    simpa [LinearMap.rTensor_tmul, TensorProduct.lid_tmul] using this.symm
  -- Its `i`-th coordinate along the basis `c` is `⟪ξ', m i ξ⟫`.
  have hωi : vectorFunctional ξ ξ' (m i) = 0 := by
    have := congrArg (fun y ↦ c.repr y i) hω
    by_cases hi : m i = 0
    · simp [hi]
    · simpa [map_finsuppSum, Finsupp.sum_apply, Finsupp.single_apply, hi] using this
  simpa using hωi

end TauCeti

/-! ### Concrete operator algebras -/

namespace NonUnitalStarSubalgebra

open TauCeti

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
  (A : NonUnitalStarSubalgebra 𝕜 (E →L[𝕜] E)) (B : NonUnitalStarSubalgebra 𝕜 (F →L[𝕜] F))

/-- The **spatial tensor homomorphism** of concrete operator algebras `A ⊆ B(E)` and
`B ⊆ B(F)`: the star homomorphism `A ⊗[𝕜] B → B(E ⊗₂ F)`, `a ⊗ b ↦ a ⊗ b`, the product of the
commuting amplifications `a ⊗ 1` and `1 ⊗ b`. -/
def spatialTensorHom :
    A ⊗[𝕜] B →⋆ₙₐ[𝕜] (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F)) :=
  Algebra.TensorProduct.liftNonUnitalStarAlgHom
    ((rTensorCompletionStarAlgHom 𝕜 E F).toNonUnitalStarAlgHom.comp
      (NonUnitalStarSubalgebraClass.subtype A))
    ((lTensorCompletionStarAlgHom 𝕜 E F).toNonUnitalStarAlgHom.comp
      (NonUnitalStarSubalgebraClass.subtype B))
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
      spatialTensorLinearMap 𝕜 E F E F
        (TensorProduct.map (NonUnitalStarSubalgebraClass.subtype A : A →ₗ[𝕜] E →L[𝕜] E)
          (NonUnitalStarSubalgebraClass.subtype B : B →ₗ[𝕜] F →L[𝕜] F) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul a b => simp

/-- **The spatial tensor homomorphism is injective.** -/
theorem spatialTensorHom_injective : Function.Injective (spatialTensorHom A B) := by
  have h := spatialTensorLinearMap_injective.comp (TensorProduct.map_injective_of_flat_flat
    (NonUnitalStarSubalgebraClass.subtype A : A →ₗ[𝕜] E →L[𝕜] E)
    (NonUnitalStarSubalgebraClass.subtype B : B →ₗ[𝕜] F →L[𝕜] F)
    Subtype.val_injective Subtype.val_injective)
  intro x y hxy
  rw [spatialTensorHom_apply, spatialTensorHom_apply] at hxy
  exact h hxy

/-! ### The spatial norm -/

/-- The **spatial norm** `‖x‖_min = ‖(spatialTensorHom A B) x‖` on `A ⊗[𝕜] B`, the norm of the
operator on `E ⊗₂ F`. -/
def spatialNorm (x : A ⊗[𝕜] B) : ℝ :=
  ‖spatialTensorHom A B x‖

/-- Unfolding `NonUnitalStarSubalgebra.spatialNorm`. -/
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

/-- The spatial norm of `0` is `0`. -/
@[simp]
theorem spatialNorm_zero : spatialNorm A B 0 = 0 := by
  rw [spatialNorm_eq_zero_iff]

/-- The spatial norm is invariant under the star operation. -/
@[simp]
theorem spatialNorm_star (x : A ⊗[𝕜] B) : spatialNorm A B (star x) = spatialNorm A B x := by
  rw [spatialNorm_def, spatialNorm_def, map_star]
  exact norm_star (spatialTensorHom A B x)

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
  rw [spatialNorm_def, spatialTensorHom_tmul, norm_mapLCompletion, AddSubgroupClass.coe_norm,
    AddSubgroupClass.coe_norm]

/-! ### The spatial tensor product -/

/-- The **spatial tensor product** `A ⊗_min B`: the norm closure in `B(E ⊗₂ F)` of the image of the
algebraic tensor product `A ⊗[𝕜] B`, a closed star subalgebra. -/
def minTensor : NonUnitalStarSubalgebra 𝕜 (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F)) :=
  (NonUnitalStarAlgHom.range (spatialTensorHom A B)).topologicalClosure

/-- Unfolding `NonUnitalStarSubalgebra.minTensor`. -/
theorem minTensor_def :
    minTensor A B = (NonUnitalStarAlgHom.range (spatialTensorHom A B)).topologicalClosure :=
  (rfl)

/-- As a set of operators, the spatial tensor product is the closure of the range of the spatial
tensor homomorphism. -/
@[simp]
theorem coe_minTensor :
    (minTensor A B : Set (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F))) =
      closure (Set.range (spatialTensorHom A B)) := by
  rw [minTensor_def, topologicalClosure_coe, NonUnitalStarAlgHom.coe_range]

/-- An operator lies in the spatial tensor product iff it is a norm limit of images of the
algebraic tensor product. -/
theorem mem_minTensor_iff {T : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F)} :
    T ∈ minTensor A B ↔ T ∈ closure (Set.range (spatialTensorHom A B)) := by
  rw [← SetLike.mem_coe, coe_minTensor]

/-- The spatial tensor product is closed. -/
theorem isClosed_minTensor :
    IsClosed (minTensor A B : Set (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F))) :=
  isClosed_topologicalClosure _

/-- The spatial tensor product contains the image of the algebraic tensor product. -/
@[simp]
theorem spatialTensorHom_mem_minTensor (x : A ⊗[𝕜] B) : spatialTensorHom A B x ∈ minTensor A B :=
  le_topologicalClosure _ ⟨x, rfl⟩

/-- The spatial tensor product is the smallest closed star subalgebra containing the image of the
algebraic tensor product. -/
theorem minTensor_le
    {S : NonUnitalStarSubalgebra 𝕜 (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F))}
    (hS : IsClosed (S : Set (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F))))
    (h : NonUnitalStarAlgHom.range (spatialTensorHom A B) ≤ S) : minTensor A B ≤ S :=
  topologicalClosure_minimal _ h hS

/-- The spatial tensor product contains the operators `a ⊗ b` for `a ∈ A` and `b ∈ B`. -/
theorem mapLCompletion_mem_minTensor {a : E →L[𝕜] E} {b : F →L[𝕜] F} (ha : a ∈ A) (hb : b ∈ B) :
    mapLCompletion a b ∈ minTensor A B := by
  simpa using spatialTensorHom_mem_minTensor A B (⟨a, ha⟩ ⊗ₜ ⟨b, hb⟩)

/-- The spatial tensor homomorphism with codomain the spatial tensor product,
`A ⊗[𝕜] B → A ⊗_min B`. -/
def toMinTensor : A ⊗[𝕜] B →⋆ₙₐ[𝕜] minTensor A B :=
  NonUnitalStarAlgHom.codRestrict (spatialTensorHom A B) (minTensor A B)
    (spatialTensorHom_mem_minTensor A B)

/-- As an operator on `E ⊗₂ F`, `toMinTensor A B x` is `spatialTensorHom A B x`. -/
@[simp]
theorem coe_toMinTensor (x : A ⊗[𝕜] B) :
    (toMinTensor A B x : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F)) =
      spatialTensorHom A B x :=
  (rfl)

/-- The norm of `x` in the spatial tensor product is its spatial norm. -/
theorem norm_toMinTensor (x : A ⊗[𝕜] B) : ‖toMinTensor A B x‖ = spatialNorm A B x := by
  rw [spatialNorm_def, ← coe_toMinTensor, AddSubgroupClass.coe_norm]

/-- The algebraic tensor product is dense in the spatial tensor product. -/
theorem denseRange_toMinTensor : DenseRange (toMinTensor A B) := by
  rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
  exact (coe_minTensor A B).subset

/-! ### Functoriality for inclusions -/

section Inclusion

variable {A B} {A₀ : NonUnitalStarSubalgebra 𝕜 (E →L[𝕜] E)}
  {B₀ : NonUnitalStarSubalgebra 𝕜 (F →L[𝕜] F)} (hA : A₀ ≤ A) (hB : B₀ ≤ B)

/-- The star homomorphism `A₀ ⊗[𝕜] B₀ → A ⊗[𝕜] B`, `a ⊗ b ↦ a ⊗ b`, induced by inclusions
`A₀ ≤ A` and `B₀ ≤ B`. -/
def tensorInclusion : A₀ ⊗[𝕜] B₀ →⋆ₙₐ[𝕜] A ⊗[𝕜] B :=
  Algebra.TensorProduct.mapNonUnitalStarAlgHom (inclusion hA) (inclusion hB)

/-- The induced star homomorphism sends `a ⊗ b` to `a ⊗ b`. -/
@[simp]
theorem tensorInclusion_tmul (a : A₀) (b : B₀) :
    tensorInclusion hA hB (a ⊗ₜ b) = inclusion hA a ⊗ₜ inclusion hB b :=
  Algebra.TensorProduct.mapNonUnitalStarAlgHom_tmul _ _ _ _

/-- For inclusions `A₀ ≤ A` and `B₀ ≤ B`, the spatial tensor homomorphism of `A` and `B` extends
that of `A₀` and `B₀`. -/
@[simp]
theorem spatialTensorHom_tensorInclusion (x : A₀ ⊗[𝕜] B₀) :
    spatialTensorHom A B (tensorInclusion hA hB x) = spatialTensorHom A₀ B₀ x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  | tmul a b => simp

/-- The map of algebraic tensor products induced by inclusions is injective. -/
theorem tensorInclusion_injective : Function.Injective (tensorInclusion hA hB) := by
  rw [tensorInclusion, Algebra.TensorProduct.coe_mapNonUnitalStarAlgHom]
  exact TensorProduct.map_injective_of_flat_flat _ _ (inclusion_injective hA)
    (inclusion_injective hB)

/-- **The spatial norm is functorial for inclusions**: for `A₀ ≤ A` and `B₀ ≤ B`, the inclusion
`A₀ ⊗[𝕜] B₀ → A ⊗[𝕜] B` is isometric for the spatial norms. -/
@[simp]
theorem spatialNorm_tensorInclusion (x : A₀ ⊗[𝕜] B₀) :
    spatialNorm A B (tensorInclusion hA hB x) = spatialNorm A₀ B₀ x := by
  rw [spatialNorm_def, spatialNorm_def, spatialTensorHom_tensorInclusion]

include hA hB in
/-- **Monotonicity of the spatial tensor product**: `A₀ ⊗_min B₀ ⊆ A ⊗_min B` for `A₀ ≤ A` and
`B₀ ≤ B`. As both are closed star subalgebras of `B(E ⊗₂ F)` carrying the operator norm, the
inclusion is isometric. -/
@[gcongr]
theorem minTensor_mono : minTensor A₀ B₀ ≤ minTensor A B :=
  minTensor_le A₀ B₀ (isClosed_minTensor A B) (by
    rintro _ ⟨x, rfl⟩
    have h := spatialTensorHom_mem_minTensor A B (tensorInclusion hA hB x)
    rw [spatialTensorHom_tensorInclusion] at h
    exact h)

/-- The inclusion `A₀ ⊗_min B₀ → A ⊗_min B` extends the inclusion of algebraic tensor
products. -/
@[simp]
theorem inclusion_toMinTensor (x : A₀ ⊗[𝕜] B₀) :
    inclusion (minTensor_mono hA hB) (toMinTensor A₀ B₀ x) =
      toMinTensor A B (tensorInclusion hA hB x) :=
  Subtype.ext <| by simp

end Inclusion

end NonUnitalStarSubalgebra
