/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Module.Semidef
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.TensorProduct.Pi

import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# The algebraic right Hilbert C⋆-module associated to a complex inner product space

The tensor product `H ⊗[ℂ] A` is endowed with the `A`-valued pairing
`⟨ξ ⊗ a, η ⊗ b⟩ = ⟨ξ, η⟩ • (star a * b)`. Its induced norm lives on
`WithCStarModule Aᵐᵒᵖ (H ⊗[ℂ] A)`, so it does not compete with tensor norms.
No completeness of `H` or identity in `A` is required for this algebraic construction.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 4.
* The sesquilinear construction follows Mathlib's `TensorProduct.instInner`, using
  `TensorProduct.map₂` and the scalar tensor unit equivalence.
-/

public section

open scoped TensorProduct InnerProductSpace WithCStarModule ComplexOrder
open MulOpposite

namespace WithCStarModule

/-- The pure tensor in the right C⋆-module synonym. -/
def tensorTmul (A : Type*) [AddCommGroup A] [Module ℂ A]
    {H : Type*} [AddCommGroup H] [Module ℂ H] (ξ : H) (a : A) :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) := (linearEquiv ℂ Aᵐᵒᵖ _).symm (ξ ⊗ₜ[ℂ] a)

/-- The pure tensor is transported through the canonical synonym equivalence. -/
theorem tensorTmul_eq (A : Type*) [AddCommGroup A] [Module ℂ A]
    {H : Type*} [AddCommGroup H] [Module ℂ H] (ξ : H) (a : A) :
    tensorTmul A ξ a = (linearEquiv ℂ Aᵐᵒᵖ _).symm (ξ ⊗ₜ[ℂ] a) := by
  simp only [tensorTmul]

section Coordinates

variable {A H : Type*} [AddCommGroup A] [Module ℂ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The finite orthonormal-coordinate identification of the algebraic tensor product. -/
noncomputable def tensorCoordinates {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ H) :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) ≃ₗ[ℂ] (ι → A) := by
  classical
  exact (linearEquiv ℂ Aᵐᵒᵖ _).trans <|
    (TensorProduct.congr e.toBasis.equivFun (LinearEquiv.refl ℂ A)).trans <|
    (TensorProduct.comm ℂ (ι → ℂ) A).trans (TensorProduct.piScalarRight ℂ ℂ A ι)

@[simp] theorem tensorCoordinates_tensorTmul {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℂ H) (ξ : H) (a : A) (i : ι) :
    tensorCoordinates e (tensorTmul A ξ a) i = e.repr ξ i • a := by
  classical
  simp [tensorCoordinates, tensorTmul, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]

/-- The inverse coordinate map is the finite sum of orthonormal pure tensors. -/
theorem tensorCoordinates_symm_apply {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℂ H) (a : ι → A) :
    (tensorCoordinates e).symm a = ∑ i, tensorTmul A (e i) (a i) := by
  classical
  apply (tensorCoordinates e).injective
  ext i
  simp [tensorCoordinates_tensorTmul, OrthonormalBasis.repr_self]

end Coordinates

section RightAction

variable {A H : Type*} [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
  [AddCommGroup H] [Module ℂ H]

/-- Right multiplication acts on the coefficient factor. -/
noncomputable instance instSMulTensor : SMul Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) where
  smul a x := (linearEquiv ℂ Aᵐᵒᵖ _).symm
    ((LinearMap.mulRight ℂ (unop a)).lTensor H (linearEquiv ℂ Aᵐᵒᵖ _ x))

@[simp] theorem op_smul_tensorTmul (ξ : H) (a b : A) :
    op b • tensorTmul A ξ a = tensorTmul A ξ (a * b) := by
  -- Unfold the transported coefficient action before evaluating on a pure tensor.
  change (linearEquiv ℂ Aᵐᵒᵖ _).symm
    ((LinearMap.mulRight ℂ b).lTensor H (ξ ⊗ₜ[ℂ] a)) = _
  simp [tensorTmul]

end RightAction

section Algebraic

variable {A H : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [StarModule ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The right self-module pairing on the coefficient algebra, as a sesquilinear map. -/
private noncomputable def tensorCoefficientPairing : A →ₗ⋆[ℂ] A →ₗ[ℂ] A :=
  (LinearMap.mul ℂ A).comp (starLinearEquiv ℂ).toLinearMap

/-- The coefficient-valued sesquilinear form on the algebraic tensor product. -/
noncomputable def tensorPairing : H ⊗[ℂ] A →ₗ⋆[ℂ] H ⊗[ℂ] A →ₗ[ℂ] A :=
  (TensorProduct.map₂ (innerₛₗ ℂ) (tensorCoefficientPairing (A := A))).compr₂ₛₗ
    (TensorProduct.lid ℂ A).toLinearMap

@[simp] theorem tensorPairing_tmul_tmul (ξ η : H) (a b : A) :
    tensorPairing (ξ ⊗ₜ[ℂ] a) (η ⊗ₜ[ℂ] b) = ⟪ξ, η⟫_ℂ • (star a * b) := by
  simp [tensorPairing, tensorCoefficientPairing]

/-- The opposite-valued inner product encoding the usual right-module pairing.
When the C⋆-module structure is available, prefer its inner-product projection so that the
generic `CStarModule` simplification lemmas apply. -/
noncomputable instance (priority := 99) instInnerTensor :
    Inner Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) where
  inner x y := op (tensorPairing (linearEquiv ℂ Aᵐᵒᵖ _ x) (linearEquiv ℂ Aᵐᵒᵖ _ y))

@[simp] theorem inner_tensorTmul_tensorTmul (ξ η : H) (a b : A) :
    inner Aᵐᵒᵖ (tensorTmul A ξ a) (tensorTmul A η b) =
      op (⟪ξ, η⟫_ℂ • (star a * b)) := by
  exact congrArg op (tensorPairing_tmul_tmul ξ η a b)

/-- In orthonormal coordinates the tensor pairing is the sum of coefficient pairings. -/
private theorem tensorPairing_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ H)
    (x y : H ⊗[ℂ] A) :
    tensorPairing x y = ∑ i, star (tensorCoordinates e ((linearEquiv ℂ Aᵐᵒᵖ _).symm x) i) *
      tensorCoordinates e ((linearEquiv ℂ Aᵐᵒᵖ _).symm y) i := by
  classical
  have hexp (z : H ⊗[ℂ] A) : z = ∑ i, e i ⊗ₜ[ℂ]
      tensorCoordinates e ((linearEquiv ℂ Aᵐᵒᵖ _).symm z) i := by
    have h := tensorCoordinates_symm_apply e
      (tensorCoordinates e ((linearEquiv ℂ Aᵐᵒᵖ _).symm z))
    simpa [tensorTmul] using congrArg (linearEquiv ℂ Aᵐᵒᵖ _) h
  conv_lhs => rw [hexp x, hexp y]
  simp [map_sum, tensorPairing_tmul_tmul, OrthonormalBasis.inner_eq_ite]

/-- Tensoring an isometry in the Hilbert-space factor preserves the coefficient pairing. -/
private theorem tensorPairing_map_map {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (f : H →ₗᵢ[ℂ] K) (x y : H ⊗[ℂ] A) :
    tensorPairing (TensorProduct.map f.toLinearMap (LinearMap.id) x)
      (TensorProduct.map f.toLinearMap (LinearMap.id) y) = tensorPairing x y := by
  induction x using TensorProduct.inductionOn with
  | tmul ξ a =>
    induction y using TensorProduct.inductionOn with
    | tmul η b => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz]

/-- Conjugate symmetry of the algebraic coefficient pairing. -/
private theorem tensorPairing_star (x y : H ⊗[ℂ] A) :
    star (tensorPairing x y) = tensorPairing y x := by
  induction x using TensorProduct.inductionOn with
  | tmul ξ a =>
    induction y using TensorProduct.inductionOn with
    | tmul η b => simp [star_smul]
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, star_add, hy, hz]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, star_add, hx, hz]

/-- Right multiplication in the coefficient factor is right linear for the pairing. -/
private theorem tensorPairing_mulRight (x y : H ⊗[ℂ] A) (a : A) :
    tensorPairing x ((LinearMap.mulRight ℂ a).lTensor H y) = tensorPairing x y * a := by
  induction x using TensorProduct.inductionOn with
  | tmul ξ b =>
    induction y using TensorProduct.inductionOn with
    | tmul η c => simp [mul_assoc, smul_mul_assoc]
    | add y z hy hz => simp only [map_add, hy, hz, add_mul]
  | add x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, add_mul]

/-- The right-module inner product in finite orthonormal coordinates. -/
theorem unop_inner_tensor_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ H)
    (x y : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    unop (inner Aᵐᵒᵖ x y) = ∑ i, star (tensorCoordinates e x i) * tensorCoordinates e y i :=
  tensorPairing_eq_sum e _ _

end Algebraic

variable {A H : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Positivity follows by expressing a tensor in a finite orthonormal subspace. -/
private theorem tensorPairing_self_nonneg (x : H ⊗[ℂ] A) : 0 ≤ tensorPairing x x := by
  obtain ⟨V, hV, hx⟩ := TensorProduct.exists_finite_submodule_left_of_setFinite
    {x} (Set.finite_singleton x)
  let := hV
  obtain ⟨y, rfl⟩ := Set.singleton_subset_iff.mp hx
  -- The submodule inclusion tensors to `map subtype id`.
  change 0 ≤ tensorPairing (TensorProduct.map V.subtypeₗᵢ.toLinearMap (LinearMap.id) y)
    (TensorProduct.map V.subtypeₗᵢ.toLinearMap (LinearMap.id) y)
  rw [tensorPairing_map_map, tensorPairing_eq_sum (stdOrthonormalBasis ℂ V)]
  exact Finset.sum_nonneg fun _ _ ↦ star_mul_self_nonneg _

/-- The algebraic coefficient pairing is definite. -/
private theorem tensorPairing_self_eq_zero (x : H ⊗[ℂ] A) (hx : tensorPairing x x = 0) : x = 0 := by
  classical
  obtain ⟨V, hV, hmem⟩ := TensorProduct.exists_finite_submodule_left_of_setFinite
    {x} (Set.finite_singleton x)
  let := hV
  obtain ⟨y, rfl⟩ := Set.singleton_subset_iff.mp hmem
  -- The submodule inclusion tensors to `map subtype id`.
  change tensorPairing (TensorProduct.map V.subtypeₗᵢ.toLinearMap (LinearMap.id) y)
    (TensorProduct.map V.subtypeₗᵢ.toLinearMap (LinearMap.id) y) = 0 at hx
  rw [tensorPairing_map_map, tensorPairing_eq_sum (stdOrthonormalBasis ℂ V)] at hx
  have hc := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦
    star_mul_self_nonneg (tensorCoordinates (stdOrthonormalBasis ℂ V)
      ((linearEquiv ℂ Aᵐᵒᵖ _).symm y) i)).mp hx
  have hy : y = 0 := by
    apply (linearEquiv ℂ Aᵐᵒᵖ _).symm.injective
    apply (tensorCoordinates (stdOrthonormalBasis ℂ V)).injective
    ext i
    simpa using (star_mul_self_eq_zero.mp (hc i (Finset.mem_univ i)))
  simp [hy]

/-- The norm induced by the `A`-valued tensor pairing. -/
noncomputable instance instNormTensor : Norm C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) :=
  CStarModule.norm Aᵐᵒᵖ

/-- The algebraic tensor product is a pre-Hilbert right C⋆-module. -/
noncomputable instance instCStarModuleTensor :
    CStarModule Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) where
  toInner := instInnerTensor
  inner_add_right := by intros; exact congrArg op (map_add (tensorPairing _) _ _)
  inner_self_nonneg := by exact op_nonneg.mpr (tensorPairing_self_nonneg _)
  inner_op_smul_right := by
    intro a x y
    exact congrArg op (tensorPairing_mulRight _ _ (unop a))
  inner_smul_right_complex := by
    intro z x y
    exact congrArg op (map_smul (tensorPairing _) z _)
  star_inner x y := by exact congrArg op (tensorPairing_star _ _)
  norm_eq_sqrt_norm_inner_self _ := rfl
  inner_self {x} := by
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · apply (linearEquiv ℂ Aᵐᵒᵖ _).injective
      exact tensorPairing_self_eq_zero _ (op_injective hx)
    · subst x
      exact congrArg op (by simp)

/-- The tensor pairing defines the normed additive group structure. -/
noncomputable instance instNormedAddCommGroupTensor :
    NormedAddCommGroup C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) := CStarModule.normedAddCommGroup Aᵐᵒᵖ

/-- Use the module norm uniformity even when a tensor norm on the underlying type is available. -/
noncomputable instance (priority := 1100) instUniformSpaceTensor :
    UniformSpace C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) := instNormedAddCommGroupTensor.toUniformSpace

/-- Use the module norm bornology even when the underlying tensor has a bornology. -/
noncomputable instance (priority := 1100) instBornologyTensor :
    Bornology C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) := instNormedAddCommGroupTensor.toBornology

/-- Complex scalar multiplication is bounded for the tensor module norm. -/
noncomputable instance instNormedSpaceTensor :
    NormedSpace ℂ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) := .ofCore (CStarModule.normedSpaceCore Aᵐᵒᵖ)

end WithCStarModule
