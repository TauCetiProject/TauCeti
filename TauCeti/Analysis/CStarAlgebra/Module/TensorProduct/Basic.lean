/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.CStarAlgebra.Module.Synonym
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.TensorProduct.Basis

import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# The algebraic right Hilbert C⋆-module associated to a complex inner product space

The tensor product `H ⊗[ℂ] A` is endowed with the `A`-valued pairing
`⟨ξ ⊗ a, η ⊗ b⟩ = ⟨ξ, η⟩ • (star a * b)`. Its induced norm lives on
`WithCStarModule Aᵐᵒᵖ (H ⊗[ℂ] A)`, so it does not compete with tensor norms.
No completeness of `H` or identity in `A` is required for this algebraic construction.

## References

* E. Christopher Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Chapter 4.
* The sesquilinear construction follows Mathlib's `TensorProduct.instInner`, using
  `TensorProduct.map₂` and the scalar tensor unit equivalence. The finite-subspace reduction
  and orthonormal-coordinate proof of positive definiteness adapt the argument in
  `Mathlib/Analysis/InnerProductSpace/TensorProduct.lean`.
-/

public section

open scoped TensorProduct InnerProductSpace WithCStarModule ComplexOrder
open MulOpposite

namespace WithCStarModule

/-- The pure tensor in the right C⋆-module synonym. -/
def tensorTmul (A : Type*) [AddCommGroup A] [Module ℂ A]
    {H : Type*} [AddCommGroup H] [Module ℂ H] (ξ : H) (a : A) :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) := (linearEquiv ℂ Aᵐᵒᵖ _).symm (ξ ⊗ₜ[ℂ] a)

/-- The canonical synonym equivalence sends a module pure tensor to its algebraic tensor. -/
@[simp] theorem linearEquiv_tensorTmul (A : Type*) [AddCommGroup A] [Module ℂ A]
    {H : Type*} [AddCommGroup H] [Module ℂ H] (ξ : H) (a : A) :
    linearEquiv ℂ Aᵐᵒᵖ _ (tensorTmul A ξ a) = ξ ⊗ₜ[ℂ] a := by
  simp only [tensorTmul, LinearEquiv.apply_symm_apply]

end WithCStarModule

namespace Module.Basis

variable {A H : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup H] [Module ℂ H]

/-- A finite basis identifies the algebraic tensor module with its coefficient functions. -/
noncomputable def tensorCoordinates {ι : Type*} [Fintype ι] (b : Basis ι ℂ H) :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) ≃ₗ[ℂ] (ι → A) := by
  classical
  exact (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).trans <|
    (TensorProduct.equivFinsuppOfBasisLeft b).trans (Finsupp.linearEquivFunOnFinite ℂ A ι)

/-- The coordinates of a pure tensor multiply its basis coordinates by its coefficient. -/
@[simp] theorem tensorCoordinates_tensorTmul {ι : Type*} [Fintype ι]
    (b : Basis ι ℂ H) (ξ : H) (a : A) (i : ι) :
    b.tensorCoordinates (WithCStarModule.tensorTmul A ξ a) i = b.repr ξ i • a := by
  classical
  simp [tensorCoordinates]

/-- The inverse coordinate map sums each basis vector tensored with its coefficient. -/
theorem tensorCoordinates_symm_apply {ι : Type*} [Fintype ι]
    (b : Basis ι ℂ H) (a : ι → A) :
    b.tensorCoordinates.symm a = ∑ i, WithCStarModule.tensorTmul A (b i) (a i) := by
  classical
  apply (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).injective
  simp only [tensorCoordinates, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, TensorProduct.equivFinsuppOfBasisLeft_symm_apply, map_sum,
    WithCStarModule.linearEquiv_tensorTmul]
  exact Finsupp.sum_of_support_subset _ (Finset.subset_univ _) _ (by simp)

end Module.Basis

namespace WithCStarModule

section RightAction

variable {A H : Type*} [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
  [AddCommGroup H] [Module ℂ H]

/-- Right multiplication acts on the coefficient factor. -/
noncomputable instance instSMulTensor : SMul Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) where
  smul a x := (linearEquiv ℂ Aᵐᵒᵖ _).symm
    ((LinearMap.mulRight ℂ (unop a)).lTensor H (linearEquiv ℂ Aᵐᵒᵖ _ x))

/-- Right multiplication of a pure tensor multiplies its coefficient on the right. -/
@[simp] theorem op_smul_tensorTmul (ξ : H) (a b : A) :
    op b • tensorTmul A ξ a = tensorTmul A ξ (a * b) := by
  unfold HSMul.hSMul instHSMul SMul.smul instSMulTensor
  simp [tensorTmul]

end RightAction

end WithCStarModule

namespace TauCeti

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

/-- The coefficient-valued pairing of pure tensors is the scalar inner product times
the right coefficient pairing. -/
@[simp] theorem tensorPairing_tmul_tmul (ξ η : H) (a b : A) :
    tensorPairing (ξ ⊗ₜ[ℂ] a) (η ⊗ₜ[ℂ] b) = ⟪ξ, η⟫_ℂ • (star a * b) := by
  simp [tensorPairing, tensorCoefficientPairing]

/-- In orthonormal coordinates the tensor pairing is the sum of coefficient pairings. -/
private theorem tensorPairing_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ H)
    (x y : H ⊗[ℂ] A) :
    tensorPairing x y =
      ∑ i, star (e.toBasis.tensorCoordinates
          ((WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).symm x) i) *
        e.toBasis.tensorCoordinates ((WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).symm y) i := by
  classical
  have hexp (z : H ⊗[ℂ] A) : z = ∑ i, e i ⊗ₜ[ℂ]
      e.toBasis.tensorCoordinates ((WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).symm z) i := by
    have h := e.toBasis.tensorCoordinates_symm_apply
      (e.toBasis.tensorCoordinates ((WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).symm z))
    simpa only [map_sum, WithCStarModule.linearEquiv_tensorTmul,
      LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply,
      OrthonormalBasis.coe_toBasis] using congrArg (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _) h
  conv_lhs => rw [hexp x, hexp y]
  simp [map_sum, tensorPairing_tmul_tmul, OrthonormalBasis.inner_eq_ite]

/-- Tensoring an isometry in the Hilbert-space factor preserves the coefficient pairing. -/
theorem tensorPairing_map_map {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
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
private theorem star_tensorPairing (x y : H ⊗[ℂ] A) :
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

end Algebraic

section Ordered

variable {A H : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [StarModule ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

omit [StarRing A] [StarModule ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] in
/-- Every algebraic tensor comes from a finite dimensional subspace of its first factor. -/
private theorem exists_finite_tensor_preimage (x : H ⊗[ℂ] A) :
    ∃ (V : Submodule ℂ H) (_ : Module.Finite ℂ V) (y : V ⊗[ℂ] A),
      TensorProduct.map V.subtypeₗᵢ.toLinearMap (LinearMap.id) y = x := by
  obtain ⟨V, hV, hx⟩ := TensorProduct.exists_finite_submodule_left_of_setFinite
    {x} (Set.finite_singleton x)
  obtain ⟨y, hy⟩ := Set.singleton_subset_iff.mp hx
  exact ⟨V, hV, y, by simpa only [LinearMap.rTensor_def,
    Submodule.subtypeₗᵢ_toLinearMap] using hy⟩

variable [PartialOrder A] [StarOrderedRing A]

/-- The coefficient pairing of an algebraic tensor with itself is nonnegative. -/
private theorem tensorPairing_self_nonneg (x : H ⊗[ℂ] A) : 0 ≤ tensorPairing x x := by
  obtain ⟨V, hV, y, rfl⟩ := exists_finite_tensor_preimage x
  let := hV
  rw [tensorPairing_map_map, tensorPairing_eq_sum (stdOrthonormalBasis ℂ V)]
  exact dotProduct_star_self_nonneg _

/-- Vanishing of the self-pairing implies that the algebraic tensor is zero. -/
private theorem eq_zero_of_tensorPairing_self_eq_zero [IsProperStar A]
    (x : H ⊗[ℂ] A) (hx : tensorPairing x x = 0) : x = 0 := by
  obtain ⟨V, hV, y, rfl⟩ := exists_finite_tensor_preimage x
  let := hV
  rw [tensorPairing_map_map, tensorPairing_eq_sum (stdOrthonormalBasis ℂ V)] at hx
  have hc := dotProduct_star_self_eq_zero.mp hx
  have hy : y = 0 := by
    apply (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).symm.injective
    apply (stdOrthonormalBasis ℂ V).toBasis.tensorCoordinates.injective
    simpa using hc
  simp [hy]

end Ordered

end TauCeti

namespace WithCStarModule

section Algebraic

variable {A H : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [StarModule ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

open TauCeti

/-- The opposite-valued inner product encoding the usual right-module pairing.
When the C⋆-module structure is available, prefer its inner-product projection so that the
generic `CStarModule` simplification lemmas apply. -/
noncomputable instance (priority := 99) instInnerTensor :
    Inner Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) where
  inner x y := op (tensorPairing (linearEquiv ℂ Aᵐᵒᵖ _ x) (linearEquiv ℂ Aᵐᵒᵖ _ y))

/-- The opposite-valued inner product of pure tensors evaluates on their two factors. -/
@[simp] theorem inner_tensorTmul_tensorTmul (ξ η : H) (a b : A) :
    inner Aᵐᵒᵖ (tensorTmul A ξ a) (tensorTmul A η b) =
      op (⟪ξ, η⟫_ℂ • (star a * b)) := by
  exact congrArg op (tensorPairing_tmul_tmul ξ η a b)

/-- On arbitrary algebraic tensors, the module inner product is the opposite of the pairing. -/
theorem unop_inner_tensor_eq_tensorPairing
    (x y : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    unop (inner Aᵐᵒᵖ x y) =
      tensorPairing (linearEquiv ℂ Aᵐᵒᵖ _ x) (linearEquiv ℂ Aᵐᵒᵖ _ y) := rfl

/-- The norm induced by the `A`-valued tensor pairing. -/
noncomputable instance instNormTensor [Norm Aᵐᵒᵖ] : Norm C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) :=
  CStarModule.norm Aᵐᵒᵖ

/-- The algebraic tensor product is a pre-Hilbert right C⋆-module. -/
noncomputable instance instCStarModuleTensor [PartialOrder A] [StarOrderedRing A]
    [IsProperStar A] [Norm Aᵐᵒᵖ] :
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
  star_inner x y := by exact congrArg op (star_tensorPairing _ _)
  norm_eq_sqrt_norm_inner_self _ := rfl
  inner_self {x} := by
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · apply (linearEquiv ℂ Aᵐᵒᵖ _).injective
      exact eq_zero_of_tensorPairing_self_eq_zero _ (op_injective hx)
    · subst x
      exact congrArg op (by simp)

end Algebraic

end WithCStarModule

namespace OrthonormalBasis

variable {A H : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [StarModule ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The right-module inner product is the sum of coefficient pairings in orthonormal coordinates. -/
theorem unop_inner_tensor_eq_sum {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℂ H)
    (x y : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    unop (inner Aᵐᵒᵖ x y) =
      ∑ i, star (e.toBasis.tensorCoordinates x i) * e.toBasis.tensorCoordinates y i :=
  TauCeti.tensorPairing_eq_sum e _ _

end OrthonormalBasis

namespace WithCStarModule

variable {A H : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

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

/-- The norm of an algebraic pure tensor is the product of its factor norms. -/
@[simp] theorem norm_tensorTmul (ξ : H) (a : A) :
    ‖tensorTmul A ξ a‖ = ‖ξ‖ * ‖a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [CStarModule.norm_sq_eq Aᵐᵒᵖ, inner_tensorTmul_tensorTmul, norm_op]
  simp [norm_smul, inner_self_eq_norm_sq_to_K, CStarRing.norm_star_mul_self,
    pow_two, mul_mul_mul_comm]

end WithCStarModule
