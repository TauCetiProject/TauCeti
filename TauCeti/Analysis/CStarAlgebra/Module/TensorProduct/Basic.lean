/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.CStarAlgebra.Module.Synonym
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Algebra.Star.Basic

import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# The coefficient pairing on an algebraic tensor product

The tensor product `H ⊗[ℂ] A` is endowed with the `A`-valued pairing
`⟨ξ ⊗ a, η ⊗ b⟩ = ⟨ξ, η⟩ • (star a * b)`. The pairing induces a `Norm` function on
`WithCStarModule Aᵐᵒᵖ (H ⊗[ℂ] A)`. Under the C⋆-algebra and star-order hypotheses, this
function satisfies the norm laws and gives a normed C⋆-module. No completeness of `H` or identity
in `A` is required. The complete Hilbert C⋆-module is constructed separately in
`TauCeti.Analysis.CStarAlgebra.Module.TensorProduct.Completion`.

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

namespace TauCeti

open WithCStarModule

/-- The canonical complex bilinear map to the algebraic right C⋆-module tensor product. -/
def tensorTmul (A : Type*) [AddCommGroup A] [Module ℂ A]
    {H : Type*} [AddCommGroup H] [Module ℂ H] :
    H →ₗ[ℂ] A →ₗ[ℂ] C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) :=
  (TensorProduct.mk ℂ H A).compr₂ (linearEquiv ℂ Aᵐᵒᵖ _).symm.toLinearMap

/-- The canonical synonym equivalence sends a module pure tensor to its algebraic tensor. -/
@[simp] theorem linearEquiv_tensorTmul (A : Type*) [AddCommGroup A] [Module ℂ A]
    {H : Type*} [AddCommGroup H] [Module ℂ H] (ξ : H) (a : A) :
    linearEquiv ℂ Aᵐᵒᵖ _ (tensorTmul A ξ a) = ξ ⊗ₜ[ℂ] a := by
  simp only [tensorTmul, LinearMap.compr₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, TensorProduct.mk_apply]

end TauCeti

namespace Module.Basis

open TauCeti

variable {A H : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup H] [Module ℂ H]

/-- A finite basis identifies the algebraic tensor module with its coefficient functions. -/
noncomputable def tensorCoordinates {ι : Type*} [Finite ι] (b : Basis ι ℂ H) :
    C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) ≃ₗ[ℂ] (ι → A) := by
  classical
  exact (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).trans <|
    (TensorProduct.equivFinsuppOfBasisLeft b).trans (Finsupp.linearEquivFunOnFinite ℂ A ι)

/-- The coordinates of a pure tensor multiply its basis coordinates by its coefficient. -/
@[simp] theorem tensorCoordinates_tensorTmul {ι : Type*} [Finite ι]
    (b : Basis ι ℂ H) (ξ : H) (a : A) (i : ι) :
    b.tensorCoordinates (tensorTmul A ξ a) i = b.repr ξ i • a := by
  classical
  simp [tensorCoordinates]

/-- The inverse coordinate map sums each basis vector tensored with its coefficient. -/
theorem tensorCoordinates_symm_apply {ι : Type*} [Fintype ι]
    (b : Basis ι ℂ H) (a : ι → A) :
    b.tensorCoordinates.symm a = ∑ i, tensorTmul A (b i) (a i) := by
  classical
  apply (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _).injective
  simp only [tensorCoordinates, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, TensorProduct.equivFinsuppOfBasisLeft_symm_apply, map_sum,
    linearEquiv_tensorTmul]
  exact Finsupp.sum_fintype _ _ (by simp)

end Module.Basis

namespace WithCStarModule

section RightAction

open TauCeti

variable {A H : Type*} [NonUnitalRing A] [Module ℂ A] [IsScalarTower ℂ A A]
  [AddCommGroup H] [Module ℂ H]

/-- Right multiplication acts on the coefficient factor. -/
noncomputable instance instSMulTensor : SMul Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) where
  smul a x := (linearEquiv ℂ Aᵐᵒᵖ _).symm
    ((LinearMap.mulRight ℂ (unop a)).lTensor H (linearEquiv ℂ Aᵐᵒᵖ _ x))

/-- Under the synonym equivalence, the opposite algebra acts by right multiplication on the
coefficient factor. -/
theorem linearEquiv_smul_tensor (x : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) (a : Aᵐᵒᵖ) :
    linearEquiv ℂ Aᵐᵒᵖ _ (a • x) =
      (LinearMap.mulRight ℂ (unop a)).lTensor H (linearEquiv ℂ Aᵐᵒᵖ _ x) :=
  LinearEquiv.apply_symm_apply _ _

/-- The coefficient action preserves addition and zero in the tensor argument. -/
noncomputable instance instDistribSMulTensor :
    DistribSMul Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) where
  smul_add a x y := by
    apply (linearEquiv ℂ Aᵐᵒᵖ _).injective
    simp only [linearEquiv_smul_tensor, map_add]
  smul_zero a := by
    apply (linearEquiv ℂ Aᵐᵒᵖ _).injective
    simp only [linearEquiv_smul_tensor, map_zero]

/-- The coefficient action is additive in its coefficient. -/
theorem add_smul_tensor (x : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) (a b : Aᵐᵒᵖ) :
    (a + b) • x = a • x + b • x := by
  apply (linearEquiv ℂ Aᵐᵒᵖ _).injective
  have h : LinearMap.mulRight ℂ (unop a + unop b) =
      LinearMap.mulRight ℂ (unop a) + LinearMap.mulRight ℂ (unop b) := by
    ext c
    exact mul_add c _ _
  simp only [linearEquiv_smul_tensor, map_add, unop_add, h,
    LinearMap.lTensor_add, LinearMap.add_apply]

/-- Zero coefficients act by zero on the algebraic tensor module. -/
noncomputable instance instSMulWithZeroTensor :
    SMulWithZero Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) where
  toSMulZeroClass := instDistribSMulTensor.toSMulZeroClass
  zero_smul x := by
    apply (linearEquiv ℂ Aᵐᵒᵖ _).injective
    simp only [linearEquiv_smul_tensor, unop_zero, LinearMap.mulRight_zero_eq_zero,
      LinearMap.lTensor_zero, LinearMap.zero_apply, map_zero]

/-- Coefficient multiplication composes right actions in the opposite-algebra order. -/
noncomputable instance instSemigroupActionTensor :
    SemigroupAction Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) where
  mul_smul a b x := by
    apply (linearEquiv ℂ Aᵐᵒᵖ _).injective
    simp only [linearEquiv_smul_tensor, unop_mul, LinearMap.mulRight_mul,
      LinearMap.lTensor_comp, LinearMap.comp_apply]

/-- Complex scalars commute with the algebraic coefficient action. -/
noncomputable instance instSMulCommClassTensor :
    SMulCommClass ℂ Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) where
  smul_comm c a x := by
    apply (linearEquiv ℂ Aᵐᵒᵖ _).injective
    simp only [linearEquiv_smul_tensor, map_smul]

/-- The complex and coefficient actions form a scalar tower when complex scalars commute
with left coefficient multiplication. -/
noncomputable instance instIsScalarTowerTensor [SMulCommClass ℂ A A] :
    IsScalarTower ℂ Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) where
  smul_assoc c a x := by
    apply (linearEquiv ℂ Aᵐᵒᵖ _).injective
    have h : LinearMap.mulRight ℂ (c • unop a) = c • LinearMap.mulRight ℂ (unop a) := by
      ext b
      exact mul_smul_comm c b (unop a)
    simp only [linearEquiv_smul_tensor, unop_smul, h, LinearMap.lTensor_smul,
      LinearMap.smul_apply, map_smul]

/-- Right multiplication of a pure tensor multiplies its coefficient on the right. -/
@[simp] theorem _root_.TauCeti.op_smul_tensorTmul (ξ : H) (a b : A) :
    op b • tensorTmul A ξ a = tensorTmul A ξ (a * b) := by
  apply (linearEquiv ℂ Aᵐᵒᵖ _).injective
  simp only [linearEquiv_smul_tensor, linearEquiv_tensorTmul, LinearMap.lTensor_tmul,
    unop_op, LinearMap.mulRight_apply]

end RightAction

end WithCStarModule

namespace TauCeti

section Algebraic

variable {A H : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [StarModule ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The coefficient-valued sesquilinear form on the algebraic tensor product. -/
noncomputable def tensorPairing : H ⊗[ℂ] A →ₗ⋆[ℂ] H ⊗[ℂ] A →ₗ[ℂ] A :=
  (TensorProduct.map₂ (innerₛₗ ℂ) (starLeftMulₛₗ ℂ A)).compr₂ₛₗ
    (TensorProduct.lid ℂ A).toLinearMap

/-- The coefficient-valued pairing of pure tensors is the scalar inner product times
the right coefficient pairing. -/
@[simp] theorem tensorPairing_tmul_tmul (ξ η : H) (a b : A) :
    tensorPairing (ξ ⊗ₜ[ℂ] a) (η ⊗ₜ[ℂ] b) = ⟪ξ, η⟫_ℂ • (star a * b) := by
  simp [tensorPairing]

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
    simpa only [map_sum, linearEquiv_tensorTmul,
      LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply,
      OrthonormalBasis.coe_toBasis] using congrArg (WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ _) h
  conv_lhs => rw [hexp x, hexp y]
  simp [map_sum, tensorPairing_tmul_tmul, OrthonormalBasis.inner_eq_ite]

/-- Tensoring an isometry in the Hilbert-space factor preserves the coefficient pairing. -/
@[simp] theorem tensorPairing_map_map {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (f : H →ₗᵢ[ℂ] K) (x y : H ⊗[ℂ] A) :
    tensorPairing (TensorProduct.map f.toLinearMap (LinearMap.id) x)
      (TensorProduct.map f.toLinearMap (LinearMap.id) y) = tensorPairing x y := by
  let g := TensorProduct.map f.toLinearMap (LinearMap.id : A →ₗ[ℂ] A)
  have h : ((tensorPairing.compl₂ g).comp g) = tensorPairing :=
    TensorProduct.ext' fun ξ a ↦ TensorProduct.ext' fun η b ↦ by
      simp [g, LinearMap.compl₂_apply]
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

/-- Conjugate symmetry of the algebraic coefficient pairing. -/
@[simp] theorem star_tensorPairing (x y : H ⊗[ℂ] A) :
    star (tensorPairing x y) = tensorPairing y x := by
  have h : tensorPairing = (tensorPairing (H := H) (A := A)).flip.compr₂ₛₗ
      (starLinearEquiv ℂ).toLinearMap :=
    TensorProduct.ext' fun ξ a ↦ TensorProduct.ext' fun η b ↦ by
      simp [LinearMap.compr₂ₛₗ_apply]
  simpa only [LinearMap.compr₂ₛₗ_apply, LinearMap.flip_apply, LinearEquiv.coe_coe,
    starLinearEquiv_apply] using (DFunLike.congr_fun (DFunLike.congr_fun h y) x).symm

/-- Right multiplication in the coefficient factor is right linear for the pairing. -/
@[simp] theorem tensorPairing_mulRight (x y : H ⊗[ℂ] A) (a : A) :
    tensorPairing x ((LinearMap.mulRight ℂ a).lTensor H y) = tensorPairing x y * a := by
  let g := LinearMap.mulRight ℂ a
  have h : tensorPairing.compl₂ (g.lTensor H) = tensorPairing.compr₂ₛₗ g :=
    TensorProduct.ext' fun ξ b ↦ TensorProduct.ext' fun η c ↦ by
      simp [g, LinearMap.compl₂_apply, LinearMap.compr₂ₛₗ_apply, mul_assoc]
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

/-- A tensor self-pairing is an orthonormal-coordinate dot product. Vanishing of the
coordinate vector forces the original tensor to vanish. -/
private theorem tensorPairing_self_eq_dotProduct (x : H ⊗[ℂ] A) :
    ∃ (n : ℕ) (c : Fin n → A), tensorPairing x x = star c ⬝ᵥ c ∧ (c = 0 → x = 0) := by
  obtain ⟨V, hV, hVx⟩ := TensorProduct.exists_finite_submodule_left_of_setFinite
    {x} (Set.finite_singleton x)
  obtain ⟨y, rfl⟩ := Set.singleton_subset_iff.mp hVx
  let := hV
  let b := (stdOrthonormalBasis ℂ V).toBasis
  let e := WithCStarModule.linearEquiv ℂ Aᵐᵒᵖ (V ⊗[ℂ] A)
  refine ⟨_, b.tensorCoordinates (e.symm y), ?_, ?_⟩
  · rw [LinearMap.rTensor_def, ← Submodule.subtypeₗᵢ_toLinearMap, tensorPairing_map_map,
      tensorPairing_eq_sum (stdOrthonormalBasis ℂ V)]
    simp only [dotProduct, Pi.star_apply, b, e]
  · intro hc
    have hy : y = 0 := (e.symm.trans b.tensorCoordinates).injective (by
      simpa only [LinearEquiv.trans_apply, map_zero] using hc)
    simp [hy]

end Algebraic

section Ordered

variable {A H : Type*} [NonUnitalRing A] [StarRing A] [Module ℂ A]
  [StarModule ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [PartialOrder A] [StarOrderedRing A]

/-- The coefficient pairing of an algebraic tensor with itself is nonnegative. -/
theorem tensorPairing_self_nonneg (x : H ⊗[ℂ] A) : 0 ≤ tensorPairing x x := by
  obtain ⟨n, c, hc, _⟩ := tensorPairing_self_eq_dotProduct x
  rw [hc]
  exact dotProduct_star_self_nonneg c

/-- The self-pairing vanishes exactly when the algebraic tensor vanishes. -/
@[simp] theorem tensorPairing_self_eq_zero [IsProperStar A] (x : H ⊗[ℂ] A) :
    tensorPairing x x = 0 ↔ x = 0 := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ by simp [hx]⟩
  obtain ⟨n, c, hc, hzero⟩ := tensorPairing_self_eq_dotProduct x
  exact hzero (dotProduct_star_self_eq_zero.mp (hc.symm.trans hx))

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

/-- On arbitrary algebraic tensors, the module inner product is the opposite of the pairing. -/
theorem unop_inner_tensor_eq_tensorPairing
    (x y : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) :
    unop (inner Aᵐᵒᵖ x y) =
      tensorPairing (linearEquiv ℂ Aᵐᵒᵖ _ x) (linearEquiv ℂ Aᵐᵒᵖ _ y) := rfl

/-- The opposite-valued inner product of pure tensors evaluates on their two factors. -/
@[simp] theorem _root_.TauCeti.inner_tensorTmul_tensorTmul (ξ η : H) (a b : A) :
    inner Aᵐᵒᵖ (tensorTmul A ξ a) (tensorTmul A η b) =
      op (⟪ξ, η⟫_ℂ • (star a * b)) := by
  apply unop_injective
  simp only [unop_inner_tensor_eq_tensorPairing, linearEquiv_tensorTmul,
    tensorPairing_tmul_tmul, unop_op]

/-- The `Norm` function induced by the coefficient pairing and the coefficient `Norm`.
Its norm laws under C⋆-algebra hypotheses are supplied by `instNormedAddCommGroupTensor`. -/
noncomputable instance instNormTensor [Norm Aᵐᵒᵖ] : Norm C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) :=
  CStarModule.norm Aᵐᵒᵖ

/-- The tensor `Norm` function takes the square root of the coefficient `Norm` of the
self-inner product. -/
theorem norm_tensor_eq_sqrt_norm_inner_self [Norm Aᵐᵒᵖ]
    (x : C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A)) : ‖x‖ = √‖inner Aᵐᵒᵖ x x‖ := rfl

/-- The algebraic `CStarModule` structure on the tensor product, with the induced `Norm` formula.
The actual normed structure under C⋆-algebra hypotheses is `instNormedAddCommGroupTensor`. -/
noncomputable instance instCStarModuleTensor [PartialOrder A] [StarOrderedRing A]
    [IsProperStar A] [Norm Aᵐᵒᵖ] :
    CStarModule Aᵐᵒᵖ C⋆ᵐᵒᵈ(Aᵐᵒᵖ, H ⊗[ℂ] A) where
  toInner := instInnerTensor
  inner_add_right := by
    intro x y z
    apply unop_injective
    simp only [unop_inner_tensor_eq_tensorPairing, unop_add, map_add]
  inner_self_nonneg := by exact op_nonneg.mpr (tensorPairing_self_nonneg _)
  inner_op_smul_right := by
    intro a x y
    apply unop_injective
    rw [unop_inner_tensor_eq_tensorPairing, linearEquiv_smul_tensor, tensorPairing_mulRight,
      unop_mul, unop_inner_tensor_eq_tensorPairing]
  inner_smul_right_complex := by
    intro z x y
    apply unop_injective
    simp only [unop_inner_tensor_eq_tensorPairing, unop_smul, map_smul]
  star_inner x y := by
    apply unop_injective
    rw [unop_star, unop_inner_tensor_eq_tensorPairing, star_tensorPairing,
      unop_inner_tensor_eq_tensorPairing]
  norm_eq_sqrt_norm_inner_self := norm_tensor_eq_sqrt_norm_inner_self
  inner_self {x} := by
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · apply (linearEquiv ℂ Aᵐᵒᵖ _).injective
      apply (tensorPairing_self_eq_zero _).mp
      simpa only [unop_inner_tensor_eq_tensorPairing, unop_zero] using congrArg unop hx
    · subst x
      apply unop_injective
      simp only [unop_inner_tensor_eq_tensorPairing, map_zero, unop_zero]

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
      ∑ i, star (e.toBasis.tensorCoordinates x i) * e.toBasis.tensorCoordinates y i := by
  rw [WithCStarModule.unop_inner_tensor_eq_tensorPairing, TauCeti.tensorPairing_eq_sum e]
  simp only [LinearEquiv.symm_apply_apply]

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

end WithCStarModule

namespace TauCeti

open WithCStarModule

variable {A H : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℂ A]
  [StarModule ℂ A] [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] [CStarRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The norm of an algebraic pure tensor is the product of its factor norms. -/
@[simp] theorem norm_tensorTmul (ξ : H) (a : A) :
    ‖tensorTmul A ξ a‖ = ‖ξ‖ * ‖a‖ := by
  rw [norm_tensor_eq_sqrt_norm_inner_self, inner_tensorTmul_tensorTmul, norm_op]
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [Real.sq_sqrt (norm_nonneg _)]
  simp [norm_smul, inner_self_eq_norm_sq_to_K, CStarRing.norm_star_mul_self,
    pow_two, mul_mul_mul_comm]

end TauCeti
