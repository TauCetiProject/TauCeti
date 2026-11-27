/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import TauCeti.Algebra.TensorProduct.Module.RightAction

/-!
# Scalar extension of adjoint pairs

Extending scalars preserves adjointness for bilinear forms. In particular, a star-adjoint action
extends to the tensor-product algebra when the new scalars have trivial involution.
-/

public section

open scoped TensorProduct

namespace LinearMap

variable {R A M N : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Base changes of mutually adjoint maps are mutually adjoint for the base-changed forms. -/
theorem IsAdjointPair.baseChange {B : LinearMap.BilinForm R M} {C : LinearMap.BilinForm R N}
    {f : M →ₗ[R] N} {g : N →ₗ[R] M} (h : IsAdjointPair B C f g) :
    IsAdjointPair (B.baseChange A) (C.baseChange A) (f.baseChange A) (g.baseChange A) := by
  rw [isAdjointPair_iff_comp_eq_compl₂]
  ext x y
  simp [h x y]

end LinearMap

namespace LinearMap.BilinForm

variable {R A O L : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [Semiring O] [AddCommMonoid L] [Module R L] [Module O L]

attribute [local instance low] TensorProduct.rightModule

/-- The right-factor action of the original scalars remains star-adjoint after base change. -/
theorem baseChange_rightModule_adjoint [Star O] [SMulCommClass R O L]
    (B : LinearMap.BilinForm R L) (b : O)
    (h : ∀ x y, B (b • x) y = B x (star b • y)) (x y : A ⊗[R] L) :
    B.baseChange A (b • x) y = B.baseChange A x (star b • y) := by
  let _ := SMulCommClass.symm R O L
  have hpair : IsAdjointPair B B (Module.toModuleEnd R L b) (Module.toModuleEnd R L (star b)) := by
    intro x y
    simpa only [Module.toModuleEnd_apply, DistribSMul.toLinearMap_apply] using h x y
  simpa only [TensorProduct.rightModule_smul_eq_lTensor, LinearMap.baseChange_eq_lTensor]
    using hpair.baseChange (A := A) x y

/-- A star-adjoint action extends to the tensor-product algebra over scalars with trivial star. -/
theorem baseChange_tensor_adjoint [StarRing R] [StarAddMonoid A] [TrivialStar A] [StarAddMonoid O]
    [Algebra R O] [StarModule R A] [StarModule R O] [IsScalarTower R O L]
    (B : LinearMap.BilinForm R L) (h : ∀ (b : O) x y, B (b • x) y = B x (star b • y))
    (c : A ⊗[R] O) (x y : A ⊗[R] L) :
    let ρ := TauCeti.BialgebraModule.tensorPairAction R A L
    B.baseChange A (ρ c x) y = B.baseChange A x (ρ (star c) y) := by
  intro ρ
  induction c using TensorProduct.inductionOn with
  | tmul a b =>
    rw [TensorProduct.star_tmul, star_trivial, TauCeti.BialgebraModule.tensorPairAction_tmul_apply,
      TauCeti.BialgebraModule.tensorPairAction_tmul_apply, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right,
      B.baseChange_rightModule_adjoint b (h b)]
  | add c d hc hd =>
    simp only [star_add, map_add, LinearMap.add_apply, hc, hd]

end LinearMap.BilinForm
