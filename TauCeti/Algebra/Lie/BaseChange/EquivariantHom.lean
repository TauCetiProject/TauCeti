/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BaseChange.Module
import TauCeti.Algebra.Lie.Basic
public import TauCeti.Algebra.Lie.BaseChange.MaxTrivSubmodule
public import TauCeti.LinearAlgebra.TensorProduct.Hom
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Scalar extension of equivariant Hom spaces

For a finitely generated Lie algebra and a finite projective source module, equivariant
Hom spaces commute with flat scalar extension. In particular, extension of fields preserves
the dimension of the space of intertwiners between finite-dimensional Lie modules. This
lets intertwiner dimensions between rational representations be computed after extending the field.

The construction restricts the linear-Hom comparison
`LinearMap.isBaseChange_baseChangeHom` to invariant vectors, using
`LieModule.maxTrivSubmodule_baseChange` and Mathlib's
`LieModule.maxTrivLinearMapEquivLieModuleHom`. No finite-generation hypothesis on the target
module, semisimplicity, or characteristic restriction is needed.

## Main definitions

* `LieModule.linearMapTensorProduct`: scalar extension of linear maps, equivariant for the
  usual commutator actions on Hom spaces.
* `LieModuleHom.baseChangeEquiv`: the scalar-extension equivalence for equivariant maps.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2 (representations and scalar extension).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §20.
-/

public section

open scoped TensorProduct

variable {R : Type*} [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
  (L M N : Type*) [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]

namespace LieModule

/-- Scalar extension of linear maps intertwines the commutator actions on the Hom spaces. -/
def linearMapTensorProduct :
    (A ⊗[R] (M →ₗ[R] N)) →ₗ⁅A,A ⊗[R] L⁆
      ((A ⊗[R] M) →ₗ[A] (A ⊗[R] N)) where
  toLinearMap := LinearMap.tensorProduct R A M N
  map_lie' {x f} := by
    dsimp only [LinearMap.toFun_eq_coe]
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [add_lie, map_add, hx, hy]
    | tmul a x =>
      induction f using TensorProduct.inductionOn with
      | add f g hf hg =>
        rw [lie_add, map_add, hf, hg, map_add]
        apply LinearMap.ext
        intro w
        simp [LieHom.lie_apply, sub_add_sub_comm]
      | tmul b f =>
        apply LinearMap.ext
        intro z
        induction z using TensorProduct.inductionOn with
        | add z w hz hw => simp only [map_add, hz, hw]
        | tmul c m =>
          simp [LinearMap.tensorProduct, LieAlgebra.ExtendScalars.bracket_tmul,
            LieHom.lie_apply, TensorProduct.tmul_sub, smul_sub,
            TensorProduct.smul_tmul', smul_eq_mul, mul_left_comm, mul_comm]

/-- On pure tensors the Hom comparison sends `a ⊗ f` and `b ⊗ m` to `ab ⊗ f(m)`. -/
@[simp]
theorem linearMapTensorProduct_tmul_apply (a b : A) (f : M →ₗ[R] N) (m : M) :
    linearMapTensorProduct A L M N (a ⊗ₜ f) (b ⊗ₜ m) = (a * b) ⊗ₜ f m := by
  simp [linearMapTensorProduct, LinearMap.tensorProduct, TensorProduct.smul_tmul']

/-- The underlying linear map is Mathlib's scalar-extension comparison for Hom spaces. -/
@[simp]
theorem linearMapTensorProduct_toLinearMap :
    (linearMapTensorProduct A L M N).toLinearMap = LinearMap.tensorProduct R A M N :=
  (rfl)

end LieModule

namespace LieModuleHom

variable [Module.Finite R L] [Module.Finite R M] [Module.Projective R M] [Module.Flat R A]

/-- Equivariant Hom spaces commute with flat scalar extension when the Lie algebra is
finitely generated and the source module is finite projective. -/
noncomputable def baseChangeEquiv :
    A ⊗[R] (M →ₗ⁅R,L⁆ N) ≃ₗ[A]
      ((A ⊗[R] M) →ₗ⁅A,A ⊗[R] L⁆ (A ⊗[R] N)) := by
  let e := LieModule.maxTrivLinearMapEquivLieModuleHom (R := R) (L := L) (M := M) (N := N)
  let p := (LieModule.maxTrivSubmodule R L (M →ₗ[R] N)).toSubmodule
  have hp : p.baseChange A =
      (LieModule.maxTrivSubmodule A (A ⊗[R] L) (A ⊗[R] (M →ₗ[R] N))).toSubmodule := by
    dsimp only [p]
    rw [← LieSubmodule.coe_baseChange, LieModule.maxTrivSubmodule_baseChange]
  have hb : Function.Bijective (LieModule.linearMapTensorProduct (R := R) A L M N) := by
    convert (LinearMap.isBaseChange_baseChangeHom R A M N).equiv.bijective using 1
    funext z
    induction z using TensorProduct.inductionOn with
    | tmul a f =>
      apply LinearMap.ext
      intro w
      simp [LieModule.linearMapTensorProduct, LinearMap.tensorProduct,
        IsBaseChange.equiv_tmul]
    | add z w hz hw => simp only [map_add, hz, hw]
  let E := TauCeti.LieModuleEquiv.ofBijective
    (LieModule.linearMapTensorProduct (R := R) A L M N) hb
  exact (e.symm.baseChange R A _ _).trans
    ((Submodule.toBaseChange.toLinearEquiv A p).trans
      ((LinearEquiv.ofEq _ _ hp).trans
        ((LieModule.maxTrivEquiv E).toLinearEquiv.trans
          (LieModule.maxTrivLinearMapEquivLieModuleHom (R := A) (L := A ⊗[R] L)
            (M := A ⊗[R] M) (N := A ⊗[R] N)))))

/-- The scalar-extension equivalence evaluates a pure tensor of intertwiners by the usual
extension-of-scalars formula. -/
private theorem baseChangeEquiv_tmul_apply (a b : A) (f : M →ₗ⁅R,L⁆ N) (m : M) :
    baseChangeEquiv A L M N (a ⊗ₜ f) (b ⊗ₜ m) = (a * b) ⊗ₜ f m := by
  let p := (LieModule.maxTrivSubmodule R L (M →ₗ[R] N)).toSubmodule
  -- Compute the underlying value, rather than rewriting the range subtype's carrier.
  have hcoe (x : A ⊗[R] p) :
      ((Submodule.toBaseChange.toLinearEquiv A p) x : A ⊗[R] (M →ₗ[R] N)) =
        p.subtype.baseChange A x :=
    congrArg (fun y : p.baseChange A => (y : A ⊗[R] (M →ₗ[R] N)))
      (Submodule.toBaseChange.toLinearEquiv_apply A p x)
  dsimp only [p] at hcoe
  simp only [baseChangeEquiv, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
  simp only [LieModule.maxTrivEquiv, LieModule.coe_maxTrivLinearMapEquivLieModuleHom]
  simp [hcoe]

/-- A pure tensor of an equivariant map extends to its scalar multiple after base change. -/
@[simp]
theorem baseChangeEquiv_tmul (a : A) (f : M →ₗ⁅R,L⁆ N) :
    baseChangeEquiv A L M N (a ⊗ₜ f) = a • f.baseChange A := by
  ext x
  induction x using TensorProduct.inductionOn with
  | tmul b m => simp [baseChangeEquiv_tmul_apply, TensorProduct.smul_tmul']
  | add x y hx hy => simp only [map_add, hx, hy]

end LieModuleHom

namespace LieModuleHom

variable (K E : Type*) [Field K] [Field E] [Algebra K E]
  (L M N : Type*) [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [Module.Finite K M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]

/-- Extension of fields preserves the `finrank` of the space of equivariant maps from a
finite-dimensional Lie module, for a finite-dimensional acting Lie algebra. -/
theorem finrank_baseChange :
    Module.finrank E ((E ⊗[K] M) →ₗ⁅E,E ⊗[K] L⁆ (E ⊗[K] N)) =
      Module.finrank K (M →ₗ⁅K,L⁆ N) := by
  rw [← (baseChangeEquiv E L M N).finrank_eq, Module.finrank_baseChange]

end LieModuleHom
