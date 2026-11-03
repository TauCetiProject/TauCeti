/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BaseChange.Module
public import TauCeti.Algebra.Lie.BaseChange.MaxTrivSubmodule
public import TauCeti.LinearAlgebra.TensorProduct.Hom

/-!
# Scalar extension of Lie-module Hom spaces

For a finite projective source module and a finitely generated acting Lie algebra, flat
scalar extension commutes with taking equivariant linear maps. In particular, extension of
fields preserves the dimension of the space of intertwiners. This comparison allows rational
representations to be compared with their scalar extensions without assuming that all
intertwiners individually descend.

The construction uses Mathlib's identification of Lie-module maps with invariant vectors in
the linear-map module, together with `LinearMap.isBaseChange_baseChangeHom` and
`LieModule.maxTrivSubmodule_baseChange`.

## References

* Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2 (representations and scalar extension).
* Jantzen, *Representations of Algebraic Groups*, II.1 (integral forms and scalar extension).
-/

public section

open scoped TensorProduct
open LieModule TensorProduct

namespace LieModule

variable {R L M N : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
  (A : Type*) [CommRing A] [Algebra R A]
  [Module.Finite R M] [Module.Projective R M]

/-- Scalar extension of linear-map spaces respects the Lie action on intertwiners. -/
noncomputable def linearMapBaseChangeEquiv :
    A ⊗[R] (M →ₗ[R] N) ≃ₗ⁅A,A ⊗[R] L⁆ (A ⊗[R] M →ₗ[A] A ⊗[R] N) := by
  let e := (LinearMap.isBaseChange_baseChangeHom R A M N).equiv
  have he (x : A ⊗[R] L) (f : A ⊗[R] (M →ₗ[R] N)) : e ⁅x, f⁆ = ⁅x, e f⁆ := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy =>
      simp only [add_lie (M := A ⊗[R] (M →ₗ[R] N)),
        add_lie (L := A ⊗[R] L) (M := A ⊗[R] M →ₗ[A] A ⊗[R] N), map_add, hx, hy]
    | tmul a x =>
      induction f using TensorProduct.inductionOn with
      | add f g hf hg =>
        simp only [lie_add (M := A ⊗[R] (M →ₗ[R] N)),
          lie_add (L := A ⊗[R] L) (M := A ⊗[R] M →ₗ[A] A ⊗[R] N), map_add, hf, hg]
      | tmul b f =>
        ext m
        simp [e, IsBaseChange.equiv_tmul, LieHom.lie_apply,
          LieAlgebra.ExtendScalars.bracket_tmul, tmul_sub, smul_sub,
          smul_tmul', mul_comm]
  exact { __ := e, map_lie' := he _ _ }

/-- On pure tensors the linear-map comparison is scalar multiplication of the extended map. -/
@[simp] theorem linearMapBaseChangeEquiv_tmul (a : A) (f : M →ₗ[R] N) :
    linearMapBaseChangeEquiv (L := L) A (a ⊗ₜ[R] f) = a • f.baseChange A :=
  IsBaseChange.equiv_tmul _ _ _

end LieModule

namespace LieModuleHom

variable {R L M N : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
  (A : Type*) [CommRing A] [Algebra R A]
  [Module.Finite R M] [Module.Projective R M] [Module.Finite R L] [Module.Flat R A]

/-- Flat scalar extension commutes with the space of Lie-module maps when the source is
finite projective and the acting Lie algebra is finitely generated. -/
noncomputable def baseChangeEquiv :
    A ⊗[R] (M →ₗ⁅R,L⁆ N) ≃ₗ[A] (A ⊗[R] M →ₗ⁅A,A ⊗[R] L⁆ A ⊗[R] N) :=
  (maxTrivLinearMapEquivLieModuleHom (R := R) (L := L) (M := M) (N := N)).symm.baseChange
      R A _ _ ≪≫ₗ
    Submodule.toBaseChange.toLinearEquiv A
      (maxTrivSubmodule R L (M →ₗ[R] N) : Submodule R (M →ₗ[R] N)) ≪≫ₗ
    LinearEquiv.ofEq _ _ (by
      simpa only [LieSubmodule.coe_baseChange] using
        congrArg LieSubmodule.toSubmodule
          (maxTrivSubmodule_baseChange R A L (M →ₗ[R] N)).symm) ≪≫ₗ
    (maxTrivEquiv
      (linearMapBaseChangeEquiv (R := R) (L := L) (M := M) (N := N) A)).toLinearEquiv ≪≫ₗ
    maxTrivLinearMapEquivLieModuleHom

/-- Forgetting equivariance on a pure tensor recovers the linear-map comparison. -/
theorem toLinearMap_baseChangeEquiv_tmul (a : A) (f : M →ₗ⁅R,L⁆ N) :
    (baseChangeEquiv A (a ⊗ₜ[R] f)).toLinearMap =
      linearMapBaseChangeEquiv (L := L) A (a ⊗ₜ[R] f.toLinearMap) := by
  simp only [baseChangeEquiv, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    toLinearMap_maxTrivLinearMapEquivLieModuleHom, LieModuleEquiv.coe_toLinearEquiv]
  rw [coe_maxTrivEquiv_apply]
  apply congrArg (linearMapBaseChangeEquiv (L := L) A)
  -- State the transport in the ambient tensor product so its subtype coercion is explicit.
  calc
    _ = (Submodule.toBaseChange.toLinearEquiv A
        (maxTrivSubmodule R L (M →ₗ[R] N) : Submodule R (M →ₗ[R] N))
        (a ⊗ₜ[R] maxTrivLinearMapEquivLieModuleHom.symm f) : A ⊗[R] (M →ₗ[R] N)) :=
      LinearEquiv.coe_ofEq_apply _ _
    _ = _ := by
      rw [Submodule.toBaseChange.toLinearEquiv_apply, Submodule.coe_toBaseChange_tmul,
        toLinearMap_maxTrivLinearMapEquivLieModuleHom_symm]

/-- The Hom-space comparison sends a pure tensor to the corresponding scalar multiple of
the extended Lie-module map. -/
@[simp] theorem baseChangeEquiv_tmul (a : A) (f : M →ₗ⁅R,L⁆ N) :
    baseChangeEquiv A (a ⊗ₜ[R] f) = a • f.baseChange A := by
  ext b
  simp only [← LieModuleHom.coe_toLinearMap, toLinearMap_baseChangeEquiv_tmul,
    linearMapBaseChangeEquiv_tmul, baseChange_toLinearMap, smul_apply,
    LinearMap.smul_apply]

end LieModuleHom

namespace LieModuleHom

variable (K A L M N : Type*) [Field K] [Field A] [Algebra K A]
  [LieRing L] [LieAlgebra K L] [Module.Finite K L]
  [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [AddCommGroup N] [Module K N] [LieRingModule L N] [LieModule K L N]
  [Module.Finite K M]

/-- Extension of fields preserves the dimension of the space of Lie-module maps.
No finite-dimensionality assumption on the target module is needed. -/
@[simp] theorem finrank_baseChange :
    Module.finrank A (A ⊗[K] M →ₗ⁅A,A ⊗[K] L⁆ A ⊗[K] N) =
      Module.finrank K (M →ₗ⁅K,L⁆ N) :=
  (baseChangeEquiv (R := K) (L := L) (M := M) (N := N) A).finrank_eq.symm.trans
    Module.finrank_baseChange

end LieModuleHom
