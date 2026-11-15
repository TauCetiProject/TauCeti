/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.NormTwoShell.FullCartan.CoverLift
public import TauCeti.LinearAlgebra.FixedSubmodule
public import TauCeti.LinearAlgebra.FixedSubmodule.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Fixed Cartan and root parts of the full signed shell algebra

The pinned action on `Matrix.FullShellLieAlgebra D` preserves its Cartan and root parts.
Its integral fixed module is therefore the product of the fixed module of the actual Cartan
automorphism and the fixed module of the signed root permutation. This is a decomposition of
modules, not of Lie algebras: opposite root brackets can have nonzero Cartan components.

The same decomposition holds after extension to every coefficient ring, without
flatness, freeness, or invertibility of the action order. The canonical comparison from the
scalar extension of integral invariants respects these two parts. Thus a computation of the
Cartan kernel and a computation of the signed root cycles can be combined independently;
neither a central/coroot splitting nor a permutation basis of the full Cartan lattice is needed.

## Main definitions

* `Matrix.FullShellLieAlgebra.fixedCartanRootEquiv`: the integral fixed-module decomposition.
* `Matrix.FullShellLieAlgebra.fixedCartanRootBaseChangeEquiv`: the decomposition after scalar
  extension, with its compatibility equation for the canonical fixed-module comparison.
* `Matrix.FullShellLieAlgebra.fixedSubmoduleBaseChange_surjective_iff`: the canonical
  comparison is surjective exactly when both component comparisons are surjective.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §§7.8–7.9.
* J. C. Jantzen, *Representations of Algebraic Groups*, second edition, Part II, Chapter 1.

The construction uses the pinned full-Cartan action in `FullCartan.CoverLift`, Mathlib's
`TensorProduct.prodRight`, and the canonical `LinearMap.fixedSubmoduleBaseChange`.
-/

public section

open scoped TensorProduct

namespace Matrix.FullShellLieAlgebra

open Module
open ShellLieAlgebra (rootReindex)

variable {I : Type*} [Fintype I] [LinearOrder I] {B : Matrix I I ℤ}
  {Y : Type*} [AddCommGroup Y] (D : ShellCartanDatum B Y)
  (σ : Equiv.Perm I) (hσ : B.reindex σ σ = B) (γ : Y ≃ₗ[ℤ] Y)

/-- The integral invariants split into the fixed full Cartan group and the signed root
invariants. This is only a linear equivalence, not a product decomposition of Lie algebras. -/
noncomputable def fixedCartanRootEquiv :
    (reindex D D σ hσ γ).toLinearMap.fixedSubmodule ≃ₗ[ℤ]
      γ.toLinearMap.fixedSubmodule × (rootReindex σ hσ).toLinearMap.fixedSubmodule :=
  (equivProd D).fixedSubmoduleCongr (by ext x <;> simp) ≪≫ₗ
    LinearEquiv.ofEq _ _ (LinearMap.fixedSubmodule_prodMap _ _) ≪≫ₗ
    Submodule.prodEquiv _ _

/-- The Cartan component of the integral decomposition is its ambient Cartan coordinate. -/
@[simp]
theorem fixedCartanRootEquiv_apply_fst
    (x : (reindex D D σ hσ γ).toLinearMap.fixedSubmodule) :
    (fixedCartanRootEquiv D σ hσ γ x).1.val = (equivProd D x).1 := by
  simp [fixedCartanRootEquiv, Submodule.prodEquiv]

/-- The root component of the integral decomposition is its ambient root coordinate. -/
@[simp]
theorem fixedCartanRootEquiv_apply_snd
    (x : (reindex D D σ hσ γ).toLinearMap.fixedSubmodule) :
    (fixedCartanRootEquiv D σ hσ γ x).2.val = (equivProd D x).2 := by
  simp [fixedCartanRootEquiv, Submodule.prodEquiv]

/-- The inverse integral decomposition reconstructs the given two ambient coordinates. -/
@[simp]
theorem equivProd_fixedCartanRootEquiv_symm
    (x : γ.toLinearMap.fixedSubmodule × (rootReindex σ hσ).toLinearMap.fixedSubmodule) :
    equivProd D ((fixedCartanRootEquiv D σ hσ γ).symm x) = (x.1.val, x.2.val) := by
  apply Prod.ext
  · simpa using (fixedCartanRootEquiv_apply_fst D σ hσ γ
      ((fixedCartanRootEquiv D σ hσ γ).symm x)).symm
  · simpa using (fixedCartanRootEquiv_apply_snd D σ hσ γ
      ((fixedCartanRootEquiv D σ hσ γ).symm x)).symm

variable (A : Type*) [Ring A]

/-- Product coordinates after scalar extension, retaining the full tensor-extended Cartan
module rather than a chosen complement to the coroots. -/
noncomputable def cartanRootBaseChangeEquiv :
    A ⊗[ℤ] FullShellLieAlgebra D ≃ₗ[A]
      (A ⊗[ℤ] Y) × (A ⊗[ℤ] (B.normTwoShell →₀ ℤ)) :=
  (equivProd D).baseChange ℤ A _ _ ≪≫ₗ TensorProduct.prodRight ℤ A A Y (B.normTwoShell →₀ ℤ)

omit [LinearOrder I] in
/-- Scalar-extended product coordinates on a pure tensor. -/
@[simp]
theorem cartanRootBaseChangeEquiv_tmul (a : A) (x : FullShellLieAlgebra D) :
    cartanRootBaseChangeEquiv D A (a ⊗ₜ x) =
      (a ⊗ₜ (equivProd D x).1, a ⊗ₜ (equivProd D x).2) := by
  simp [cartanRootBaseChangeEquiv]

/-- Scalar-extended product coordinates intertwine the action with the product of the two
scalar-extended actions. No exactness assumption on scalar extension is needed. -/
@[simp]
theorem cartanRootBaseChangeEquiv_reindex (x : A ⊗[ℤ] FullShellLieAlgebra D) :
    cartanRootBaseChangeEquiv D A ((reindex D D σ hσ γ).toLinearMap.baseChange A x) =
      ((γ.toLinearMap.baseChange A) (cartanRootBaseChangeEquiv D A x).1,
        ((rootReindex σ hσ).toLinearMap.baseChange A) (cartanRootBaseChangeEquiv D A x).2) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => simp
  | add x y hx hy => simp_all

/-- The invariants after arbitrary scalar extension split into the actual Cartan kernel and
signed root invariants. In particular this does not presume that invariants commute with
scalar extension. -/
noncomputable def fixedCartanRootBaseChangeEquiv :
    ((reindex D D σ hσ γ).toLinearMap.baseChange A).fixedSubmodule ≃ₗ[A]
      (γ.toLinearMap.baseChange A).fixedSubmodule ×
        ((rootReindex σ hσ).toLinearMap.baseChange A).fixedSubmodule :=
  (cartanRootBaseChangeEquiv D A).fixedSubmoduleCongr (by ext x <;> simp) ≪≫ₗ
    LinearEquiv.ofEq _ _ (LinearMap.fixedSubmodule_prodMap _ _) ≪≫ₗ
    Submodule.prodEquiv _ _

/-- The fixed scalar-extended Cartan component is the ambient tensor Cartan coordinate. -/
@[simp]
theorem fixedCartanRootBaseChangeEquiv_apply_fst
    (x : ((reindex D D σ hσ γ).toLinearMap.baseChange A).fixedSubmodule) :
    (fixedCartanRootBaseChangeEquiv D σ hσ γ A x).1.val =
      (cartanRootBaseChangeEquiv D A x).1 := by
  simp [fixedCartanRootBaseChangeEquiv, Submodule.prodEquiv]

/-- The fixed scalar-extended root component is the ambient tensor root coordinate. -/
@[simp]
theorem fixedCartanRootBaseChangeEquiv_apply_snd
    (x : ((reindex D D σ hσ γ).toLinearMap.baseChange A).fixedSubmodule) :
    (fixedCartanRootBaseChangeEquiv D σ hσ γ A x).2.val =
      (cartanRootBaseChangeEquiv D A x).2 := by
  simp [fixedCartanRootBaseChangeEquiv, Submodule.prodEquiv]

/-- The inverse fixed decomposition reconstructs the two tensor coordinates. -/
@[simp]
theorem cartanRootBaseChangeEquiv_fixedCartanRootBaseChangeEquiv_symm
    (x : (γ.toLinearMap.baseChange A).fixedSubmodule ×
      ((rootReindex σ hσ).toLinearMap.baseChange A).fixedSubmodule) :
    cartanRootBaseChangeEquiv D A ((fixedCartanRootBaseChangeEquiv D σ hσ γ A).symm x) =
      (x.1.val, x.2.val) := by
  apply Prod.ext
  · simpa using (fixedCartanRootBaseChangeEquiv_apply_fst D σ hσ γ A
      ((fixedCartanRootBaseChangeEquiv D σ hσ γ A).symm x)).symm
  · simpa using (fixedCartanRootBaseChangeEquiv_apply_snd D σ hσ γ A
      ((fixedCartanRootBaseChangeEquiv D σ hσ γ A).symm x)).symm

/-- The canonical comparison from scalar-extended integral invariants acts separately on the
Cartan and root parts. This identifies the two independent sources of failure of surjectivity. -/
private theorem fixedCartanRootBaseChangeEquiv_fixedSubmoduleBaseChange_tmul (a : A)
    (x : (reindex D D σ hσ γ).toLinearMap.fixedSubmodule) :
    fixedCartanRootBaseChangeEquiv D σ hσ γ A
        ((reindex D D σ hσ γ).toLinearMap.fixedSubmoduleBaseChange A (a ⊗ₜ x)) =
      (γ.toLinearMap.fixedSubmoduleBaseChange A
        (a ⊗ₜ (fixedCartanRootEquiv D σ hσ γ x).1),
       (rootReindex σ hσ).toLinearMap.fixedSubmoduleBaseChange A
        (a ⊗ₜ (fixedCartanRootEquiv D σ hσ γ x).2)) := by
  apply Prod.ext <;> apply Subtype.ext <;> simp

/-- The entire canonical fixed-module comparison is block diagonal in Cartan/root coordinates,
not only on pure tensors. -/
theorem fixedCartanRootBaseChangeEquiv_comp_fixedSubmoduleBaseChange :
    (fixedCartanRootBaseChangeEquiv D σ hσ γ A).toLinearMap ∘ₗ
        (reindex D D σ hσ γ).toLinearMap.fixedSubmoduleBaseChange A =
      (γ.toLinearMap.fixedSubmoduleBaseChange A).prodMap
          ((rootReindex σ hσ).toLinearMap.fixedSubmoduleBaseChange A) ∘ₗ
        (TensorProduct.prodRight ℤ A A γ.toLinearMap.fixedSubmodule
          (rootReindex σ hσ).toLinearMap.fixedSubmodule).toLinearMap ∘ₗ
        ((fixedCartanRootEquiv D σ hσ γ).baseChange ℤ A _ _).toLinearMap := by
  refine TensorProduct.AlgebraTensorModule.ext fun a x ↦ ?_
  simpa using fixedCartanRootBaseChangeEquiv_fixedSubmoduleBaseChange_tmul D σ hσ γ A a x

/-- Scalar extension supplies every fixed full-Cartan vector exactly when it supplies every fixed
Cartan vector and every signed root invariant. Neither condition is implicit in the other. -/
theorem fixedSubmoduleBaseChange_surjective_iff :
    Function.Surjective ((reindex D D σ hσ γ).toLinearMap.fixedSubmoduleBaseChange A) ↔
      Function.Surjective (γ.toLinearMap.fixedSubmoduleBaseChange A) ∧
        Function.Surjective ((rootReindex σ hσ).toLinearMap.fixedSubmoduleBaseChange A) := by
  let e := (fixedCartanRootEquiv D σ hσ γ).baseChange ℤ A _ _ ≪≫ₗ
    TensorProduct.prodRight ℤ A A γ.toLinearMap.fixedSubmodule
      (rootReindex σ hσ).toLinearMap.fixedSubmodule
  have h := congrArg DFunLike.coe
    (fixedCartanRootBaseChangeEquiv_comp_fixedSubmoduleBaseChange D σ hσ γ A)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, LinearMap.coe_prodMap] at h
  rw [← EquivLike.comp_surjective _ (fixedCartanRootBaseChangeEquiv D σ hσ γ A), h]
  exact (EquivLike.surjective_comp e _).trans Prod.map_surjective

end Matrix.FullShellLieAlgebra
