/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Augmentation
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.Basic

/-!
# The trivial action of an augmented differential graded algebra

Let `A` be a differential graded algebra over `R` with an augmentation `ε : A → R`. The composite
of `ε` with the unit `R → A` is a morphism of DG algebras `A → A`
(`TauCeti.DGAlgAugmentation.trivialAction`). A right DG module over `A` restricted along it is
acted on by `a` through the scalar `ε(a)`: the **trivial action**
(`TauCeti.DGAlgAugmentation.op_smul_eq`). In particular every element
of the augmentation ideal acts by zero on such a module
(`TauCeti.DGAlgAugmentation.op_smul_eq_zero_of_eq_zero`). For the chains on a loop space these are
the coefficients on which the loops act trivially.

## Main definitions

* `TauCeti.DGAlgAugmentation.trivialAction`: the composite of the augmentation and the unit.

## Main results

* `TauCeti.DGAlgAugmentation.op_smul_eq`: `a` acts through the trivial action by the scalar
  `ε(a)`.
* `TauCeti.DGAlgAugmentation.op_smul_eq_zero_of_eq_zero`: an element of augmentation zero acts by
  zero through the trivial action.
-/

public section

open MulOpposite

namespace TauCeti

namespace DGAlgAugmentation

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  (e : DGAlgAugmentation h)

/-- The **trivial action** of an augmented DG algebra: the composite of the augmentation
`A → R` with the unit `R → A`. A DG right module restricted along it is acted on by `a` through
the scalar `ε(a)`. -/
noncomputable def trivialAction : DGAlgHom h h :=
  h.unitHom.comp e

/-- The trivial action sends an element to the unit times its augmentation. -/
@[simp]
theorem trivialAction_apply (a : A) : e.trivialAction a = algebraMap R A (e a) := by
  rw [trivialAction, DGAlgHom.comp_apply, IsDGAlgebra.unitHom_apply]

/-- **Through the trivial action, `a` acts by the scalar `ε(a)`.** -/
@[simp]
theorem op_smul_eq {M : Type*} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
    [IsScalarTower R Aᵐᵒᵖ M] (a : A) (α : DGRightModule.RestrictScalars e.trivialAction M) :
    op a • α = e a • α := by
  apply DGRightModule.RestrictScalars.ext
  rw [DGRightModule.RestrictScalars.val_op_smul, trivialAction_apply,
    DGRightModule.RestrictScalars.val_smul, ← MulOpposite.algebraMap_apply, algebraMap_smul]

/-- **An element of augmentation zero acts by zero through the trivial action.** This needs no
compatibility of the action with the scalars of `R`, unlike
`TauCeti.DGAlgAugmentation.op_smul_eq`. -/
theorem op_smul_eq_zero_of_eq_zero {M : Type*} [AddCommGroup M] [Module Aᵐᵒᵖ M] {a : A}
    (ha : e a = 0) (α : DGRightModule.RestrictScalars e.trivialAction M) : op a • α = 0 := by
  apply DGRightModule.RestrictScalars.ext
  rw [DGRightModule.RestrictScalars.val_op_smul, trivialAction_apply, ha, map_zero, op_zero,
    zero_smul, DGRightModule.RestrictScalars.val_zero]

end DGAlgAugmentation

end TauCeti
