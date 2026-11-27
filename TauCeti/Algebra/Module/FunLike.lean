/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FunLike
public import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Coercion on `FunLike` types as a linear map

For a `FunLike F α β` carrying `R`-module operations pointwise (`[IsAddApply F]`,
`[IsSMulApply R F]`), coercion `⇑ : F → α → β` is an `R`-linear map (`FunLike.coeLinearMap`).

## Main definitions

* `FunLike.coeLinearMap`: coercion `F →ₗ[R] α → β` as an `R`-linear map.

## Main results

* `FunLike.coeLinearMap_injective`: `FunLike.coeLinearMap` is injective.
-/

public section

namespace FunLike

variable {R F α β : Type*} [FunLike F α β]
  [Semiring R] [AddCommMonoid F] [AddCommMonoid β] [Module R F] [Module R β]
  [IsAddApply F] [IsSMulApply R F]

variable (R F α β) in
/-- Coercion on a `FunLike` module carrying its operations pointwise, as an `R`-linear map. -/
def coeLinearMap : F →ₗ[R] α → β where
  toFun f := ⇑f
  map_add' := coe_add
  map_smul' r f := by rw [RingHom.id_apply, coe_smul]

/-- Applying `coeLinearMap` coerces `f` to a function `α → β`. -/
@[simp]
theorem coeLinearMap_apply (f : F) : coeLinearMap R F α β f = ⇑f :=
  (rfl)

/-- Coercing `coeLinearMap` to a function gives `DFunLike.coe`. -/
@[norm_cast]
theorem coe_coeLinearMap : (coeLinearMap R F α β : F → α → β) = DFunLike.coe :=
  (rfl)

/-- Forgetting scalar multiplication on `coeLinearMap` recovers `FunLike.coeAddMonoidHom`. -/
theorem coeLinearMap_toAddMonoidHom [IsZeroApply F] :
    (coeLinearMap R F α β).toAddMonoidHom = coeAddMonoidHom F α β :=
  (rfl)

/-- `FunLike.coeLinearMap` is injective. -/
theorem coeLinearMap_injective : Function.Injective (coeLinearMap R F α β) := by
  rw [coe_coeLinearMap]
  exact DFunLike.coe_injective

end FunLike
