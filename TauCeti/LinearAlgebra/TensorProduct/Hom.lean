/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom

/-!
# Scalar extension of linear-map spaces

For a finite free source module, extending the scalars of the space of linear maps is the same
as taking linear maps between the scalar-extended modules. This file identifies Mathlib's
`LinearMap.baseChangeHom` as that scalar-extension map, so `IsBaseChange.equiv` supplies the
comparison equivalence and `IsBaseChange.equiv_tmul` evaluates it on pure tensors.
-/

public section

namespace LinearMap

/-- Linear maps out of a finite free module commute with scalar extension of both modules. -/
theorem isBaseChange_baseChangeHom (R A M N : Type*) [CommSemiring R] [CommSemiring A]
    [Algebra R A] [AddCommMonoid M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommMonoid N] [Module R N] :
    IsBaseChange A (baseChangeHom R A M N) := by
  convert! (TensorProduct.isBaseChange R M A).linearMapLeftRight
    (TensorProduct.isBaseChange R N A) using 1
  ext f m
  exact (IsBaseChange.linearMapLeftRightHom_comp_apply (TensorProduct.isBaseChange R M A)
    ((TensorProduct.mk R A N) 1) f m).symm

end LinearMap
