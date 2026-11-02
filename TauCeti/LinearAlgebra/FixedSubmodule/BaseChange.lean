/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FixedSubmodule
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension of fixed vectors

Extending the inclusion of a fixed submodule gives a canonical map into the fixed
submodule after scalar extension. This construction requires no flatness assumption.
-/

public section

open TensorProduct

namespace LinearMap

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The natural comparison from scalar-extended fixed vectors to fixed vectors of the
scalar-extended endomorphism. -/
def fixedSubmoduleBaseChange (f : M →ₗ[R] M) (A : Type*) [Semiring A] [Algebra R A] :
    A ⊗[R] f.fixedSubmodule →ₗ[A] (f.baseChange A).fixedSubmodule :=
  (f.fixedSubmodule.subtype.baseChange A).codRestrict _ fun x ↦ by
    have h : f ∘ₗ f.fixedSubmodule.subtype = f.fixedSubmodule.subtype := by
      ext v
      exact v.property
    rw [mem_fixedSubmodule_iff]
    have hA := congrArg (LinearMap.baseChange A) h
    rw [baseChange_comp] at hA
    exact LinearMap.congr_fun hA x

/-- The comparison is the scalar extension of the original inclusion on ambient vectors. -/
@[simp]
theorem coe_fixedSubmoduleBaseChange (f : M →ₗ[R] M) (A : Type*) [Semiring A]
    [Algebra R A] (x : A ⊗[R] f.fixedSubmodule) :
    (f.fixedSubmoduleBaseChange A x : A ⊗[R] M) = f.fixedSubmodule.subtype.baseChange A x := by
  rfl

/-- A pure tensor of a fixed vector maps to the same ambient pure tensor. -/
theorem fixedSubmoduleBaseChange_tmul (f : M →ₗ[R] M) (A : Type*) [Semiring A]
    [Algebra R A] (a : A) (v : f.fixedSubmodule) :
    (f.fixedSubmoduleBaseChange A (a ⊗ₜ[R] v) : A ⊗[R] M) = a ⊗ₜ[R] (v : M) := by
  rfl

/-- Composing the comparison with the target inclusion recovers the extended inclusion. -/
@[simp]
theorem subtype_comp_fixedSubmoduleBaseChange (f : M →ₗ[R] M) (A : Type*) [Semiring A]
    [Algebra R A] :
    (f.baseChange A).fixedSubmodule.subtype ∘ₗ f.fixedSubmoduleBaseChange A =
      f.fixedSubmodule.subtype.baseChange A := by
  rfl

end LinearMap
