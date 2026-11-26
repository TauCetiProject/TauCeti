/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The right-factor module action on a tensor product

An action on the right factor commuting with the ground scalars acts on the tensor product
by tensoring its endomorphisms with the identity on the left.
-/

public section

open scoped TensorProduct

namespace TensorProduct

variable {R A O L : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Semiring O] [Algebra R O] [AddCommMonoid L] [Module R L] [Module O L] [IsScalarTower R O L]

/-- The action of `O` on `A ⊗[R] L` induced by its action on `L`. This is an explicit module
structure since a scalar can also act through the left factor. -/
abbrev rightModule : Module O (A ⊗[R] L) :=
  Module.compHom _ ((Module.End.lTensorAlgHom R L A).comp (Algebra.lsmul R R L)).toRingHom

/-- The right-factor action is the tensor extension of the original scalar endomorphism. -/
theorem rightModule_smul_eq_lTensor (b : O) (x : A ⊗[R] L) :
    letI := rightModule (O := O) (R := R) (A := A) (L := L)
    b • x = (Algebra.lsmul R R L b).lTensor A x :=
  (rfl)

/-- The right-factor action on a pure tensor acts on its right entry. -/
theorem rightModule_smul_tmul (b : O) (a : A) (x : L) :
    letI := rightModule (O := O) (R := R) (A := A) (L := L)
    b • (a ⊗ₜ[R] x) = a ⊗ₜ[R] (b • x) := by
  simp [rightModule_smul_eq_lTensor, Algebra.lsmul_apply]

end TensorProduct
