/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import TauCeti.Algebra.Module.GradedModule.Coarsen

/-!
# The parity involution as an algebra automorphism

On an internally `ZMod 2`-graded algebra, the parity involution fixing the even piece and negating
the odd piece (`TauCeti.InternalGrading.parityTwist`) is an involutive algebra automorphism. This is
the `ZMod 2`-graded counterpart of `TauCeti.InternalGrading.koszulTwistAlgEquiv` at parameter `1`.

## Main definitions

* `TauCeti.InternalGrading.parityTwistAlgEquiv`: the parity algebra automorphism of a
  `ZMod 2`-graded algebra.
-/

public section

namespace TauCeti.InternalGrading

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]
  (𝒜 : ZMod 2 → Submodule R A) [GradedAlgebra 𝒜]

/-- The involutive algebra automorphism of a `ZMod 2`-graded algebra scaling parity `i` by
`(-1) ^ i`. -/
noncomputable def parityTwistAlgEquiv : A ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom
    (AlgHom.ofLinearMap (ofDecomposition 𝒜).parityTwist
      parityTwist_ofDecomposition_one parityTwist_ofDecomposition_mul)
    (AlgHom.ofLinearMap (ofDecomposition 𝒜).parityTwist
      parityTwist_ofDecomposition_one parityTwist_ofDecomposition_mul)
    (by ext a; exact (ofDecomposition 𝒜).parityTwist_parityTwist a)
    (by ext a; exact (ofDecomposition 𝒜).parityTwist_parityTwist a)

/-- The underlying linear map of `parityTwistAlgEquiv` is `parityTwist`. -/
@[simp]
theorem parityTwistAlgEquiv_apply (a : A) :
    parityTwistAlgEquiv 𝒜 a = (ofDecomposition 𝒜).parityTwist a := (rfl)

/-- On an element of parity `i`, `parityTwistAlgEquiv` acts as `(-1) ^ i`. -/
theorem parityTwistAlgEquiv_apply_of_mem {i : ZMod 2} {a : A} (ha : a ∈ 𝒜 i) :
    parityTwistAlgEquiv 𝒜 a = ((-1 : ℤˣ) ^ i) • a :=
  parityTwist_ofDecomposition_apply_of_mem 𝒜 ha

/-- The inverse of `parityTwistAlgEquiv` is `parityTwistAlgEquiv` itself. -/
@[simp]
theorem parityTwistAlgEquiv_symm :
    (parityTwistAlgEquiv 𝒜).symm = parityTwistAlgEquiv 𝒜 := by
  ext a
  rfl

/-- Composing `parityTwistAlgEquiv` with itself gives the identity algebra equivalence. -/
@[simp]
theorem parityTwistAlgEquiv_trans_self :
    (parityTwistAlgEquiv 𝒜).trans (parityTwistAlgEquiv 𝒜) = AlgEquiv.refl := by
  ext a
  simp

end TauCeti.InternalGrading
