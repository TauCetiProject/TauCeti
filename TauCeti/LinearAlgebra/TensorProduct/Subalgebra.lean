/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearDisjoint
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import TauCeti.Algebra.Algebra.Subalgebra.Pointwise

/-!
# Tensor product multiplication equivalences for commuting subalgebras

Mathlib's `Subalgebra.LinearDisjoint.mulMap` constructs the canonical `R`-algebra isomorphism
`S ⊗[R] T ≃ₐ[R] ↥(S ⊔ T)` induced by multiplication when the ambient algebra `A` is commutative.
In noncommutative algebras—such as operator algebras containing commuting subalgebras `S` and `T`—
the same isomorphism holds whenever every element of `S` commutes with every element of `T` and the
underlying submodules are linearly disjoint (`S.toSubmodule.LinearDisjoint T.toSubmodule`).

## Main declarations

* `Subalgebra.mulAlgEquivOfCommute`: for elementwise-commuting, linearly disjoint subalgebras
  `S T : Subalgebra R A`, multiplication induces an `R`-algebra isomorphism
  `S ⊗[R] T ≃ₐ[R] ↥(S ⊔ T)`.
* `Subalgebra.coe_mulAlgEquivOfCommute_tmul`: `mulAlgEquivOfCommute` sends `a ⊗ₜ b` to `a * b`.
-/

public section

open scoped TensorProduct

namespace Subalgebra

variable {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

/-- If `S` and `T` are linearly disjoint subalgebras of `A` whose elements commute, multiplication
induces a unital `R`-algebra equivalence `S ⊗[R] T ≃ₐ[R] ↥(S ⊔ T)`. This generalizes
`Subalgebra.LinearDisjoint.mulMap` from commutative `A` to elementwise-commuting subalgebras of a
general semiring `A`. -/
noncomputable def mulAlgEquivOfCommute (S T : Subalgebra R A)
    (hcomm : ∀ a ∈ S, ∀ b ∈ T, Commute a b) (H : S.toSubmodule.LinearDisjoint T.toSubmodule) :
    S ⊗[R] T ≃ₐ[R] ↥(S ⊔ T) :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct
    (H.mulMap.trans (LinearEquiv.ofEq _ _ (mul_toSubmodule_of_commute S T hcomm)))
    (fun a₁ a₂ b₁ b₂ => Subtype.ext <|
      (hcomm a₂ a₂.property b₁ b₁.property).mul_mul_mul_comm a₁ b₂)
    (Subtype.ext <| mul_one (1 : A))

/-- `mulAlgEquivOfCommute` sends a pure tensor `a ⊗ₜ b` to the product `a * b`. -/
@[simp]
theorem coe_mulAlgEquivOfCommute_tmul {S T : Subalgebra R A}
    (hcomm : ∀ a ∈ S, ∀ b ∈ T, Commute a b) (H : S.toSubmodule.LinearDisjoint T.toSubmodule)
    (a : S) (b : T) :
    (S.mulAlgEquivOfCommute T hcomm H (a ⊗ₜ[R] b) : A) = (a : A) * b := by
  rw [mulAlgEquivOfCommute, Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct_apply,
    LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply, Submodule.LinearDisjoint.val_mulMap_tmul]

end Subalgebra
