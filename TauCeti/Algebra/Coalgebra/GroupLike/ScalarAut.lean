/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.Coalgebra.TensorProduct
public import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# Scalar automorphisms on group-like elements of base-changed coalgebras

For a commutative semiring extension `L/K` and a `K`-coalgebra `A`, the scalar-factor action on
`L ⊗[K] A` preserves the counit and comultiplication equations defining group-like elements.
It therefore induces an action on the group-like elements without requiring multiplication on
`A`. For bialgebras, compatibility with multiplication is proved in
`TauCeti.Algebra.Bialgebra.GroupLike.ScalarAut`.

## Main declarations

* `TauCeti.ScalarAut.counit_smul`: the counit commutes with the scalar-factor action.
* `TauCeti.ScalarAut.comul_smul`: comultiplication commutes with the semilinear scalar action.
* `TauCeti.ScalarAut.isGroupLikeElem_smul`: scalar automorphisms preserve group-like elements.
* `TauCeti.ScalarAut.instGroupLikeMulAction`: the induced action on group-like elements.
-/

public section

open Coalgebra TensorProduct

namespace TauCeti.ScalarAut

variable {K L A : Type*} [CommSemiring K] [CommSemiring L] [Algebra K L]
variable [AddCommMonoid A] [Module K A]

section CoalgebraStruct

variable [CoalgebraStruct K A]

/-- The counit is equivariant for the semilinear scalar action. -/
theorem counit_smul (σ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    counit (R := L) (σ • x) = σ (counit (R := L) x) := by
  induction x with
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, map_add]
  | tmul a x => simp

/-- Comultiplication is equivariant for the semilinear scalar action. -/
theorem comul_smul (σ : L ≃ₐ[K] L) (x : L ⊗[K] A) :
    comul (σ • x) =
      TensorProduct.map (semilinearMap (A := A) σ)
        (semilinearMap (A := A) σ) (comul x) := by
  induction x with
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, map_add]
  | tmul a x =>
      rw [smul_tmul, TensorProduct.comul_tmul, TensorProduct.comul_tmul]
      induction comul (R := K) x with
      | add x y hx hy => simp only [tmul_add, map_add, hx, hy]
      | tmul x₁ x₂ =>
          rw [CommSemiring.comul_apply L a, CommSemiring.comul_apply L (σ a)]
          simp only [AlgebraTensorModule.tensorTensorTensorComm_tmul, TensorProduct.map_tmul,
            semilinearMap_apply, smul_tmul, map_one]

end CoalgebraStruct

variable [Coalgebra K A]

/-- Applying a scalar automorphism preserves the group-like equations. -/
theorem isGroupLikeElem_smul (σ : L ≃ₐ[K] L) {x : L ⊗[K] A}
    (hx : IsGroupLikeElem L x) : IsGroupLikeElem L (σ • x) where
  counit_eq_one := by rw [counit_smul, hx.counit_eq_one, map_one]
  comul_eq_tmul_self := by
    rw [comul_smul, hx.comul_eq_tmul_self, TensorProduct.map_tmul]
    simp only [semilinearMap_apply]

/-- Scalar automorphisms act on group-like elements through the scalar factor. -/
noncomputable instance instGroupLikeMulAction :
    MulAction (L ≃ₐ[K] L) (_root_.GroupLike L (L ⊗[K] A)) where
  smul σ x := ⟨σ • x.val, isGroupLikeElem_smul σ x.isGroupLikeElem_val⟩
  one_smul x := _root_.GroupLike.val_injective (one_smul _ x.val)
  mul_smul σ τ x := _root_.GroupLike.val_injective (mul_smul σ τ x.val)

/-- The value of the scalar action on a group-like element is the scalar-factor action. -/
@[simp]
theorem val_smul (σ : L ≃ₐ[K] L) (x : _root_.GroupLike L (L ⊗[K] A)) :
    (σ • x).val = σ • x.val :=
  (rfl)

end TauCeti.ScalarAut
