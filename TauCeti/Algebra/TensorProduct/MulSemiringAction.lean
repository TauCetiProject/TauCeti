/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The factorwise action of a product of monoids on a tensor product

If a monoid `G` acts on an `R`-algebra `A` and a monoid `H` acts on an `R`-algebra `B`, both by
`R`-algebra endomorphisms, then `G × H` acts on `A ⊗[R] B` factorwise, by
`(g, h) • (a ⊗ b) = (g • a) ⊗ (h • b)`. Geometrically, the product `Spec A ×_{Spec R} Spec B`
carries the product of the two actions. This is the action under which the tensor product of a
`G`-torsor and an `H`-torsor is a `(G × H)`-torsor.

## Main definitions

* `Algebra.TensorProduct.prodMulSemiringAction`: the factorwise action of `G × H` on
  `A ⊗[R] B`, by `R`-algebra endomorphisms.

## Implementation notes

The action is not a global instance: when `G × H` also acts on `A`, Mathlib's action through the
left factor would make the action of `G × H` on `A ⊗[R] B` ambiguous. This follows
`Algebra.TensorProduct.rightMulSemiringAction`, the action through the right factor alone.
-/

public section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable {R : Type*} [CommSemiring R] (A B G H : Type*) [Semiring A] [Algebra R A] [Semiring B]
  [Algebra R B] [Monoid G] [Monoid H] [MulSemiringAction G A] [SMulCommClass G R A]
  [MulSemiringAction H B] [SMulCommClass H R B]

/-- Monoids `G` acting on `A` and `H` acting on `B` by `R`-algebra endomorphisms give an action of
`G × H` on `A ⊗[R] B` by `R`-algebra endomorphisms: `(g, h) • (a ⊗ b) = (g • a) ⊗ (h • b)`.

This is not a global instance: when `G × H` also acts on `A`, Mathlib's action through the left
factor would make the action of `G × H` on `A ⊗[R] B` ambiguous. -/
noncomputable abbrev prodMulSemiringAction : MulSemiringAction (G × H) (A ⊗[R] B) where
  smul k := Algebra.TensorProduct.map (MulSemiringAction.toAlgHom R A k.1)
    (MulSemiringAction.toAlgHom R B k.2)
  one_smul := DFunLike.congr_fun (f := Algebra.TensorProduct.map
    (MulSemiringAction.toAlgHom R A (1 : G)) (MulSemiringAction.toAlgHom R B (1 : H)))
    (g := AlgHom.id R _) (Algebra.TensorProduct.ext' fun _ _ ↦ by simp)
  mul_smul k l := DFunLike.congr_fun (f := Algebra.TensorProduct.map
    (MulSemiringAction.toAlgHom R A (k * l).1) (MulSemiringAction.toAlgHom R B (k * l).2))
    (g := (Algebra.TensorProduct.map (MulSemiringAction.toAlgHom R A k.1)
        (MulSemiringAction.toAlgHom R B k.2)).comp
      (Algebra.TensorProduct.map (MulSemiringAction.toAlgHom R A l.1)
        (MulSemiringAction.toAlgHom R B l.2)))
    (Algebra.TensorProduct.ext' fun _ _ ↦ by simp [mul_smul])
  smul_zero _ := map_zero _
  smul_add _ := map_add _
  smul_one _ := map_one _
  smul_mul _ := map_mul _

attribute [local instance] prodMulSemiringAction

variable {A B G H}

/-- The factorwise action of `k : G × H` is the `R`-algebra map `k.1 ⊗ k.2`. -/
theorem prodMulSemiringAction_smul_def (k : G × H) (z : A ⊗[R] B) :
    k • z = Algebra.TensorProduct.map (MulSemiringAction.toAlgHom R A k.1)
      (MulSemiringAction.toAlgHom R B k.2) z :=
  rfl

/-- The factorwise action on a pure tensor. -/
@[simp]
theorem prodMulSemiringAction_smul_tmul (k : G × H) (a : A) (b : B) :
    k • (a ⊗ₜ[R] b) = (k.1 • a) ⊗ₜ (k.2 • b) :=
  rfl

/-- The factorwise action is by `R`-linear maps. -/
instance prodMulSemiringAction_smulCommClass : SMulCommClass (G × H) R (A ⊗[R] B) where
  smul_comm k r z := by
    simp only [prodMulSemiringAction_smul_def, map_smul]

end Algebra.TensorProduct
